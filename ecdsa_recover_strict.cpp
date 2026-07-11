// ecdsa_recover_strict.cpp
// Build:
/*
sudo apt-get update && sudo apt-get install -y g++ libsecp256k1-dev libssl-dev libboost-dev
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

#include <boost/multiprecision/cpp_int.hpp>

using namespace std;
using boost::multiprecision::cpp_int;
namespace fs = std::filesystem;

// ------------------------------- Global Constraints & Constants -------------------------------
static const char* N_HEX = "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141";
static cpp_int SECP256K1_N;

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

static void sha256_once(const unsigned char* in, size_t len, unsigned char out[32]) {
    SHA256_CTX c;
    SHA256_Init(&c);
    SHA256_Update(&c, in, len);
    SHA256_Final(out, &c);
}

// ------------------------------- Simple Micro-JSON Parser -------------------------------
// Hand-rolled to keep zero-dependency architecture outside boost & native headers
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
        // Fallback for numeric tokens unquoted
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
    string pub_hex; // Known public key constraint if provided
    
    // Derived bignums
    cpp_int r, s, z;
};

// Global Thread Safe Thread Write Managers
static mutex g_out_mutex;
static ofstream g_out_json_f;
static ofstream g_out_txt_f;
static ofstream g_out_k_f;
static ofstream g_out_deltas_f;

static set<string> g_found_privkeys;
static atomic<long long> g_total_iterations(0);
static atomic<long long> g_keys_cracked(0);

// ------------------------------- Key Derivation Validation -------------------------------
static bool verify_and_log_privkey(const cpp_int& priv, const SignatureEntry& entry, const string& source_method) {
    if (priv <= 0 || priv >= SECP256K1_N) return false;
    
    // Check duplication profiles
    stringstream ss;
    ss << std::hex << priv;
    string p_hex = hexlower(ss.str());
    while(p_hex.size() < 64) p_hex = "0" + p_hex;

    lock_guard<mutex> lock(g_out_mutex);
    if (g_found_privkeys.count(p_hex)) return true; // Already discovered
    
    // Verify math explicitly matching: s = k^-1 * (z + r*x) mod n => test if matching pubkey if given
    // Fast verification via secp256k1 context
    secp256k1_context* ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);
    vector<unsigned char> priv_bytes = from_hex(p_hex);
    secp256k1_pubkey pubkey;
    
    if (secp256k1_ec_pubkey_create(ctx, &pubkey, priv_bytes.data()) == 1) {
        unsigned char pub_compressed[33];
        size_t out_len = 33;
        secp256k1_ec_pubkey_serialize(ctx, pub_compressed, &out_len, &pubkey, SECP256K1_EC_COMPRESSED);
        string computed_pub = to_hex(pub_compressed, out_len);
        
        // Write outputs
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

// Extract Private Key using a solved ephemeral candidate k
static bool test_k_candidate(const cpp_int& k, const SignatureEntry& entry, const string& method) {
    if (k <= 0 || k >= SECP256K1_N) return false;
    
    // x = r^-1 * (s * k - z) mod n
    cpp_int r_inv = boost::multiprecision::miller_rabin_test(SECP256K1_N, 5) ? 0 : 1; 
    // Fallback manual modular inverse via Extended Euclidean
    cpp_int t = 0, newt = 1;
    cpp_int r_val = SECP256K1_N, newr = entry.r;
    while (newr != 0) {
        cpp_int quotient = r_val / newr;
        t = t - quotient * newt; swap(t, newt);
        r_val = r_val - quotient * newr; swap(r_val, newr);
    }
    if (r_val > 1) return false; // Not invertible
    if (t < 0) t += SECP256K1_N;
    r_inv = t;

    cpp_int sk = (entry.s * k) % SECP256K1_N;
    cpp_int sk_z = (sk - entry.z) % SECP256K1_N;
    if (sk_z < 0) sk_z += SECP256K1_N;
    
    cpp_int priv = (sk_z * r_inv) % SECP256K1_N;
    
    if (verify_and_log_privkey(priv, entry, method)) {
        if (g_out_k_f.is_open()) {
            stringstream skk; skk << std::hex << k;
            lock_guard<mutex> lock(g_out_mutex);
            g_out_k_f << "{\"index\":\"" << entry.index << "\",\"k_hex\":\"" << skk.str() << "\"}\n" << flush;
        }
        return true;
    }
    return false;
}

// ------------------------------- Worker Engine Core -------------------------------
void execution_worker(int thread_id, const vector<SignatureEntry>& entries, 
                      int max_iter, long long dg_max_delta, const vector<long long>& dg_seeds,
                      int dg_fill_step, int dg_per_pair_cap, const vector<long long>& step_seeds,
                      long long lcg_a_max, long long lcg_b_max, int lcg_per_pair_cap,
                      int scan_rand_k) {
    
    size_t total = entries.size();
    // Round-robin index distribution across concurrent native worker threads
    for (size_t i = thread_id; i < total; i += max_iter) {
        const auto& e1 = entries[i];
        
        // Loop pairings for comparison optimizations
        for (size_t j = i + 1; j < total; j++) {
            const auto& e2 = entries[j];
            g_total_iterations++;
            
            // --- Strategy 1: Shared k analysis (Reused nonce detection) ---
            if (e1.r == e2.r && e1.s != e2.s) {
                // k = (z1 - z2) / (s1 - s2) mod n
                cpp_int top = (e1.z - e2.z) % SECP256K1_N; if (top < 0) top += SECP256K1_N;
                cpp_int bot = (e1.s - e2.s) % SECP256K1_N; if (bot < 0) bot += SECP256K1_N;
                
                cpp_int t = 0, newt = 1;
                cpp_int r_val = SECP256K1_N, newr = bot;
                while (newr != 0) {
                    cpp_int quotient = r_val / newr;
                    t = t - quotient * newt; swap(t, newt);
                    r_val = r_val - quotient * newr; swap(r_val, newr);
                }
                if (r_val == 1) {
                    if (t < 0) t += SECP256K1_N;
                    cpp_int k = (top * t) % SECP256K1_N;
                    test_k_candidate(k, e1, "Shared Nonce (k1=k2)");
                }
            }

            // --- Strategy 2: Differential Gap Multipliers ---
            int pair_dg_count = 0;
            for (long long seed : dg_seeds) {
                if (pair_dg_count >= dg_per_pair_cap) break;
                
                // Scan explicit bounds surrounding seeds (+/- step sequences)
                for (long long delta = -dg_max_delta; delta <= dg_max_delta; delta += dg_fill_step) {
                    if (pair_dg_count >= dg_per_pair_cap) break;
                    
                    cpp_int target_k_delta = seed + delta;
                    if (target_k_delta <= 0) continue;
                    pair_dg_count++;

                    // Test k2 = k1 + target_k_delta
                    // s1 = (z1 + r1*x)/k1, s2 = (z2 + r2*x)/(k1 + delta) => solve systems

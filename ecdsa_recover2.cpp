// ecdsa_recover_strict.cpp
// Build:
// /* sudo apt-get install "-y" g++ libsecp256k1-dev libssl-dev g++ "-O3" "-march=native" "-flto" "-fexceptions" "-pthread" "-std=c++17" \
//    ecdsa_recover_strict.cpp "-o" ecdsa_recover_strict \
//    "-lsecp256k1" "-lcrypto" "-lpthread" "-Wno-deprecated-declarations" */
// /* Example:
//    ./ecdsa_recover_strict \
//      --sigs signatures.jsonl \
//      --threads 12 \
//      --out-json recovered_keys.jsonl \
//      --out-txt recovered_keys.txt \
//      --out-k recovered_k.jsonl \
//      --out-deltas delta_insights.jsonl \
//      --max-iter 4 \
//      --preload-priv known_keys.txt \
//      --dg-max-delta 65536 \
//      --dg-seeds 1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192,16384,32768,65536 \
//      --dg-fill-step 8 \
//      --dg-per-pair-cap 4096 \
//      --step-seeds 3,5,7,9,11,13,17,19,29,37 \
//      --lcg-a-max 4 --lcg-b-max 4096 --lcg-per-pair-cap 2048 \
//      --scan-random-k 0 \
//      --rand-seed 1337 */

#include <bits/stdc++.h>
#include <secp256k1.h>
#include <openssl/sha.h>
#include <openssl/bn.h>
#include <openssl/rand.h>
#include <openssl/crypto.h>

using namespace std;

#include <boost/multiprecision/cpp_int.hpp>
using boost::multiprecision::cpp_int;

#include <filesystem>
namespace fs = std::filesystem;

// ------------------------------- Constants / Helpers -------------------------------
static const char* N_HEX = "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141";

static inline string hexlower(const string& s){
    string t=s;
    for(char& c:t) c=tolower((unsigned char)c);
    return t;
}

static inline bool is_hexlike(const string& s){
    if(s.empty()) return false;
    for(char c: s) if(!isxdigit((unsigned char)c)) return false;
    return true;
}

static string to_hex(const unsigned char* p, size_t n){
    static const char* he="0123456789abcdef";
    string s;
    s.resize(n*2);
    for(size_t i=0;i<n;i++){
        s[2*i]=he[p[i]>>4];
        s[2*i+1]=he[p[i]&0xF];
    }
    return s;
}

static void sha256_once(const unsigned char* in, size_t len, unsigned char out[32]){
    SHA256_CTX c;
    SHA256_Init(&c);
    SHA256_Update(&c, in, len);
    SHA256_Final(out, &c);
}

static string b58encode(const vector<uint8_t>& in){
    static const char* ALPH="123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    int zeros=0;
    while(zeros<(int)in.size() && in[zeros]==0) zeros++;
    vector<uint8_t> b(in.begin(), in.end());
    vector<char> out;
    int start=zeros;
    while(start<(int)b.size()){
        int carry=0;
        for(int i=start;i<(int)b.size();i++){
            int x = (int)b[i] + carry*256;
            b[i]=x/58;
            carry = x%58;
        }
        out.push_back(ALPH[carry]);
        while(start<(int)b.size() && b[start]==0) start++;
    }
    string s(zeros,'1');
    for(auto it=out.rbegin(); it!=out.rend(); ++it) s.push_back(*it);
    return s;
}

static string priv_to_wif(const string& priv_hex, bool compressed=true, bool mainnet=true){
    vector<uint8_t> payload;
    payload.push_back(mainnet?0x80:0xEF);
    vector<uint8_t> sk(32,0);
    for(int i=0;i<32;i++){
        string byte = priv_hex.substr(i*2,2);
        sk[i]=(uint8_t)strtoul(byte.c_str(), nullptr, 16);
    }
    payload.insert(payload.end(), sk.begin(), sk.end());
    if(compressed) payload.push_back(0x01);
    unsigned char h1[32], h2[32];
    sha256_once(payload.data(), payload.size(), h1);
    sha256_once(h1, 32, h2);
    payload.insert(payload.end(), h2, h2+4);
    return b58encode(payload);
}

// ------------------------------- JSONL mini-parser -------------------------------
static bool jsonl_get(const string& line, const string& key, string& out){
    size_t k = line.find("\""+key+"\"");
    if(k==string::npos) return false;
    size_t c = line.find(':', k);
    if(c==string::npos) return false;
    size_t i=c+1;
    while(i<line.size() && isspace((unsigned char)line[i])) i++;
    if(i>=line.size()) return false;
    if(line[i]=='"'){
        size_t j=line.find('"', i+1);
        if(j==string::npos) return false;
        out = line.substr(i+1, j-(i+1));
        return true;
    }else{
        size_t j=i;
        while(j<line.size() && line[j]!=',' && line[j]!='}') j++;
        out = line.substr(i, j-i);
        while(!out.empty() && isspace((unsigned char)out.back())) out.pop_back();
        while(!out.empty() && isspace((unsigned char)out.front())) out.erase(out.begin());
        return !out.empty();
    }
}

// ------------------------------- OpenSSL BN helpers -------------------------------
struct BNWrap {
    BIGNUM* n=nullptr;
    BNWrap(){ n=BN_new(); }
    ~BNWrap(){ if(n) BN_free(n); }
    BNWrap(const BNWrap&)=delete;
    BNWrap& operator=(const BNWrap&)=delete;
    BNWrap(BNWrap&& other) noexcept : n(other.n) { other.n = nullptr; }
    BNWrap& operator=(BNWrap&& other) noexcept {
        if (this != &other) {
            if (n) BN_free(n);
            n = other.n;
            other.n = nullptr;
        }
        return *this;
    }
};

struct Ctx {
    BN_CTX* ctx=nullptr;
    BIGNUM* N=nullptr;
    BIGNUM* halfN=nullptr;
    Ctx() {
        ctx=BN_CTX_new();
        N=BN_new();
        halfN=BN_new();
        BN_hex2bn(&N, N_HEX);
        BN_copy(halfN, N);
        BN_rshift1(halfN, halfN); 
    }
    ~Ctx(){
        if(halfN) BN_free(halfN);
        if(N) BN_free(N);
        if(ctx) BN_CTX_free(ctx);
    }
};

static bool bn_from_hex(const string& hx, BIGNUM* out){
    string t = hx;
    if (t.size()>=2 && t[0]=='0' && (t[1]=='x'||t[1]=='X')) t = t.substr(2);
    if (t.empty()) return false;
    BIGNUM* tmp = nullptr;
    if (BN_hex2bn(&tmp, t.c_str()) <= 0) return false;
    BN_copy(out, tmp);
    BN_free(tmp);
    return true;
}

static string bn_to_hex32(const BIGNUM* bn){
    unsigned char buf[32];
    memset(buf, 0, 32);
    int len = BN_num_bytes(bn);
    if (len > 32) return ""; 
    BN_bn2bin(bn, buf + (32 - len));
    return to_hex(buf, 32);
}

// ------------------------------- Data Models -------------------------------
struct SignatureEntry {
    int index = -1;
    string msg_hex;
    string r_hex;
    string s_hex;
    string pub_hex;
    
    // Parsed forms
    BNWrap bn_z;
    BNWrap bn_r;
    BNWrap bn_s;
    
    bool valid = false;
};

struct PreloadKey {
    string d_hex;
    BNWrap bn_d;
};

// ------------------------------- Context Structures -------------------------------
struct GlobalArgs {
    string sigs_file;
    int threads = 4;
    string out_json;
    string out_txt;
    string out_k;
    string out_deltas;
    int max_iter = 1;
    string preload_priv;
    
    // Delta G settings
    int dg_max_delta = 0;
    vector<long long> dg_seeds;
    int dg_fill_step = 0;
    int dg_per_pair_cap = 0;
    
    // Step settings
    vector<long long> step_seeds;
    
    // LCG settings
    long long lcg_a_max = 0;
    long long lcg_b_max = 0;
    int lcg_per_pair_cap = 0;
    
    // Random scan settings
    long long scan_random_k = 0;
    unsigned int rand_seed = 1337;
};

// Thread-safe standard out logger
static mutex g_log_mutex;
static void log_info(const string& msg) {
    lock_guard<mutex> lock(g_log_mutex);
    cout << "[INFO] " << msg << endl;
}

static void log_error(const string& msg) {
    lock_guard<mutex> lock(g_log_mutex);
    cerr << "[ERROR] " << msg << endl;
}

// Global thread coordination 
static mutex g_out_mutex;
static set<string> g_found_keys;

static void report_found_key(const string& d_hex, int idx1, int idx2, const string& method,
                             const string& out_json_path, const string& out_txt_path,
                             const string& k_hex = "", const string& out_k_path = "") {
    lock_guard<mutex> lock(g_out_mutex);
    string clean_d = hexlower(d_hex);
    if (g_found_keys.count(clean_d)) return;
    g_found_keys.insert(clean_d);
    
    string wif = priv_to_wif(clean_d);
    log_info("!!! KEY RECOVERED (" + method + ") !!! Private key: " + clean_d + " | WIF: " + wif);
    
    if (!out_json_path.empty()) {
        ofstream out(out_json_path, ios::app);
        if (out.is_open()) {
            out << "{\"private_key\":\"" << clean_d << "\",\"wif\":\"" << wif 
                << "\",\"method\":\"" << method << "\",\"idx1\":" << idx1 << ",\"idx2\":" << idx2 << "}\n";
        }
    }
    if (!out_txt_path.empty()) {
        ofstream out(out_txt_path, ios::app);
        if (out.is_open()) {
            out << clean_d << " # " << method << " (idx1=" << idx1 << ", idx2=" << idx2 << ")\n";
        }
    }
    if (!k_hex.empty() && !out_k_path.empty()) {
        ofstream out(out_k_path, ios::app);
        if (out.is_open()) {
            out << "{\"private_key\":\"" << clean_d << "\",\"k_hex\":\"" << hexlower(k_hex) 
                << "\",\"idx\":" << (idx1 >= 0 ? idx1 : idx2) << "}\n";
        }
    }
}

static void write_delta_insight(const string& out_deltas_path, int idx1, int idx2, 
                                 const string& delta_z, const string& delta_s, const string& type) {
    if (out_deltas_path.empty()) return;
    lock_guard<mutex> lock(g_out_mutex);
    ofstream out(out_deltas_path, ios::app);
    if (out.is_open()) {
        out << "{\"idx1\":" << idx1 << ",\"idx2\":" << idx2 
            << ",\"delta_z\":\"" << hexlower(delta_z) << "\",\"delta_s\":\"" << hexlower(delta_s) 
            << "\",\"type\":\"" << type << "\"}\n";
    }
}

// Validation function using secp256k1 context
static bool validate_privkey(secp256k1_context* ctx, const string& d_hex, const string& expected_pub) {
    if (d_hex.size() != 64) return false;
    unsigned char priv[32];
    for(int i=0;i<32;i++){
        priv[i] = (unsigned char)strtoul(d_hex.substr(i*2, 2).c_str(), nullptr, 16);
    }
    if (!secp256k1_ec_seckey_verify(ctx, priv)) return false;
    
    secp256k1_pubkey pubkey;
    if (!secp256k1_ec_pubkey_create(ctx, &pubkey, priv)) return false;
    
    unsigned char pub_serialized[65];
    size_t pub_len = 65;

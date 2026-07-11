#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>
#include <cctype>
#include <cstdlib>
#include <secp256k1.h>
#include <openssl/sha.h>
#include <openssl/bn.h>
#include <openssl/rand.h>
#include <openssl/crypto.h>
#include <filesystem>

using namespace std;
namespace fs = std::filesystem;

static const char* N_HEX = "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141";

static inline string hexlower(const string& s){
    string t = s;
    for(char& c : t) c = tolower((unsigned char)c);
    return t;
}

static inline bool is_hexlike(const string& s){
    if(s.empty()) return false;
    for(char c : s) if(!isxdigit((unsigned char)c)) return false;
    return true;
}

static string to_hex(const unsigned char* p, size_t n){
    static const char* he = "0123456789abcdef";
    string s;
    s.resize(n * 2);
    for(size_t i = 0; i < n; i++){
        s[2 * i] = he[p[i] >> 4];
        s[2 * i + 1] = he[p[i] & 0xF];
    }
    return s;
}

static void sha256_once(const unsigned char* in, size_t len, unsigned char* out){
    SHA256_CTX c;
    SHA256_Init(&c);
    SHA256_Update(&c, in, len);
    SHA256_Final(out, &c);
}

static string b58encode(const vector<uint8_t>& in){
    static const char* ALPH = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
    int zeros = 0;
    while(zeros < (int)in.size() && in[zeros] == 0) zeros++;
    vector<uint8_t> b(in.begin(), in.end());
    vector<char> out;
    int start = zeros;
    while(start < (int)b.size()){
        int carry = 0;
        for(int i = start; i < (int)b.size(); i++){
            int x = (int)b[i] + carry * 256;
            b[i] = x / 58;
            carry = x % 58;
        }
        out.push_back(ALPH[carry]);
        while(start < (int)b.size() && b[start] == 0) start++;
    }
    string s(zeros, '1');
    for(auto it = out.rbegin(); it != out.rend(); ++it) s.push_back(*it);
    return s;
}

static string priv_to_wif(const string& priv_hex, bool compressed = true, bool mainnet = true){
    vector<uint8_t> payload;
    payload.push_back(mainnet ? 0x80 : 0xEF);
    vector<uint8_t> sk(32, 0);
    for(int i = 0; i < 32; i++){
        string byte = priv_hex.substr(i * 2, 2);
        sk[i] = (uint8_t)strtoul(byte.c_str(), nullptr, 16);
    }
    payload.insert(payload.end(), sk.begin(), sk.end());
    if(compressed) payload.push_back(0x01);
    unsigned char h1[32], h2[32];
    sha256_once(payload.data(), payload.size(), h1);
    sha256_once(h1, 32, h2);
    payload.insert(payload.end(), h2, h2 + 4);
    return b58encode(payload);
}

static bool jsonl_get(const string& line, const string& key, string& out){
    size_t k = line.find("\"" + key + "\"");
    if(k == string::npos) return false;
    size_t c = line.find(':', k);
    if(c == string::npos) return false;
    size_t i = c + 1;
    while(i < line.size() && isspace((unsigned char)line[i])) i++;
    if(i >= line.size()) return false;
    if(line[i] == '"'){
        size_t j = line.find('"', i + 1);
        if(j == string::npos) return false;
        out = line.substr(i + 1, j - (i + 1));
        return true;
    } else {
        size_t j = i;
        while(j < line.size() && line[j] != ',' && line[j] != '}') j++;
        out = line.substr(i, j - i);
        while(!out.empty() && isspace((unsigned char)out.back())) out.pop_back();
        while(!out.empty() && isspace((unsigned char)out.front())) out.erase(out.begin());
        return !out.empty();
    }
}

struct BNWrap {
    BIGNUM* n = nullptr;
    BNWrap() { n = BN_new(); }
    ~BNWrap() { if(n) BN_free(n); }
    BNWrap(const BNWrap&) = delete;
    BNWrap& operator=(const BNWrap&) = delete;
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
    BN_CTX* ctx = nullptr;
    BIGNUM* N = nullptr;
    BIGNUM* halfN = nullptr;
    Ctx() {
        ctx = BN_CTX_new();
        N = BN_new();
        halfN = BN_new();
        BN_hex2bn(&N, N_HEX);
        BN_copy(halfN, N);
        BN_rshift1(halfN, halfN);
    }
    ~Ctx() {
        if(halfN) BN_free(halfN);
        if(N) BN_free(N);
        if(ctx) BN_CTX_free(ctx);
    }
};

static bool bn_from_hex(const string& hx, BIGNUM* out){
    string t = hx;
    if (t.size() >= 2 && t[0] == '0' && (t[1] == 'x' || t[1] == 'X')) t = t.substr(2);
    if (t.empty()) return false;
    BIGNUM* tmp = nullptr;
    if (BN_hex2bn(&tmp, t.c_str()) <= 0) return false;
    BN_copy(out, tmp);
    BN_free(tmp);
    return true;
}

struct SignatureData {
    string r, s, msg;
    string pubkey;
};

struct Config {
    string sigs_file;
    string out_json;
    string out_txt;
    string out_k;
    string out_deltas;
    string preload_priv;
    int max_iter = 4;
    int dg_max_delta = 65536;
    vector<int> dg_seeds;
    int dg_fill_step = 8;
    int dg_per_pair_cap = 4096;
    vector<int> step_seeds;
    int lcg_a_max = 4;
    int lcg_b_max = 4096;
    int lcg_per_pair_cap = 2048;
    int scan_random_k = 0;
    unsigned int rand_seed = 1337;
};

static vector<int> parse_comma_seeds(const string& s) {
    vector<int> res;
    stringstream ss(s);
    string item;
    while (getline(ss, item, ',')) {
        if (!item.empty()) res.push_back(stoi(item));
    }
    return res;
}

static void process_signatures(const Config& cfg) {
    ifstream infile(cfg.sigs_file);
    if (!infile.is_open()) {
        cerr << "Error: Cannot open signatures file: " << cfg.sigs_file << "\n";
        return;
    }

    ofstream f_json(cfg.out_json);
    ofstream f_txt(cfg.out_txt);
    ofstream f_k(cfg.out_k);
    ofstream f_deltas(cfg.out_deltas);

    Ctx context;
    secp256k1_context* secp_ctx = secp256k1_context_create(SECP256K1_CONTEXT_VERIFY | SECP256K1_CONTEXT_SIGN);

    string line;
    vector<SignatureData> sigs;
    while (getline(infile, line)) {
        SignatureData sd;
        if (jsonl_get(line, "r", sd.r) && jsonl_get(line, "s", sd.s) && jsonl_get(line, "msg", sd.msg)) {
            jsonl_get(line, "pubkey", sd.pubkey);
            sigs.push_back(sd);
        }
    }
    infile.close();

    cout << "Loaded " << sigs.size() << " signatures. Processing sequentially...\n";

    for (size_t idx = 0; idx < sigs.size(); ++idx) {
        const auto& sd = sigs[idx];
        BNWrap r_bn, s_bn, msg_bn;
        if (!bn_from_hex(sd.r, r_bn.n) || !bn_from_hex(sd.s, s_bn.n) || !bn_from_hex(sd.msg, msg_bn.n)) {
            continue; 
        }
    }
    secp256k1_context_destroy(secp_ctx);
}

int main(int argc, char* argv[]) {
    Config cfg;
    for (int i = 1; i < argc; ++i) {
        string arg = argv[i];
        if (arg == "--sigs" && i + 1 < argc) cfg.sigs_file = argv[++i];
        else if (arg == "--out-json" && i + 1 < argc) cfg.out_json = argv[++i];
        else if (arg == "--out-txt" && i + 1 < argc) cfg.out_txt = argv[++i];
        else if (arg == "--out-k" && i + 1 < argc) cfg.out_k = argv[++i];
        else if (arg == "--out-deltas" && i + 1 < argc) cfg.out_deltas = argv[++i];
        else if (arg == "--preload-priv" && i + 1 < argc) cfg.preload_priv = argv[++i];
        else if (arg == "--max-iter" && i + 1 < argc) cfg.max_iter = stoi(argv[++i]);
        else if (arg == "--dg-max-delta" && i + 1 < argc) cfg.dg_max_delta = stoi(argv[++i]);
        else if (arg == "--dg-seeds" && i + 1 < argc) cfg.dg_seeds = parse_comma_seeds(argv[++i]);
        else if (arg == "--dg-fill-step" && i + 1 < argc) cfg.dg_fill_step = stoi(argv[++i]);
        else if (arg == "--dg-per-pair-cap" && i + 1 < argc) cfg.dg_per_pair_cap = stoi(argv[++i]);
        else if (arg == "--step-seeds" && i + 1 < argc) cfg.step_seeds = parse_comma_seeds(argv[++i]);
        else if (arg == "--lcg-a-max" && i + 1 < argc) cfg.lcg_a_max = stoi(argv[++i]);
        else if (arg == "--lcg-b-max" && i + 1 < argc) cfg.lcg_b_max = stoi(argv[++i]);
        else if (arg == "--lcg-per-pair-cap" && i + 1 < argc) cfg.lcg_per_pair_cap = stoi(argv[++i]);
        else if (arg == "--scan-random-k" && i + 1 < argc) cfg.scan_random_k = stoi(argv[++i]);
        else if (arg == "--rand-seed" && i + 1 < argc) cfg.rand_seed = stoul(argv[++i]);
    }

    if (cfg.sigs_file.empty()) {
        cerr << "Usage error: Specify target signature file using --sigs <file.jsonl>\n";
        return 1;
    }

    process_signatures(cfg);
    return 0;
}

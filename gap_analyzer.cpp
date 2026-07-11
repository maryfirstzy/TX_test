#include <iostream>
#include <vector>
#include <string>
#include <cctype>
#include <memory>
#include <stdexcept>
#include <sstream>

// ==========================================
// 1. THE LEXER (TOKENIZER)
// ==========================================
enum class TokenType {
    NUMBER, IDENTIFIER, ASSIGN, PLUS, MINUS, MULTIPLY, DIVIDE, END_OF_FILE
};

struct Token {
    TokenType type;
    std::string value;
};

class Lexer {
public:
    explicit Lexer(std::string src) : source(std::move(src)), index(0) {}

    std::vector<Token> tokenize() {
        std::vector<Token> tokens;
        while (index < source.length()) {
            char current = source[index];

            if (std::isspace(current)) {
                index++;
                continue;
            }
            if (std::isdigit(current)) {
                tokens.push_back({TokenType::NUMBER, readNumber()});
                continue;
            }
            if (std::isalpha(current)) {
                tokens.push_back({TokenType::IDENTIFIER, readIdentifier()});
                continue;
            }
            if (current == '=') { tokens.push_back({TokenType::ASSIGN, "="}); index++; continue; }
            if (current == '+') { tokens.push_back({TokenType::PLUS, "+"}); index++; continue; }
            if (current == '-') { tokens.push_back({TokenType::MINUS, "-"}); index++; continue; }
            if (current == '*') { tokens.push_back({TokenType::MULTIPLY, "*"}); index++; continue; }
            if (current == '/') { tokens.push_back({TokenType::DIVIDE, "/"}); index++; continue; }

            throw std::runtime_error(std::string("Unknown character: ") + current);
        }
        tokens.push_back({TokenType::END_OF_FILE, ""});
        return tokens;
    }

private:
    std::string source;
    size_t index;

    std::string readNumber() {
        std::string result;
        while (index < source.length() && std::isdigit(source[index])) {
            result += source[index++];
        }
        return result;
    }

    std::string readIdentifier() {
        std::string result;
        while (index < source.length() && std::isalnum(source[index])) {
            result += source[index++];
        }
        return result;
    }
};

// ==========================================
// 2. THE PARSER & AST
// ==========================================
enum class ASTNodeType { NUMBER_LITERAL, VARIABLE, BINARY_OP, ASSIGNMENT };

struct ASTNode {
    ASTNodeType type;
    std::string value;
    std::shared_ptr<ASTNode> left;
    std::shared_ptr<ASTNode> right;
};

class Parser {
public:
    explicit Parser(std::vector<Token> tks) : tokens(std::move(tks)), index(0) {}

    std::shared_ptr<ASTNode> parse() {
        return parseAssignment();
    }

private:
    std::vector<Token> tokens;
    size_t index;

    Token peek() { return tokens[index]; }
    Token consume(TokenType expected) {
        Token t = peek();
        if (t.type != expected) {
            throw std::runtime_error("Unexpected token format during syntax parsing!");
        }
        index++;
        return t;
    }

    std::shared_ptr<ASTNode> parseAssignment() {
        if (peek().type == TokenType::IDENTIFIER) {
            Token varToken = peek();
            if (tokens[index + 1].type == TokenType::ASSIGN) {
                consume(TokenType::IDENTIFIER);
                consume(TokenType::ASSIGN);
                auto exprNode = parseExpression();
                
                auto node = std::make_shared<ASTNode>();
                node->type = ASTNodeType::ASSIGNMENT;
                node->value = varToken.value;
                node->left = exprNode;
                return node;
            }
        }
        return parseExpression();
    }

    std::shared_ptr<ASTNode> parseExpression() {
        auto node = parseTerm();
        while (peek().type == TokenType::PLUS || peek().type == TokenType::MINUS) {
            Token op = peek();
            index++;
            auto rightNode = parseTerm();
            
            auto binaryNode = std::make_shared<ASTNode>();
            binaryNode->type = ASTNodeType::BINARY_OP;
            binaryNode->value = op.value;
            binaryNode->left = node;
            binaryNode->right = rightNode;
            node = binaryNode;
        }
        return node;
    }

    std::shared_ptr<ASTNode> parseTerm() {
        auto node = parseFactor();
        while (peek().type == TokenType::MULTIPLY || peek().type == TokenType::DIVIDE) {
            Token op = peek();
            index++;
            auto rightNode = parseFactor();
            
            auto binaryNode = std::make_shared<ASTNode>();
            binaryNode->type = ASTNodeType::BINARY_OP;
            binaryNode->value = op.value;
            binaryNode->left = node;
            binaryNode->right = rightNode;
            node = binaryNode;
        }
        return node;
    }

    std::shared_ptr<ASTNode> parseFactor() {
        Token t = peek();
        if (t.type == TokenType::NUMBER) {
            consume(TokenType::NUMBER);
            auto node = std::make_shared<ASTNode>();
            node->type = ASTNodeType::NUMBER_LITERAL;
            node->value = t.value;
            return node;
        }
        if (t.type == TokenType::IDENTIFIER) {
            consume(TokenType::IDENTIFIER);
            auto node = std::make_shared<ASTNode>();
            node->type = ASTNodeType::VARIABLE;
            node->value = t.value;
            return node;
        }
        throw std::runtime_error("Expected a dynamic value or variable reference.");
    }
};

// ==========================================
// 3. THE CODE GENERATOR
// ==========================================
class CodeGenerator {
public:
    std::string generate(const std::shared_ptr<ASTNode>& node) {
        std::stringstream code;
        generateCode(node, code);
        return code.str();
    }

private:
    void generateCode(const std::shared_ptr<ASTNode>& node, std::stringstream& code) {
        if (!node) return;

        switch (node->type) {
            case ASTNodeType::NUMBER_LITERAL:
                code << "PUSH " << node->value << "\n";
                break;
            case ASTNodeType::VARIABLE:
                code << "LOAD " << node->value << "\n";
                break;
            case ASTNodeType::ASSIGNMENT:
                generateCode(node->left, code);
                code << "STORE " << node->value << "\n";
                break;
            case ASTNodeType::BINARY_OP:
                // Post-fix notation generator (evaluates children first)
                generateCode(node->left, code);
                generateCode(node->right, code);
                if (node->value == "+") code << "ADD\n";
                else if (node->value == "-") code << "SUB\n";
                else if (node->value == "*") code << "MUL\n";
                else if (node->value == "/") code << "DIV\n";
                break;
        }
    }
};

// ==========================================
// 4. MAIN PROGRAM PIPELINE
// ==========================================
int main() {
    // Example high-level statement input 
    std::string inputSource = "score = 10 + 5 * 2";
    
    std::cout << "Compiling source expression: \"" << inputSource << "\"\n\n";

    try {
        // Run Phase 1: Lexical Analysis
        Lexer lexer(inputSource);
        std::vector<Token> tokens = lexer.tokenize();

        // Run Phase 2: Syntactic Analysis (Parsing)
        Parser parser(tokens);
        std::shared_ptr<ASTNode> astRoot = parser.parse();

        // Run Phase 3: Code Generation
        CodeGenerator codegen;
        std::string targetAssembly = codegen.generate(astRoot);

        std::cout << "--- EMITTED VIRTUAL MACHINE ASSEMBLY ---\n";
        std::cout << targetAssembly;
        std::cout << "----------------------------------------\n";

    } catch (const std::exception& err) {
        std::cerr << "Compilation Error Encountered: " << err.what() << "\n";
        return 1;
    }

    return 0;
}


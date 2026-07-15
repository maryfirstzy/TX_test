#include <iostream>
#include <string>
#include <boost/multiprecision/cpp_int.hpp>

using namespace boost::multiprecision;

// Function to calculate the factorial of a large number
cpp_int calculate_factorial(int n) {
    cpp_int result = 1;
    for (int i = 1; i <= n; ++i) {
        result *= i;
    }
    return result;
}

int main() {
    // 1. Initializing massive numbers using string literals
    cpp_int large_num1("1234567890123456789012345678901234567890");
    cpp_int large_num2("9876543210987654321098765432109876543210");

    // 2. Performing basic arithmetic operations
    cpp_int sum = large_num1 + large_num2;
    cpp_int product = large_num1 * large_num2;

    std::cout << "Sum: " << sum << "\n\n";
    std::cout << "Product: " << product << "\n\n";

    // 3. Calculating a massive factorial (100!)
    int target = 100;
    cpp_int factorial = calculate_factorial(target);
    std::cout << target << "! = " << factorial << "\n";

    return 0;
}

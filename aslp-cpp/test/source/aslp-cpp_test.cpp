#include <iostream>
#include <memory>
#include <random>
#include <string>
#include <chrono>

#include "aslp-cpp/aslp-cpp.hpp"

class opgen
{
  std::unique_ptr<std::mt19937> rng;
  std::unique_ptr<std::uniform_int_distribution<std::mt19937::result_type>>
      dist;

public:
  opgen()
  {
    rng = std::make_unique<std::mt19937>(1234);
    dist = std::make_unique<
        std::uniform_int_distribution<std::mt19937::result_type>>(0,
                                                                  UINT32_MAX);
  }

  uint32_t get() { return (*dist)(*rng); }
};


auto main() -> int
{
  auto s = aslp_connection("127.0.0.1", 8000);
  auto gen = opgen();

  std::chrono::time_point begin = std::chrono::high_resolution_clock::now();

  auto add_mask = 0b00010001111111111111111111111111 ;
  auto add_set = 0b01000000000000000000000000000000 ;

  for (int i = 0; i < 50000; i++) {
    std::string c;
    auto op = gen.get();

    if ((i % 1000) == 0) {
      std::cout << "Did " << i << "\n";
    }

    try {
      std::string c;
      std::tie(std::ignore, c) = s.get_opcode(op);

    } catch (std::runtime_error& e) {
    }
  }
  auto end = std::chrono::high_resolution_clock::now();
  std::cout << std::chrono::duration_cast<std::chrono::milliseconds>(end-begin).count() << " ms" << std::endl;

  return 0;
}

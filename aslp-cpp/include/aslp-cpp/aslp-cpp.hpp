#pragma once

#include <map>
#include <memory>
#include <string>
#include <vector>

namespace httplib
{
class Client;
}  // namespace httplib

// tuple of encoding and semantics
using aslp_opcode_result_t = std::tuple<std::string, std::string>;

class aslp_connection
{
  using params_t = std::multimap<std::string, std::string>;

  const params_t& extra_params;
  std::unique_ptr<httplib::Client> client {nullptr};

public:
  aslp_connection(const std::string& server_addr, int server_port, const params_t& extra_params = {});
  aslp_connection(aslp_connection&&) noexcept;
  auto get_opcode(uint32_t opcode) -> aslp_opcode_result_t;
  void wait_active();
  ~aslp_connection();
};

class aslp_client
{
private:
  pid_t server_pid;
  const std::string server_addr;
  int server_port;
  void shutdown();

public:
  aslp_client(const aslp_client&) = delete;
  aslp_client(aslp_client&&) = delete;
  auto operator=(const aslp_client&) -> aslp_client& = delete;
  auto operator=(aslp_client&&) -> aslp_client& = delete;

  /**
   * Creates a new aslp_client with the given details.
   */
  aslp_client(pid_t pid, std::string addr, int port)
      : server_pid(pid)
      , server_addr(std::move(addr))
      , server_port(port)
  {
  }

  /**
   * Creates a new aslp_client with a managed server on
   * the default address, localhost:8000.
   */
  std::unique_ptr<aslp_client> static start()
  {
    return start("127.0.0.1", 8000);
  }

  /** Creates a new managed aslp_client with the given address and port. */
  auto static start(const std::string& addr,
                    int server_port) -> std::unique_ptr<aslp_client>;

  /** Returns the semantics for the given opcode, as a newline-separated string.
   */
  auto get_opcode(uint32_t opcode) -> aslp_opcode_result_t;

  /** Destroys the aslp_client and terminates the managed server as well. */
  virtual ~aslp_client() { shutdown(); };
};

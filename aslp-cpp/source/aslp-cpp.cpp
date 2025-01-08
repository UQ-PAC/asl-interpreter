#include <algorithm>
#include <cassert>
#include <chrono>
#include <csignal>
#include <filesystem>
#include <format>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

#include "aslp-cpp/aslp-cpp.hpp"

#include <sys/wait.h>
#include <unistd.h>

#include "httplib.h"
#include "json.hpp"

std::unordered_map<std::string, std::unique_ptr<aslp_connection>> servers {};

auto find_proc_stat(const std::filesystem::path& path, const std::string& stat)
    -> std::optional<std::string>
{
  std::ifstream stream {path};

  for (std::string line; std::getline(stream, line);) {
    auto delim = line.find(':');
    if (delim == std::string::npos) {
      continue;
    }
    std::string left = line.substr(0, delim);
    if (left != stat) {
      continue;
    }
    auto ndelim = line.find_first_not_of(" \t", delim + 1);
    if (ndelim == std::string::npos) {
      continue;
    }
    std::string right = line.substr(ndelim);
    return right;
  }

  return {};
}

auto parse_proc_stat(std::filesystem::path p)
    -> std::unordered_map<std::string, std::string>
{
  std::ifstream s {p};
  std::unordered_map<std::string, std::string> res {};

  for (std::string line; std::getline(s, line);) {
    auto delim = line.find(":");
    if (delim == std::string::npos) {
      continue;
    }
    std::string left = line.substr(0, delim);
    auto ndelim = line.find_first_not_of(" \t", delim + 1);
    if (ndelim == std::string::npos) {
      continue;
    }
    std::string right = line.substr(ndelim);
    res[left] = right;
  }

  return res;
}

/**
 * Iterate /proc/$pid/status to find all children of the given process.
 */
auto get_proc_children(std::vector<pid_t>& procs,
                       pid_t proc,
                       bool recursive = false) -> std::vector<pid_t>
{
  const std::filesystem::path procpath {"/proc/"};

  std::ranges::for_each(
      std::filesystem::directory_iterator {procpath},
      [proc, &procs, recursive](const auto& dir_entry)
      {
        std::filesystem::path status {dir_entry.path() / "status"};
        if (std::filesystem::exists(status)
            && std::filesystem::is_regular_file(status))
        {
          auto parent = find_proc_stat(status, "PPid");
          if (std::stoi(parent.value_or("0")) == proc) {
            int child = std::stoi(dir_entry.path().filename().string());
            procs.push_back(child);
            if (recursive)
              (get_proc_children(procs, child));
          }
        }
      });
  return procs;
}

auto get_proc_children(pid_t proc) -> std::vector<pid_t>
{
  std::vector<pid_t> pids {proc};
  return get_proc_children(pids, proc, /*recursive=*/false);
}

auto get_proc_children_transitive(pid_t proc) -> std::vector<pid_t>
{
  std::vector<pid_t> pids {proc};
  return get_proc_children(pids, proc, /*recursive=*/true);
}

auto aslp_client::start(const std::string& addr,
                        int server_port) -> std::unique_ptr<aslp_client>
{
  auto pid = fork();

  if (pid != 0) {
    return std::make_unique<aslp_client>(pid, addr, server_port);
  } else {
    auto command = std::format(
        "opam exec -- aslp-server --host {} --port {}", addr, server_port);
    std::cerr << command << std::endl;
    std::system(command.c_str());
    std::cerr << "Child process exited." << std::endl;
    return {nullptr};
  }

  assert(false);  // unreachable
  return {nullptr};
}

void aslp_connection::wait_active()
{
  auto req = client->Get("/");

  while (req.error() != httplib::Error::Success) {
    std::this_thread::sleep_for(std::chrono::milliseconds(1000));
    req = client->Get("/");
  }
}

aslp_opcode_result_t aslp_connection::get_opcode(uint32_t opcode)
{
  auto codestr = std::format("{:#x}", opcode);
  auto params = httplib::Params({{"opcode", codestr}});
  for (const auto& pair : extra_params) {
    params.insert(pair);
  }
  auto req = client->Get("/", params, httplib::Headers());

  if (req.error() != httplib::Error::Success) {
    throw std::runtime_error(
        std::format("Error {}", httplib::to_string(req.error())));
  }

  auto result = nlohmann::json::parse(req->body);

  if (result.contains("error")) {
    throw std::runtime_error(result["error"]);
  }
  if (!result.contains("semantics")) {
    throw std::runtime_error("semantics missing");
  }
  if (!result.contains("encoding")) {
    throw std::runtime_error("encoding name missing");
  }
  return {result["encoding"], result["semantics"]};
}

aslp_connection::aslp_connection(const std::string& server_addr,
                                 int server_port,
                                 const params_t& extra_params) :
  extra_params{extra_params},
  client{std::make_unique<httplib::Client>(server_addr, server_port)}
{}

aslp_connection::aslp_connection(aslp_connection&&) noexcept = default;
aslp_connection::~aslp_connection() = default;

aslp_opcode_result_t aslp_client::get_opcode(uint32_t opcode)
{
  aslp_connection conn {server_addr, server_port};
  conn.wait_active();
  return conn.get_opcode(opcode);
}

void aslp_client::shutdown()
{
  auto children = get_proc_children_transitive(server_pid);
  for (auto c : children) {
    std::cout << "Killing " << c << "\n";
    kill(c, SIGINT);
  }
  wait(nullptr);
}

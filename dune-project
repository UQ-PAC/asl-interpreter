(lang dune 2.8)
(name asli)
(version 0.2.0)

(using menhir 2.0)

(package
  (name asli)
  (synopsis "Interpreter for Arm's Architecture Specification Language (ASL)")
  (description "\| Interpreter for the language ASL that Arm uses to write their ISA specifications.
               "\|
               "\| Currently supports reading/typechecking the specification,
               "\| interactive execution of ASL statements and expressions,
               "\| executing opcodes one at a time,
               "\| loading ELF files and executing Arm binaries.
  )
  (depends
    ("ocaml"     (>= "4.14"))
    ("menhir"    :build)
    ("ott"       (and :build (>= "0.31")))
    "linenoise"
    "pprint"
    "zarith"
    ("z3"        (>= "4.8.7"))
    ("alcotest"  :with-test)
    "ppx_blob"
    "lwt"
    "cohttp-lwt-unix"
    "yojson"
    "mlbdd"
  )
)

(package
  (name aslp_offline)
  (synopsis "AArch64 Offline lifter")
  (description "" )
  (depends
    ("ocaml"     (>= "4.14"))
    "asli"
  )
)

(license BSD-3-Clause)
(authors "UQ-PAC")
(maintainers "UQ-PAC")
(source (github UQ-PAC/aslp))
(bug_reports "https://github.com/UQ-PAC/aslp/issues")
(homepage "https://github.com/UQ-PAC/aslp")
; (documentation ...)

(generate_opam_files true)
(cram enable)

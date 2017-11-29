open OUnit2

let () =
  [
    Parsing_tests.tt;
    Codegen_tests.tt;
    Expand_tests.tt;
    Pass_typeck_tests.tt;
  ]
  |> test_list
  |> run_test_tt_main

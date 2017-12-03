open OUnit2
open Migrate_parsetree
open Ast_405.Parsetree
open Ast_405.Longident
open Ast_405.Ast_helper

let stri_type_decl stri =
  match stri.pstr_desc with
  | Pstr_type (_, [td]) -> td
  | _ -> raise (Failure "incorrect structure item accessor")

let stri_mod_bind stri =
  match stri.pstr_desc with
  | Pstr_module mb -> mb
  | _ -> raise (Failure "incorrect structure item accessor")

let stri_value_binding e =
  match e.pstr_desc with
  | Pstr_value (_, [vb]) -> vb
  | _ -> raise (Failure "incorrect expression accessor")

let expr_function_cases e =
  match e.pexp_desc with
  | Pexp_function cases -> cases
  | _ -> raise (Failure "incorrect expression accessor")


let test_L0 =
  stri_mod_bind
    [%stri module Test_L0 = struct
       type a = [ `A of b | `A0 ]
       and b = [ `B of a ]
     end]
  |> Nanocaml.Lang.language_of_module

let test_L0_a = Nanocaml.Lang.language_nonterm test_L0 "a"
let test_L0_b = Nanocaml.Lang.language_nonterm test_L0 "b"

let () =
  Hashtbl.add Nanocaml.Lang.languages "Test_L0" test_L0

let tt =
  "parsing" >:::
    let open Nanocaml.Lang in
    let open Nanocaml.Pass in
    let nt_names = ["expr"; "stmt"] in
    let t_of_ct = type_of_core_type ~nt_names in
    let nt_of_td = nonterm_of_type_decl ~nt_names in
    let l_of_mb = language_of_module in
    let loc = !default_loc in
    [

      "type_of_core_type(1)" >::
        begin fun _ ->
        match t_of_ct [%type: (int * expr) list] with
        | NP_list
          (NP_tuple
             [NP_term {ptyp_desc = Ptyp_constr ({txt = Lident "int"}, [])};
              NP_nonterm "expr"]) -> ()
        | _ ->
           assert_failure "[(int * expr) list] does not match"
        end;

      "type_of_core_type(2)" >::
        begin fun _ ->
        match t_of_ct [%type: int list] with
        | NP_term {ptyp_desc = Ptyp_constr ({txt = Lident "list"}, _)} -> ()
        | _ -> assert_failure "[int list] should be a list terminal"
        end;

      "type_of_core_type(3)" >::
        begin fun _ ->
        match t_of_ct [%type: int * string] with
        | NP_term {ptyp_desc = Ptyp_tuple [_; _]} -> ()
        | _ -> assert_failure "[int * string] should be a tuple terminal"
        end;

      "nonterm_of_type_decl(1)" >::
        begin fun _ ->
        match stri_type_decl
                [%stri type expr =
                   [ `Two of string * int
                   | `Zero ] ]
              |> nt_of_td
        with
        | {npnt_name = "expr";
           npnt_productions = [
               {nppr_name = "Two"; nppr_arg = Some _};
               {nppr_name = "Zero"; nppr_arg = None} ]} -> ()
        | _ ->
           assert_failure "expr nonterm has the wrong structure"
        end;

      "nonterm_of_type_decl(2)" >::
        begin fun _ ->
        try
          stri_type_decl
            [%stri type expr =
               Var of string
             | Int of int ]
          |> nt_of_td
          |> ignore;
          assert_failure "expected nonterm to fail"
        with Location.Error _ -> ()
        end;

      "language_of_module(1)" >::
        begin fun _ ->
        let lang =
          stri_mod_bind
            [%stri module L0 = struct
               type a = [ `A of b ]
               and b = [ `B of a ]
             end]
          |> l_of_mb
        in
        assert_equal "L0" lang.npl_name;
        assert_equal ["a"; "b"] (List.map (fun nt -> nt.npnt_name) lang.npl_nonterms);
        assert_equal [ {nppr_name = "A"; nppr_arg = Some (NP_nonterm "b") };
                       {nppr_name = "B"; nppr_arg = Some (NP_nonterm "a") } ]
          (lang.npl_nonterms
           |> List.map (fun nt -> nt.npnt_productions)
           |> List.concat);
        end;

      "language_of_module(2)" >::
        begin fun _ ->
        try
          stri_mod_bind
            [%stri module L0 = struct
               type a = [ `A of b ]
               type b = [ `B of a ] (* must be single recursive declaration *)
             end ]
          |> l_of_mb
          |> ignore;
          assert_failure "expected language to fail"
        with Location.Error _ -> ()
        end;

      "language_of_module(3)" >::
        begin fun _ ->
        let lang =
          stri_mod_bind
            [%stri module L1 = struct
               include Test_L0
               type c = [ `C of int ]
             end ]
          |> l_of_mb
        in
        assert_equal ["c"; "a"; "b"] (List.map (fun nt -> nt.npnt_name) lang.npl_nonterms)
        end;

      "language_of_module(4)" >::
        begin fun _ ->
        let lang =
          stri_mod_bind
            [%stri module L1 = struct
               include Test_L0
               type a = { del : [ `A ]
                        ; add : [ `AB of a * b ] }
             end ]
          |> l_of_mb
        in
        assert_equal ["a"; "b"] (List.map (fun nt -> nt.npnt_name) lang.npl_nonterms);
        let a_nt = List.find (fun nt -> nt.npnt_name = "a") lang.npl_nonterms in
        let a_prods = a_nt.npnt_productions in
        assert_equal ["AB"; "A0"] (List.map (fun pr -> pr.nppr_name) a_prods);
        end;

      "pat_of_pattern(1)" >::
        begin fun _ ->
        let p1 = [%pat? 3] in
        let p2 = [%pat? x] in
        let p3 = [%pat? (_, y)] in
        assert_equal (NPpat p1) (pat_of_pattern p1);
        assert_equal (NPpat_var {txt = "x"; loc = p2.ppat_loc}) (pat_of_pattern p2);
        match pat_of_pattern p3 with
        | NPpat_tuple ([ NPpat_any _; NPpat_var {txt = "y"} ], _) -> ()
        | _ -> assert_failure "np_pat tuple does not match"
        end;

      "pat_of_pattern(2)" >::
        begin fun _ ->
        match pat_of_pattern [%pat? x [@l]] with
        | NPpat_map (NPpat_var {txt = "x"}) -> ()
        | _ -> assert_failure "np_pat list does not match"
        end;

      "pat_of_pattern(3)" >::
        begin fun _ ->
        match pat_of_pattern [%pat? (x,y) [@r] [@l]] with
        | NPpat_map (NPpat_cata (NPpat_tuple _, None)) -> ()
        | _ -> assert_failure "np_pat cata + list + tuple does not match"
        end;

      "pat_of_pattern(4)" >::
        begin fun _ ->
        match pat_of_pattern [%pat? (`X (_, _), (`Y as y))] with
        | NPpat_tuple ([ NPpat_variant ("X", Some (NPpat_tuple _), _);
                         NPpat_alias (NPpat_variant ("Y", None, _), {txt = "y"}) ],
                       _)
          -> ()
        | _ -> assert_failure "np_pat variant does not match"
        end;

      (* currently unimplemented *)
      (* "pat_of_pattern(4)" >::
        begin fun _ ->
        match pat_of_pattern [%pat? e' [@r expr]] with
        | NPpat_cata (NPpat_var _, Some {pexp_desc = Pexp_ident {txt = Lident "expr"}}) -> ()
        | _ -> assert_failure "np_pattern explicit cata does not match"
        end; *)

      "processor_of_rhs(1)" >::
        begin fun _ ->
        match processor_of_rhs ~name:"a" ~dom:test_L0_a ~cod:None ~loc
                [%expr fun x ~y ->
                    function
                    | `Var x -> `Var (find x)
                    | `Let (x, e[@r], e') -> push x; expr e'
                ] with
        | {npc_name = "a";
           npc_dom = dom;
           npc_args = [ (Asttypes.Nolabel, _, {ppat_desc = Ppat_var {txt = "x"}});
                        (Asttypes.Labelled "y", _, {ppat_desc = Ppat_var {txt = "y"}}) ];
           npc_clauses = clauses}
          ->
           assert_equal test_L0_a dom;
           begin match clauses with
           | [ NPpat_variant ("Var", _, _), _;
               NPpat_variant ("Let", _, _), _ ] -> ()
           | _ -> assert_failure "clauses do not match"
           end;
        | _ -> assert_failure "processor does not match"
        end;

      "processor_of_rhs(2)" >::
        begin fun _ ->
        try
          [%expr fun x y -> 0]
          |> processor_of_rhs ~name:"a" ~dom:test_L0_a ~cod:None ~loc
          |> ignore;
          assert_failure "expected processor to fail (no 'function')"
        with Location.Error _ -> ()
        end;

      "processor_of_rhs(3)" >::
        begin fun _ ->
        try
          [%expr function
              | `Foo when some_guard -> 0
              | `Bar -> 1]
          |> processor_of_rhs ~name:"a" ~dom:test_L0_a ~cod:None ~loc
          |> ignore;
          assert_failure "expected processor to fail (guard not allowed)"
        with Location.Error _ -> ()
        end;

      "extract_pass_sig(1)" >::
        begin fun _ ->
        let (l0, _), (l1, _) = extract_pass_sig [%expr La => Lb] in
        assert_equal "La" l0;
        assert_equal "Lb" l1;
        end;

      "extract_pass_sig(2)" >::
        begin fun _ ->
        try
          extract_pass_sig [%expr la => Lb]
          |> ignore;
          assert_failure "expected pass_sig to fail (non module argument)"
        with Location.Error _ -> ()
        end;

      "extract_pass_sig(3)" >::
        begin fun _ ->
        try
          extract_pass_sig [%expr (=>) La Lb Lc]
          |> ignore;
          assert_failure "expected pass_sig to fail (too many arguments)"
        with Location.Error _ -> ()
        end;

      "extract_pass_sig(4)" >::
        begin fun _ ->
        try
          extract_pass_sig [%expr La --> Lb]
          |> ignore;
          assert_failure "expected pass_sig to fail (wrong arrow)"
        with Location.Error _ -> ()
        end;

      "extract_dom_cod(1)" >::
        begin fun _ ->
        let extr = extract_dom_cod ~loc test_L0 test_L0 in
        assert_equal (test_L0_a, None) (extr "a_thing");
        assert_equal (test_L0_a, None) (extr "a_to_thing");
        assert_equal (test_L0_a, None) (extr "thing_of_a");
        assert_equal (test_L0_a, Some (test_L0_b)) (extr "b_of_a");
        assert_equal (test_L0_a, Some (test_L0_b)) (extr "a_to_b");
        assert_equal (test_L0_a, Some (test_L0_a)) (extr "a");
        assert_equal (test_L0_b, Some (test_L0_b)) (extr "b");
        end;

      "extract_dom_cod(2)" >::
        begin fun _ ->
        try
          extract_dom_cod ~loc test_L0 test_L0 "c" |> ignore;
          assert_failure "expected to fail";
        with Location.Error _ -> ()
        end;

      "extract_dom_cod(3)" >::
        begin fun _ ->
        try
          extract_dom_cod ~loc test_L0 test_L0 "_" |> ignore;
          assert_failure "expected to fail";
        with Location.Error _ -> ()
        end;

      "pass_of_value_binding(1)" >::
        begin fun _ ->
        match stri_value_binding
                [%stri let[@pass Test_L0 => Test_L0] remove_a ini =
                   let tmp = 0 in
                   let rec a = function
                     | `A _ -> `A0
                   in
                   a ini]
              |> pass_of_value_binding
        with
        | {npp_name = "remove_a";
           npp_input = li;
           npp_output = lo;
           npp_pre = pre;
           npp_post = {pexp_desc =
                         Pexp_apply
                           ({pexp_desc = Pexp_ident {txt = Lident "a"}},
                            [ Nolabel, {pexp_desc = Pexp_ident {txt = Lident "ini"}} ])};
           npp_procs = [ a_proc ]}
          ->
           assert_equal "Test_L0" li.npl_name;
           assert_equal "Test_L0" lo.npl_name;
           assert_equal "a" a_proc.npc_name;
           assert_equal test_L0_a a_proc.npc_dom;
           assert_equal (Some test_L0_a) a_proc.npc_cod;
           assert_equal 1 (List.length a_proc.npc_clauses);

           let body = [%expr 1 + 2 + 3] in
           begin match pre body with
           | {pexp_desc =
                Pexp_fun (Nolabel, None, (* fun ini -> *)
                          {ppat_desc = Ppat_var {txt = "ini"}},
                          {pexp_desc =
                             Pexp_let (Nonrecursive, (* let tmp = .. in *)
                                       [ {pvb_pat = {ppat_desc = Ppat_var {txt = "tmp"}}} ],
                                       body')})}
             ->
              assert_equal body body'
           | _ -> assert_failure "prefix has wrong structure"
           end

        | _ -> assert_failure "pass has wrong structure"
        end;

      "pass_of_value_binding(2)" >::
        begin fun _ ->
        match stri_value_binding
                [%stri let[@pass Test_L0 => Test_L0] remove_a =
                   let tmp = 0 in
                   [%passes
                     let[@entry] rec a = function
                       | `A _ -> `A0 ] ]
              |> pass_of_value_binding
        with
        | {npp_name = "remove_a";
           npp_input = li;
           npp_output = lo;
           npp_pre = pre;
           npp_post = {pexp_desc = Pexp_ident {txt = Lident "a"}};
           npp_procs = [ a_proc ]}
          ->
           ()

        | _ -> assert_failure "pass has wrong structure"
        end;

      "pass_of_value_binding(3)" >::
        begin fun _ ->
        try
          stri_value_binding
            [%stri let[@pass Test_L0 => L1] foo =
               let rec a = function | `A _ -> `A0
               in a ]
          |> pass_of_value_binding
          |> ignore;
          assert_failure "expected failure for missing language"
        with Location.Error _ -> ()
        end;

      "pass_of_value_binding(4)" >::
        begin fun _ ->
        try
          stri_value_binding
            [%stri let[@pass Test_L0 => Test_L0] foo =
               let rec c = function
                 | `A _ -> `A0
               in c ]
          |> pass_of_value_binding
          |> ignore;
          assert_failure "expected failure for missing nonterminal"
        with Location.Error _ -> ()
        end;

      "pass_of_value_binding(5)" >::
        begin fun _ ->
        try
          stri_value_binding
            [%stri let[@pass Test_L0 => Test_L0] foo = 0 ]
          |> pass_of_value_binding
          |> ignore;
          assert_failure "expected failure for missing productions letrec"
        with Location.Error _ -> ()
        end;

      "pass_of_value_binding(6)" >::
        begin fun _ ->
        try
          stri_value_binding
            [%stri let[@pass Test_L0 => Test_L0] foo =
               let a = function
                 | `A _ -> `A0
               in a ]
          |> pass_of_value_binding
          |> ignore;
          assert_failure "expected failure for missing 'rec'"
        with Location.Error _ -> ()
        end;

    ]

open TClib.Tcimpl

let print_tree tc : unit =
  let rec aux dep tc = 
    let Node ({ info_tid = x; info_clk = clk_x; info_aclk = aclk_x }, chn) = tc in
    for i = 1 to dep do
      print_char ' '
    done;
    print_int x; 
    print_string "   clk: ";
    print_int clk_x;
    print_string "   aclk: ";
    print_int aclk_x;
    print_char '\n'; 
    List.iter (aux (dep + 2)) chn
  in aux 0 tc

let rec construct_tree () : int treeclock =
  let x = read_int () in
  let clk_x = read_int () in
  let aclk_x = read_int () in
  let chn_sz_x = read_int () in
  let chn = construct_children chn_sz_x in
  Node ({ info_tid = x; info_clk = clk_x; info_aclk = aclk_x }, chn)
and construct_children n : (int treeclock) list =
  if n <= 0
  then []
  else 
    let ch = construct_tree () in
    ch :: (construct_children (n-1))

let dom_check (dom1 : int nodeinfo list) (dom2 : int nodeinfo list) : bool = 
  (List.sort_uniq compare (List.map (fun x -> x.info_tid) dom1)) = 
  (List.sort compare (List.map (fun x -> x.info_tid) dom2))

let test_join (tc : int treeclock) (tc_ : int treeclock) verbosity : bool =
  let tc_max = tc_join ( = ) tc tc_ in
  let dom_original = List.append (tc_flatten tc) (tc_flatten tc_) in 
  let dom_new = tc_flatten tc_max in
  (if verbosity >= 1
    then begin 
      print_char '\n';
      print_tree tc;
      print_char '\n';
      print_tree tc_;
      print_char '\n';
      print_tree tc_max
    end
    else ());
  if dom_check dom_original dom_new
  then begin
    let res_fail = (List.filter (fun { info_tid = x; info_clk = clk_x; _ } -> 
    clk_x <> (max (tc_getclk ( = ) tc x) (tc_getclk ( = ) tc_ x))) dom_new) in
      match res_fail with
      | [] -> true
      | { info_tid = x; info_clk = clk_x_fail; _ } :: _ -> 
        print_string "maximal check error!\n";  
        print_string "For thread "; print_int x; 
        print_string ", expected "; print_int (max (tc_getclk ( = ) tc x) (tc_getclk ( = ) tc_ x)); 
        print_string ", got "; print_int clk_x_fail; 
        print_char '\n'; false 
    end
  else (print_string "dom check error!\n"; false)

let sanity_check (tc : int treeclock) (tc_ : int treeclock) : bool =
  (* see 1.test *)
  (tc_rootinfo tc).info_clk >= (tc_getclk ( = ) tc_ (tc_rootinfo tc).info_tid)

let _ = 
  assert (Array.length Sys.argv = 2);
  let tc = construct_tree () in
  let tc_ = construct_tree () in
  if sanity_check tc tc_
  then assert (test_join tc tc_ (int_of_string Sys.argv.(1)))
  else ()
      (* print_string "ok, let's skip this. \n" *)

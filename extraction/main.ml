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
  if dom_check (List.map tc_rootinfo dom_original) (List.map tc_rootinfo dom_new)
  then begin
    let res_fail = (List.filter (fun { info_tid = x; info_clk = clk_x; _ } -> 
    clk_x <> (max (tc_getclk ( = ) x tc) (tc_getclk ( = ) x tc_))) (List.map tc_rootinfo dom_new)) in
      match res_fail with
      | [] -> true
      | { info_tid = x; info_clk = clk_x_fail; _ } :: _ -> 
        print_string "maximal check error!\n";  
        print_string "For thread "; print_int x; 
        print_string ", expected "; print_int (max (tc_getclk ( = ) x tc) (tc_getclk ( = ) x tc_)); 
        print_string ", got "; print_int clk_x_fail; 
        print_char '\n'; false 
    end
  else (print_string "dom check error!\n"; false)

let sanity_check (tc : int treeclock) (tc_ : int treeclock) : bool =
  (* see 1.test *)
  (tc_rootinfo tc).info_clk >= (tc_getclk ( = ) (tc_rootinfo tc).info_tid tc_)

let output_tree (tc : int treeclock) (filename : string) : unit =
  let rec aux oc (Node ({ info_tid = x; info_clk = clk_x; info_aclk = aclk_x }, chn)) = begin
    Printf.fprintf oc "%d\n%d\n%d\n%d\n" x clk_x aclk_x (List.length chn);
    List.iter (aux oc) chn
  end in
  let oc = open_out filename in
  aux oc tc; close_out oc

let rec normalize_tree (tc : int treeclock) : int treeclock =
  let Node (ni, chn) = tc in
  let chn_ = List.sort (fun tc tc_ -> compare (tc_roottid tc) (tc_roottid tc_)) (List.map normalize_tree chn) in
  Node (ni, chn_)

type event = { sender : int; sendtime : int; receiver : int; recvtime : int }

let read_event () : event =
  let sender = read_int () in
  let sendtime = read_int () in
  let receiver = read_int () in
  let recvtime = read_int () in
  { sender; sendtime; receiver; recvtime }

let read_history () : int * event list =
  let rec aux n =
    if n <= 0
    then []
    else 
      let ch = read_event () in
      ch :: (aux (n-1))
  in 
  let num_process = read_int () in
  let num_message = read_int () in
  (num_process, aux num_message)

let clock_simulate (num_process : int) (history : event list) : int treeclock list =
  let local_clocks = Array.init num_process (fun (i : int) -> tc_init i) in
  let simulate_step (e : event) : unit = begin
    let snd = e.sender - 1 in
    let rcv = e.receiver - 1 in
    local_clocks.(snd) <- tc_incr local_clocks.(snd) 1;
    local_clocks.(rcv) <- tc_incr local_clocks.(rcv) 1;
    local_clocks.(rcv) <- tc_join ( = ) local_clocks.(rcv) local_clocks.(snd)
  end in
  List.iter simulate_step history;
  Array.to_list local_clocks

let _ = 
  assert (Array.length Sys.argv <= 4 && Array.length Sys.argv >= 2);
  match Sys.argv.(1) with
  | "print" -> begin
    (* read from stdin *)
    let treenum = (int_of_string Sys.argv.(2)) in
    for i = 1 to treenum do
      let tc = construct_tree () in
      print_tree tc;
      print_char '\n'
    done
  end
  | "testjoin" -> begin
    let tc = construct_tree () in
    let tc_ = construct_tree () in
    if sanity_check tc tc_
    then begin
      assert (test_join tc tc_ (int_of_string Sys.argv.(2)));
      if (Array.length Sys.argv == 4)
        then output_tree (tc_join ( = ) tc tc_) Sys.argv.(3)
        else ()
    end
  end
  | "simulate" -> begin
    (* read from stdin *)
    let num_process, history = read_history () in
    let res = clock_simulate num_process history in
    let res_ = List.map (fun tc -> normalize_tree (tc_eraseaclk tc)) res in
    List.iteri (fun i tc -> output_tree tc (Sys.argv.(2) ^ (string_of_int i) ^ ".tr")) res_
  end
  | _ -> ()

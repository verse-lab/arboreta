From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.11".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "aarch64".
  Definition model := "default".
  Definition abi := "apple".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "treeclock_ndt.c".
  Definition normalized := true.
End Info.

Definition _Clock : ident := $"Clock".
Definition _Node : ident := $"Node".
Definition _S : ident := $"S".
Definition _TreeClock : ident := $"TreeClock".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_cls : ident := $"__builtin_cls".
Definition ___builtin_clsl : ident := $"__builtin_clsl".
Definition ___builtin_clsll : ident := $"__builtin_clsll".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fence : ident := $"__builtin_fence".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition _c : ident := $"c".
Definition _cl : ident := $"cl".
Definition _clock_aclk : ident := $"clock_aclk".
Definition _clock_clk : ident := $"clock_clk".
Definition _clocks : ident := $"clocks".
Definition _cr : ident := $"cr".
Definition _delta : ident := $"delta".
Definition _detach_from_neighbors : ident := $"detach_from_neighbors".
Definition _dim : ident := $"dim".
Definition _get_updated_nodes_copy_chn : ident := $"get_updated_nodes_copy_chn".
Definition _get_updated_nodes_join_chn : ident := $"get_updated_nodes_join_chn".
Definition _head_child : ident := $"head_child".
Definition _increment_clock : ident := $"increment_clock".
Definition _is_less_than_or_equal : ident := $"is_less_than_or_equal".
Definition _join : ident := $"join".
Definition _main : ident := $"main".
Definition _malloc : ident := $"malloc".
Definition _memset : ident := $"memset".
Definition _monotone_copy : ident := $"monotone_copy".
Definition _nd : ident := $"nd".
Definition _nd_par : ident := $"nd_par".
Definition _ndtmp : ident := $"ndtmp".
Definition _next_node : ident := $"next_node".
Definition _node_headch : ident := $"node_headch".
Definition _node_is_null : ident := $"node_is_null".
Definition _node_next : ident := $"node_next".
Definition _node_par : ident := $"node_par".
Definition _node_prev : ident := $"node_prev".
Definition _par : ident := $"par".
Definition _par_clock : ident := $"par_clock".
Definition _par_node : ident := $"par_node".
Definition _parent_node : ident := $"parent_node".
Definition _prev_node : ident := $"prev_node".
Definition _push_child : ident := $"push_child".
Definition _read_clock : ident := $"read_clock".
Definition _root_tid : ident := $"root_tid".
Definition _root_tid_this : ident := $"root_tid_this".
Definition _self : ident := $"self".
Definition _self_root_clocks : ident := $"self_root_clocks".
Definition _t : ident := $"t".
Definition _t_next : ident := $"t_next".
Definition _t_parent : ident := $"t_parent".
Definition _t_prev : ident := $"t_prev".
Definition _targ : ident := $"targ".
Definition _tc : ident := $"tc".
Definition _tc_new : ident := $"tc_new".
Definition _tid : ident := $"tid".
Definition _top : ident := $"top".
Definition _tree : ident := $"tree".
Definition _tree_clock_init : ident := $"tree_clock_init".
Definition _u_clock : ident := $"u_clock".
Definition _u_clocks : ident := $"u_clocks".
Definition _u_node : ident := $"u_node".
Definition _uprime_clocks : ident := $"uprime_clocks".
Definition _uprime_node : ident := $"uprime_node".
Definition _uprime_tid : ident := $"uprime_tid".
Definition _v_clock : ident := $"v_clock".
Definition _v_clocks : ident := $"v_clocks".
Definition _val : ident := $"val".
Definition _vprime_clocks : ident := $"vprime_clocks".
Definition _vprime_tid : ident := $"vprime_tid".
Definition _write_clock : ident := $"write_clock".
Definition _y : ident := $"y".
Definition _z_clock : ident := $"z_clock".
Definition _z_clocks : ident := $"z_clocks".
Definition _z_node : ident := $"z_node".
Definition _zprime_clock : ident := $"zprime_clock".
Definition _zprime_clocks : ident := $"zprime_clocks".
Definition _zprime_tid : ident := $"zprime_tid".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_node_is_null := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_nd, (tptr (Tstruct _Node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'7, tint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'6
          (Efield
            (Ederef (Etempvar _nd (tptr (Tstruct _Node noattr)))
              (Tstruct _Node noattr)) _node_next tint))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tint)
                       (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tint)
          (Ssequence
            (Sset _t'7
              (Efield
                (Ederef (Etempvar _nd (tptr (Tstruct _Node noattr)))
                  (Tstruct _Node noattr)) _node_prev tint))
            (Sset _t'1
              (Ecast
                (Ebinop Oeq (Etempvar _t'7 tint)
                  (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tint)
                tbool)))
          (Sset _t'1 (Econst_int (Int.repr 0) tint))))
      (Sifthenelse (Etempvar _t'1 tint)
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _nd (tptr (Tstruct _Node noattr)))
                (Tstruct _Node noattr)) _node_par tint))
          (Sset _t'2
            (Ecast
              (Ebinop Oeq (Etempvar _t'5 tint)
                (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tint) tbool)))
        (Sset _t'2 (Econst_int (Int.repr 0) tint))))
    (Sifthenelse (Etempvar _t'2 tint)
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _nd (tptr (Tstruct _Node noattr)))
              (Tstruct _Node noattr)) _node_headch tint))
        (Sset _t'3
          (Ecast
            (Ebinop Oeq (Etempvar _t'4 tint)
              (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tint) tbool)))
      (Sset _t'3 (Econst_int (Int.repr 0) tint))))
  (Sreturn (Some (Etempvar _t'3 tint))))
|}.

Definition f_tree_clock_init := {|
  fn_return := (tptr (Tstruct _TreeClock noattr));
  fn_callconv := cc_default;
  fn_params := ((_dim, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_tc_new, (tptr (Tstruct _TreeClock noattr))) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr tvoid)) ::
               (_t'2, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'6, (tptr (Tstruct _Clock noattr))) ::
               (_t'5, (tptr (Tstruct _Node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid) cc_default))
      ((Esizeof (Tstruct _TreeClock noattr) tulong) :: nil))
    (Sset _tc_new
      (Ecast (Etempvar _t'1 (tptr tvoid)) (tptr (Tstruct _TreeClock noattr)))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _tc_new (tptr (Tstruct _TreeClock noattr)))
          (Tstruct _TreeClock noattr)) _root_tid tint)
      (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _tc_new (tptr (Tstruct _TreeClock noattr)))
            (Tstruct _TreeClock noattr)) _dim tint) (Etempvar _dim tint))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                            cc_default))
            ((Ebinop Omul (Etempvar _dim tint)
               (Esizeof (Tstruct _Clock noattr) tulong) tulong) :: nil))
          (Sassign
            (Efield
              (Ederef (Etempvar _tc_new (tptr (Tstruct _TreeClock noattr)))
                (Tstruct _TreeClock noattr)) _clocks
              (tptr (Tstruct _Clock noattr)))
            (Ecast (Etempvar _t'2 (tptr tvoid))
              (tptr (Tstruct _Clock noattr)))))
        (Ssequence
          (Ssequence
            (Scall (Some _t'3)
              (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                              cc_default))
              ((Ebinop Omul (Etempvar _dim tint)
                 (Esizeof (Tstruct _Node noattr) tulong) tulong) :: nil))
            (Sassign
              (Efield
                (Ederef (Etempvar _tc_new (tptr (Tstruct _TreeClock noattr)))
                  (Tstruct _TreeClock noattr)) _tree
                (tptr (Tstruct _Node noattr)))
              (Ecast (Etempvar _t'3 (tptr tvoid))
                (tptr (Tstruct _Node noattr)))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'4)
                (Evar _malloc (Tfunction (Tcons tulong Tnil) (tptr tvoid)
                                cc_default))
                ((Ebinop Omul (Etempvar _dim tint) (Esizeof tint tulong)
                   tulong) :: nil))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _tc_new (tptr (Tstruct _TreeClock noattr)))
                    (Tstruct _TreeClock noattr)) _S (tptr tint))
                (Ecast (Etempvar _t'4 (tptr tvoid)) (tptr tint))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _tc_new (tptr (Tstruct _TreeClock noattr)))
                    (Tstruct _TreeClock noattr)) _top tint)
                (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
              (Ssequence
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef
                        (Etempvar _tc_new (tptr (Tstruct _TreeClock noattr)))
                        (Tstruct _TreeClock noattr)) _clocks
                      (tptr (Tstruct _Clock noattr))))
                  (Scall None
                    (Evar _memset (Tfunction
                                    (Tcons (tptr tvoid)
                                      (Tcons tint (Tcons tulong Tnil)))
                                    (tptr tvoid) cc_default))
                    ((Etempvar _t'6 (tptr (Tstruct _Clock noattr))) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Ebinop Omul (Etempvar _dim tint)
                       (Esizeof (Tstruct _Clock noattr) tulong) tulong) ::
                     nil)))
                (Ssequence
                  (Ssequence
                    (Sset _t'5
                      (Efield
                        (Ederef
                          (Etempvar _tc_new (tptr (Tstruct _TreeClock noattr)))
                          (Tstruct _TreeClock noattr)) _tree
                        (tptr (Tstruct _Node noattr))))
                    (Scall None
                      (Evar _memset (Tfunction
                                      (Tcons (tptr tvoid)
                                        (Tcons tint (Tcons tulong Tnil)))
                                      (tptr tvoid) cc_default))
                      ((Etempvar _t'5 (tptr (Tstruct _Node noattr))) ::
                       (Econst_int (Int.repr 0) tint) ::
                       (Ebinop Omul (Etempvar _dim tint)
                         (Esizeof (Tstruct _Node noattr) tulong) tulong) ::
                       nil)))
                  (Sreturn (Some (Etempvar _tc_new (tptr (Tstruct _TreeClock noattr))))))))))))))
|}.

Definition f_increment_clock := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_self, (tptr (Tstruct _TreeClock noattr))) ::
                (_delta, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_c, (tptr (Tstruct _Clock noattr))) :: (_t'3, tint) ::
               (_t'2, (tptr (Tstruct _Clock noattr))) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
          (Tstruct _TreeClock noattr)) _clocks
        (tptr (Tstruct _Clock noattr))))
    (Ssequence
      (Sset _t'3
        (Efield
          (Ederef (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
            (Tstruct _TreeClock noattr)) _root_tid tint))
      (Sset _c
        (Ebinop Oadd (Etempvar _t'2 (tptr (Tstruct _Clock noattr)))
          (Etempvar _t'3 tint) (tptr (Tstruct _Clock noattr))))))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _c (tptr (Tstruct _Clock noattr)))
          (Tstruct _Clock noattr)) _clock_clk tint))
    (Sassign
      (Efield
        (Ederef (Etempvar _c (tptr (Tstruct _Clock noattr)))
          (Tstruct _Clock noattr)) _clock_clk tint)
      (Ebinop Oadd (Etempvar _t'1 tint) (Etempvar _delta tint) tint))))
|}.

Definition f_write_clock := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_self, (tptr (Tstruct _TreeClock noattr))) ::
                (_val, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_c, (tptr (Tstruct _Clock noattr))) :: (_t'2, tint) ::
               (_t'1, (tptr (Tstruct _Clock noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
          (Tstruct _TreeClock noattr)) _clocks
        (tptr (Tstruct _Clock noattr))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
            (Tstruct _TreeClock noattr)) _root_tid tint))
      (Sset _c
        (Ebinop Oadd (Etempvar _t'1 (tptr (Tstruct _Clock noattr)))
          (Etempvar _t'2 tint) (tptr (Tstruct _Clock noattr))))))
  (Sassign
    (Efield
      (Ederef (Etempvar _c (tptr (Tstruct _Clock noattr)))
        (Tstruct _Clock noattr)) _clock_clk tint) (Etempvar _val tint)))
|}.

Definition f_read_clock := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_self, (tptr (Tstruct _TreeClock noattr))) ::
                (_tid, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_c, (tptr (Tstruct _Clock noattr))) ::
               (_t'2, (tptr (Tstruct _Clock noattr))) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
          (Tstruct _TreeClock noattr)) _clocks
        (tptr (Tstruct _Clock noattr))))
    (Sset _c
      (Ebinop Oadd (Etempvar _t'2 (tptr (Tstruct _Clock noattr)))
        (Etempvar _tid tint) (tptr (Tstruct _Clock noattr)))))
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _c (tptr (Tstruct _Clock noattr)))
          (Tstruct _Clock noattr)) _clock_clk tint))
    (Sreturn (Some (Etempvar _t'1 tint)))))
|}.

Definition f_is_less_than_or_equal := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_self, (tptr (Tstruct _TreeClock noattr))) ::
                (_tc, (tptr (Tstruct _TreeClock noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_root_tid, tint) :: (_cl, tint) :: (_cr, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _root_tid
    (Efield
      (Ederef (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
        (Tstruct _TreeClock noattr)) _root_tid tint))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _read_clock (Tfunction
                            (Tcons (tptr (Tstruct _TreeClock noattr))
                              (Tcons tint Tnil)) tint cc_default))
        ((Etempvar _self (tptr (Tstruct _TreeClock noattr))) ::
         (Etempvar _root_tid tint) :: nil))
      (Sset _cl (Etempvar _t'1 tint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'2)
          (Evar _read_clock (Tfunction
                              (Tcons (tptr (Tstruct _TreeClock noattr))
                                (Tcons tint Tnil)) tint cc_default))
          ((Etempvar _tc (tptr (Tstruct _TreeClock noattr))) ::
           (Etempvar _root_tid tint) :: nil))
        (Sset _cr (Etempvar _t'2 tint)))
      (Sreturn (Some (Ebinop Ole (Etempvar _cl tint) (Etempvar _cr tint)
                       tint))))))
|}.

Definition f_detach_from_neighbors := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_self, (tptr (Tstruct _TreeClock noattr))) :: (_t, tint) ::
                (_nd, (tptr (Tstruct _Node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t_next, tint) :: (_t_prev, tint) :: (_t_parent, tint) ::
               (_parent_node, (tptr (Tstruct _Node noattr))) ::
               (_prev_node, (tptr (Tstruct _Node noattr))) ::
               (_next_node, (tptr (Tstruct _Node noattr))) ::
               (_t'4, (tptr (Tstruct _Node noattr))) ::
               (_t'3, (tptr (Tstruct _Node noattr))) :: (_t'2, tint) ::
               (_t'1, (tptr (Tstruct _Node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t_next
    (Efield
      (Ederef (Etempvar _nd (tptr (Tstruct _Node noattr)))
        (Tstruct _Node noattr)) _node_next tint))
  (Ssequence
    (Sset _t_prev
      (Efield
        (Ederef (Etempvar _nd (tptr (Tstruct _Node noattr)))
          (Tstruct _Node noattr)) _node_prev tint))
    (Ssequence
      (Sset _t_parent
        (Efield
          (Ederef (Etempvar _nd (tptr (Tstruct _Node noattr)))
            (Tstruct _Node noattr)) _node_par tint))
      (Ssequence
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                (Tstruct _TreeClock noattr)) _tree
              (tptr (Tstruct _Node noattr))))
          (Sset _parent_node
            (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct _Node noattr)))
              (Etempvar _t_parent tint) (tptr (Tstruct _Node noattr)))))
        (Ssequence
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef (Etempvar _parent_node (tptr (Tstruct _Node noattr)))
                  (Tstruct _Node noattr)) _node_headch tint))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'2 tint) (Etempvar _t tint)
                           tint)
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _parent_node (tptr (Tstruct _Node noattr)))
                    (Tstruct _Node noattr)) _node_headch tint)
                (Etempvar _t_next tint))
              (Ssequence
                (Ssequence
                  (Sset _t'3
                    (Efield
                      (Ederef
                        (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                        (Tstruct _TreeClock noattr)) _tree
                      (tptr (Tstruct _Node noattr))))
                  (Sset _prev_node
                    (Ebinop Oadd
                      (Etempvar _t'3 (tptr (Tstruct _Node noattr)))
                      (Etempvar _t_prev tint) (tptr (Tstruct _Node noattr)))))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _prev_node (tptr (Tstruct _Node noattr)))
                      (Tstruct _Node noattr)) _node_next tint)
                  (Etempvar _t_next tint)))))
          (Sifthenelse (Ebinop One (Etempvar _t_next tint)
                         (Eunop Oneg (Econst_int (Int.repr 1) tint) tint)
                         tint)
            (Ssequence
              (Ssequence
                (Sset _t'1
                  (Efield
                    (Ederef
                      (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                      (Tstruct _TreeClock noattr)) _tree
                    (tptr (Tstruct _Node noattr))))
                (Sset _next_node
                  (Ebinop Oadd (Etempvar _t'1 (tptr (Tstruct _Node noattr)))
                    (Etempvar _t_next tint) (tptr (Tstruct _Node noattr)))))
              (Sassign
                (Efield
                  (Ederef (Etempvar _next_node (tptr (Tstruct _Node noattr)))
                    (Tstruct _Node noattr)) _node_prev tint)
                (Etempvar _t_prev tint)))
            Sskip))))))
|}.

Definition f_push_child := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_self, (tptr (Tstruct _TreeClock noattr))) ::
                (_par, tint) :: (_t, tint) ::
                (_nd, (tptr (Tstruct _Node noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_par_node, (tptr (Tstruct _Node noattr))) ::
               (_head_child, tint) ::
               (_ndtmp, (tptr (Tstruct _Node noattr))) ::
               (_t'2, (tptr (Tstruct _Node noattr))) ::
               (_t'1, (tptr (Tstruct _Node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Ederef (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
          (Tstruct _TreeClock noattr)) _tree (tptr (Tstruct _Node noattr))))
    (Sset _par_node
      (Ebinop Oadd (Etempvar _t'2 (tptr (Tstruct _Node noattr)))
        (Etempvar _par tint) (tptr (Tstruct _Node noattr)))))
  (Ssequence
    (Sset _head_child
      (Efield
        (Ederef (Etempvar _par_node (tptr (Tstruct _Node noattr)))
          (Tstruct _Node noattr)) _node_headch tint))
    (Ssequence
      (Sifthenelse (Ebinop One (Etempvar _head_child tint)
                     (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tint)
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                  (Tstruct _TreeClock noattr)) _tree
                (tptr (Tstruct _Node noattr))))
            (Sset _ndtmp
              (Ebinop Oadd (Etempvar _t'1 (tptr (Tstruct _Node noattr)))
                (Etempvar _head_child tint) (tptr (Tstruct _Node noattr)))))
          (Sassign
            (Efield
              (Ederef (Etempvar _ndtmp (tptr (Tstruct _Node noattr)))
                (Tstruct _Node noattr)) _node_prev tint) (Etempvar _t tint)))
        Sskip)
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _nd (tptr (Tstruct _Node noattr)))
              (Tstruct _Node noattr)) _node_prev tint)
          (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _nd (tptr (Tstruct _Node noattr)))
                (Tstruct _Node noattr)) _node_next tint)
            (Etempvar _head_child tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef (Etempvar _nd (tptr (Tstruct _Node noattr)))
                  (Tstruct _Node noattr)) _node_par tint)
              (Etempvar _par tint))
            (Sassign
              (Efield
                (Ederef (Etempvar _par_node (tptr (Tstruct _Node noattr)))
                  (Tstruct _Node noattr)) _node_headch tint)
              (Etempvar _t tint))))))))
|}.

Definition f_get_updated_nodes_join_chn := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_self, (tptr (Tstruct _TreeClock noattr))) ::
                (_tc, (tptr (Tstruct _TreeClock noattr))) :: (_par, tint) ::
                (_par_clock, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_nd_par, (tptr (Tstruct _Node noattr))) ::
               (_vprime_tid, tint) ::
               (_vprime_clocks, (tptr (Tstruct _Clock noattr))) ::
               (_v_clocks, (tptr (Tstruct _Clock noattr))) ::
               (_v_clock, tint) :: (_nd, (tptr (Tstruct _Node noattr))) ::
               (_t'1, tint) :: (_t'9, (tptr (Tstruct _Node noattr))) ::
               (_t'8, (tptr (Tstruct _Clock noattr))) ::
               (_t'7, (tptr (Tstruct _Clock noattr))) :: (_t'6, tint) ::
               (_t'5, (tptr tint)) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, (tptr (Tstruct _Node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'9
      (Efield
        (Ederef (Etempvar _tc (tptr (Tstruct _TreeClock noattr)))
          (Tstruct _TreeClock noattr)) _tree (tptr (Tstruct _Node noattr))))
    (Sset _nd_par
      (Ebinop Oadd (Etempvar _t'9 (tptr (Tstruct _Node noattr)))
        (Etempvar _par tint) (tptr (Tstruct _Node noattr)))))
  (Ssequence
    (Sset _vprime_tid
      (Efield
        (Ederef (Etempvar _nd_par (tptr (Tstruct _Node noattr)))
          (Tstruct _Node noattr)) _node_headch tint))
    (Swhile
      (Ebinop One (Etempvar _vprime_tid tint)
        (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tint)
      (Ssequence
        (Ssequence
          (Sset _t'8
            (Efield
              (Ederef (Etempvar _tc (tptr (Tstruct _TreeClock noattr)))
                (Tstruct _TreeClock noattr)) _clocks
              (tptr (Tstruct _Clock noattr))))
          (Sset _vprime_clocks
            (Ebinop Oadd (Etempvar _t'8 (tptr (Tstruct _Clock noattr)))
              (Etempvar _vprime_tid tint) (tptr (Tstruct _Clock noattr)))))
        (Ssequence
          (Ssequence
            (Sset _t'7
              (Efield
                (Ederef (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                  (Tstruct _TreeClock noattr)) _clocks
                (tptr (Tstruct _Clock noattr))))
            (Sset _v_clocks
              (Ebinop Oadd (Etempvar _t'7 (tptr (Tstruct _Clock noattr)))
                (Etempvar _vprime_tid tint) (tptr (Tstruct _Clock noattr)))))
          (Ssequence
            (Sset _v_clock
              (Efield
                (Ederef (Etempvar _v_clocks (tptr (Tstruct _Clock noattr)))
                  (Tstruct _Clock noattr)) _clock_clk tint))
            (Ssequence
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef
                      (Etempvar _vprime_clocks (tptr (Tstruct _Clock noattr)))
                      (Tstruct _Clock noattr)) _clock_clk tint))
                (Sifthenelse (Ebinop Olt (Etempvar _v_clock tint)
                               (Etempvar _t'3 tint) tint)
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'6
                          (Efield
                            (Ederef
                              (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                              (Tstruct _TreeClock noattr)) _top tint))
                        (Sset _t'1
                          (Ecast
                            (Ebinop Oadd (Etempvar _t'6 tint)
                              (Econst_int (Int.repr 1) tint) tint) tint)))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                            (Tstruct _TreeClock noattr)) _top tint)
                        (Etempvar _t'1 tint)))
                    (Ssequence
                      (Sset _t'5
                        (Efield
                          (Ederef
                            (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                            (Tstruct _TreeClock noattr)) _S (tptr tint)))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _t'5 (tptr tint))
                            (Etempvar _t'1 tint) (tptr tint)) tint)
                        (Etempvar _vprime_tid tint))))
                  (Ssequence
                    (Sset _t'4
                      (Efield
                        (Ederef
                          (Etempvar _vprime_clocks (tptr (Tstruct _Clock noattr)))
                          (Tstruct _Clock noattr)) _clock_aclk tint))
                    (Sifthenelse (Ebinop Ole (Etempvar _t'4 tint)
                                   (Etempvar _par_clock tint) tint)
                      Sbreak
                      Sskip))))
              (Ssequence
                (Ssequence
                  (Sset _t'2
                    (Efield
                      (Ederef
                        (Etempvar _tc (tptr (Tstruct _TreeClock noattr)))
                        (Tstruct _TreeClock noattr)) _tree
                      (tptr (Tstruct _Node noattr))))
                  (Sset _nd
                    (Ebinop Oadd
                      (Etempvar _t'2 (tptr (Tstruct _Node noattr)))
                      (Etempvar _vprime_tid tint)
                      (tptr (Tstruct _Node noattr)))))
                (Sset _vprime_tid
                  (Efield
                    (Ederef (Etempvar _nd (tptr (Tstruct _Node noattr)))
                      (Tstruct _Node noattr)) _node_next tint))))))))))
|}.

Definition f_join := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_self, (tptr (Tstruct _TreeClock noattr))) ::
                (_tc, (tptr (Tstruct _TreeClock noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_root_tid_this, tint) :: (_zprime_tid, tint) ::
               (_zprime_clocks, (tptr (Tstruct _Clock noattr))) ::
               (_zprime_clock, tint) ::
               (_z_node, (tptr (Tstruct _Node noattr))) ::
               (_z_clocks, (tptr (Tstruct _Clock noattr))) ::
               (_z_clock, tint) ::
               (_self_root_clocks, (tptr (Tstruct _Clock noattr))) ::
               (_uprime_tid, tint) ::
               (_uprime_clocks, (tptr (Tstruct _Clock noattr))) ::
               (_u_node, (tptr (Tstruct _Node noattr))) ::
               (_u_clocks, (tptr (Tstruct _Clock noattr))) ::
               (_u_clock, tint) ::
               (_uprime_node, (tptr (Tstruct _Node noattr))) :: (_y, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'17, tint) :: (_t'16, (tptr (Tstruct _Clock noattr))) ::
               (_t'15, (tptr (Tstruct _Node noattr))) ::
               (_t'14, (tptr (Tstruct _Clock noattr))) ::
               (_t'13, (tptr (Tstruct _Clock noattr))) :: (_t'12, tint) ::
               (_t'11, tint) :: (_t'10, (tptr tint)) ::
               (_t'9, (tptr (Tstruct _Clock noattr))) ::
               (_t'8, (tptr (Tstruct _Node noattr))) ::
               (_t'7, (tptr (Tstruct _Clock noattr))) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, (tptr (Tstruct _Node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _root_tid_this
    (Efield
      (Ederef (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
        (Tstruct _TreeClock noattr)) _root_tid tint))
  (Ssequence
    (Ssequence
      (Sset _t'17
        (Efield
          (Ederef (Etempvar _tc (tptr (Tstruct _TreeClock noattr)))
            (Tstruct _TreeClock noattr)) _root_tid tint))
      (Sifthenelse (Ebinop Oeq (Etempvar _root_tid_this tint)
                     (Etempvar _t'17 tint) tint)
        (Sreturn None)
        Sskip))
    (Ssequence
      (Sset _zprime_tid
        (Efield
          (Ederef (Etempvar _tc (tptr (Tstruct _TreeClock noattr)))
            (Tstruct _TreeClock noattr)) _root_tid tint))
      (Ssequence
        (Ssequence
          (Sset _t'16
            (Efield
              (Ederef (Etempvar _tc (tptr (Tstruct _TreeClock noattr)))
                (Tstruct _TreeClock noattr)) _clocks
              (tptr (Tstruct _Clock noattr))))
          (Sset _zprime_clocks
            (Ebinop Oadd (Etempvar _t'16 (tptr (Tstruct _Clock noattr)))
              (Etempvar _zprime_tid tint) (tptr (Tstruct _Clock noattr)))))
        (Ssequence
          (Sset _zprime_clock
            (Efield
              (Ederef
                (Etempvar _zprime_clocks (tptr (Tstruct _Clock noattr)))
                (Tstruct _Clock noattr)) _clock_clk tint))
          (Ssequence
            (Ssequence
              (Sset _t'15
                (Efield
                  (Ederef (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                    (Tstruct _TreeClock noattr)) _tree
                  (tptr (Tstruct _Node noattr))))
              (Sset _z_node
                (Ebinop Oadd (Etempvar _t'15 (tptr (Tstruct _Node noattr)))
                  (Etempvar _zprime_tid tint) (tptr (Tstruct _Node noattr)))))
            (Ssequence
              (Ssequence
                (Sset _t'14
                  (Efield
                    (Ederef
                      (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                      (Tstruct _TreeClock noattr)) _clocks
                    (tptr (Tstruct _Clock noattr))))
                (Sset _z_clocks
                  (Ebinop Oadd
                    (Etempvar _t'14 (tptr (Tstruct _Clock noattr)))
                    (Etempvar _zprime_tid tint)
                    (tptr (Tstruct _Clock noattr)))))
              (Ssequence
                (Sset _z_clock
                  (Efield
                    (Ederef
                      (Etempvar _z_clocks (tptr (Tstruct _Clock noattr)))
                      (Tstruct _Clock noattr)) _clock_clk tint))
                (Ssequence
                  (Sifthenelse (Ebinop Ole (Etempvar _zprime_clock tint)
                                 (Etempvar _z_clock tint) tint)
                    (Sreturn None)
                    (Ssequence
                      (Scall (Some _t'1)
                        (Evar _node_is_null (Tfunction
                                              (Tcons
                                                (tptr (Tstruct _Node noattr))
                                                Tnil) tint cc_default))
                        ((Etempvar _z_node (tptr (Tstruct _Node noattr))) ::
                         nil))
                      (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
                        (Scall None
                          (Evar _detach_from_neighbors (Tfunction
                                                         (Tcons
                                                           (tptr (Tstruct _TreeClock noattr))
                                                           (Tcons tint
                                                             (Tcons
                                                               (tptr (Tstruct _Node noattr))
                                                               Tnil))) tvoid
                                                         cc_default))
                          ((Etempvar _self (tptr (Tstruct _TreeClock noattr))) ::
                           (Etempvar _zprime_tid tint) ::
                           (Etempvar _z_node (tptr (Tstruct _Node noattr))) ::
                           nil))
                        Sskip)))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _z_clocks (tptr (Tstruct _Clock noattr)))
                          (Tstruct _Clock noattr)) _clock_clk tint)
                      (Etempvar _zprime_clock tint))
                    (Ssequence
                      (Ssequence
                        (Sset _t'13
                          (Efield
                            (Ederef
                              (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                              (Tstruct _TreeClock noattr)) _clocks
                            (tptr (Tstruct _Clock noattr))))
                        (Sset _self_root_clocks
                          (Ebinop Oadd
                            (Etempvar _t'13 (tptr (Tstruct _Clock noattr)))
                            (Etempvar _root_tid_this tint)
                            (tptr (Tstruct _Clock noattr)))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'12
                            (Efield
                              (Ederef
                                (Etempvar _self_root_clocks (tptr (Tstruct _Clock noattr)))
                                (Tstruct _Clock noattr)) _clock_clk tint))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _z_clocks (tptr (Tstruct _Clock noattr)))
                                (Tstruct _Clock noattr)) _clock_aclk tint)
                            (Etempvar _t'12 tint)))
                        (Ssequence
                          (Scall None
                            (Evar _push_child (Tfunction
                                                (Tcons
                                                  (tptr (Tstruct _TreeClock noattr))
                                                  (Tcons tint
                                                    (Tcons tint
                                                      (Tcons
                                                        (tptr (Tstruct _Node noattr))
                                                        Tnil)))) tvoid
                                                cc_default))
                            ((Etempvar _self (tptr (Tstruct _TreeClock noattr))) ::
                             (Etempvar _root_tid_this tint) ::
                             (Etempvar _zprime_tid tint) ::
                             (Etempvar _z_node (tptr (Tstruct _Node noattr))) ::
                             nil))
                          (Ssequence
                            (Scall None
                              (Evar _get_updated_nodes_join_chn (Tfunction
                                                                  (Tcons
                                                                    (tptr (Tstruct _TreeClock noattr))
                                                                    (Tcons
                                                                    (tptr (Tstruct _TreeClock noattr))
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tint
                                                                    Tnil))))
                                                                  tvoid
                                                                  cc_default))
                              ((Etempvar _self (tptr (Tstruct _TreeClock noattr))) ::
                               (Etempvar _tc (tptr (Tstruct _TreeClock noattr))) ::
                               (Etempvar _zprime_tid tint) ::
                               (Etempvar _z_clock tint) :: nil))
                            (Sloop
                              (Ssequence
                                (Ssequence
                                  (Sset _t'11
                                    (Efield
                                      (Ederef
                                        (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                                        (Tstruct _TreeClock noattr)) _top
                                      tint))
                                  (Sifthenelse (Ebinop Oge
                                                 (Etempvar _t'11 tint)
                                                 (Econst_int (Int.repr 0) tint)
                                                 tint)
                                    Sskip
                                    Sbreak))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'2
                                        (Efield
                                          (Ederef
                                            (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                                            (Tstruct _TreeClock noattr)) _top
                                          tint))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                                            (Tstruct _TreeClock noattr)) _top
                                          tint)
                                        (Ebinop Osub (Etempvar _t'2 tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint)))
                                    (Ssequence
                                      (Sset _t'10
                                        (Efield
                                          (Ederef
                                            (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                                            (Tstruct _TreeClock noattr)) _S
                                          (tptr tint)))
                                      (Sset _uprime_tid
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'10 (tptr tint))
                                            (Etempvar _t'2 tint) (tptr tint))
                                          tint))))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'9
                                        (Efield
                                          (Ederef
                                            (Etempvar _tc (tptr (Tstruct _TreeClock noattr)))
                                            (Tstruct _TreeClock noattr))
                                          _clocks
                                          (tptr (Tstruct _Clock noattr))))
                                      (Sset _uprime_clocks
                                        (Ebinop Oadd
                                          (Etempvar _t'9 (tptr (Tstruct _Clock noattr)))
                                          (Etempvar _uprime_tid tint)
                                          (tptr (Tstruct _Clock noattr)))))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'8
                                          (Efield
                                            (Ederef
                                              (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                                              (Tstruct _TreeClock noattr))
                                            _tree
                                            (tptr (Tstruct _Node noattr))))
                                        (Sset _u_node
                                          (Ebinop Oadd
                                            (Etempvar _t'8 (tptr (Tstruct _Node noattr)))
                                            (Etempvar _uprime_tid tint)
                                            (tptr (Tstruct _Node noattr)))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'7
                                            (Efield
                                              (Ederef
                                                (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                                                (Tstruct _TreeClock noattr))
                                              _clocks
                                              (tptr (Tstruct _Clock noattr))))
                                          (Sset _u_clocks
                                            (Ebinop Oadd
                                              (Etempvar _t'7 (tptr (Tstruct _Clock noattr)))
                                              (Etempvar _uprime_tid tint)
                                              (tptr (Tstruct _Clock noattr)))))
                                        (Ssequence
                                          (Sset _u_clock
                                            (Efield
                                              (Ederef
                                                (Etempvar _u_clocks (tptr (Tstruct _Clock noattr)))
                                                (Tstruct _Clock noattr))
                                              _clock_clk tint))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'3)
                                                (Evar _node_is_null (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _Node noattr))
                                                                    Tnil)
                                                                    tint
                                                                    cc_default))
                                                ((Etempvar _u_node (tptr (Tstruct _Node noattr))) ::
                                                 nil))
                                              (Sifthenelse (Eunop Onotbool
                                                             (Etempvar _t'3 tint)
                                                             tint)
                                                (Scall None
                                                  (Evar _detach_from_neighbors 
                                                  (Tfunction
                                                    (Tcons
                                                      (tptr (Tstruct _TreeClock noattr))
                                                      (Tcons tint
                                                        (Tcons
                                                          (tptr (Tstruct _Node noattr))
                                                          Tnil))) tvoid
                                                    cc_default))
                                                  ((Etempvar _self (tptr (Tstruct _TreeClock noattr))) ::
                                                   (Etempvar _uprime_tid tint) ::
                                                   (Etempvar _u_node (tptr (Tstruct _Node noattr))) ::
                                                   nil))
                                                Sskip))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'6
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _uprime_clocks (tptr (Tstruct _Clock noattr)))
                                                      (Tstruct _Clock noattr))
                                                    _clock_clk tint))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _u_clocks (tptr (Tstruct _Clock noattr)))
                                                      (Tstruct _Clock noattr))
                                                    _clock_clk tint)
                                                  (Etempvar _t'6 tint)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'5
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _uprime_clocks (tptr (Tstruct _Clock noattr)))
                                                        (Tstruct _Clock noattr))
                                                      _clock_aclk tint))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _u_clocks (tptr (Tstruct _Clock noattr)))
                                                        (Tstruct _Clock noattr))
                                                      _clock_aclk tint)
                                                    (Etempvar _t'5 tint)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'4
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _tc (tptr (Tstruct _TreeClock noattr)))
                                                          (Tstruct _TreeClock noattr))
                                                        _tree
                                                        (tptr (Tstruct _Node noattr))))
                                                    (Sset _uprime_node
                                                      (Ebinop Oadd
                                                        (Etempvar _t'4 (tptr (Tstruct _Node noattr)))
                                                        (Etempvar _uprime_tid tint)
                                                        (tptr (Tstruct _Node noattr)))))
                                                  (Ssequence
                                                    (Sset _y
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _uprime_node (tptr (Tstruct _Node noattr)))
                                                          (Tstruct _Node noattr))
                                                        _node_par tint))
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _push_child 
                                                        (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _TreeClock noattr))
                                                            (Tcons tint
                                                              (Tcons tint
                                                                (Tcons
                                                                  (tptr (Tstruct _Node noattr))
                                                                  Tnil))))
                                                          tvoid cc_default))
                                                        ((Etempvar _self (tptr (Tstruct _TreeClock noattr))) ::
                                                         (Etempvar _y tint) ::
                                                         (Etempvar _uprime_tid tint) ::
                                                         (Etempvar _u_node (tptr (Tstruct _Node noattr))) ::
                                                         nil))
                                                      (Scall None
                                                        (Evar _get_updated_nodes_join_chn 
                                                        (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _TreeClock noattr))
                                                            (Tcons
                                                              (tptr (Tstruct _TreeClock noattr))
                                                              (Tcons tint
                                                                (Tcons tint
                                                                  Tnil))))
                                                          tvoid cc_default))
                                                        ((Etempvar _self (tptr (Tstruct _TreeClock noattr))) ::
                                                         (Etempvar _tc (tptr (Tstruct _TreeClock noattr))) ::
                                                         (Etempvar _uprime_tid tint) ::
                                                         (Etempvar _u_clock tint) ::
                                                         nil))))))))))))))
                              Sskip)))))))))))))))
|}.

Definition f_get_updated_nodes_copy_chn := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_self, (tptr (Tstruct _TreeClock noattr))) ::
                (_tc, (tptr (Tstruct _TreeClock noattr))) :: (_par, tint) ::
                (_par_clock, tint) :: (_targ, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_nd_par, (tptr (Tstruct _Node noattr))) ::
               (_vprime_tid, tint) ::
               (_vprime_clocks, (tptr (Tstruct _Clock noattr))) ::
               (_v_clocks, (tptr (Tstruct _Clock noattr))) ::
               (_v_clock, tint) :: (_nd, (tptr (Tstruct _Node noattr))) ::
               (_t'2, tint) :: (_t'1, tint) ::
               (_t'12, (tptr (Tstruct _Node noattr))) ::
               (_t'11, (tptr (Tstruct _Clock noattr))) ::
               (_t'10, (tptr (Tstruct _Clock noattr))) :: (_t'9, tint) ::
               (_t'8, (tptr tint)) :: (_t'7, tint) :: (_t'6, (tptr tint)) ::
               (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, (tptr (Tstruct _Node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'12
      (Efield
        (Ederef (Etempvar _tc (tptr (Tstruct _TreeClock noattr)))
          (Tstruct _TreeClock noattr)) _tree (tptr (Tstruct _Node noattr))))
    (Sset _nd_par
      (Ebinop Oadd (Etempvar _t'12 (tptr (Tstruct _Node noattr)))
        (Etempvar _par tint) (tptr (Tstruct _Node noattr)))))
  (Ssequence
    (Sset _vprime_tid
      (Efield
        (Ederef (Etempvar _nd_par (tptr (Tstruct _Node noattr)))
          (Tstruct _Node noattr)) _node_headch tint))
    (Swhile
      (Ebinop One (Etempvar _vprime_tid tint)
        (Eunop Oneg (Econst_int (Int.repr 1) tint) tint) tint)
      (Ssequence
        (Ssequence
          (Sset _t'11
            (Efield
              (Ederef (Etempvar _tc (tptr (Tstruct _TreeClock noattr)))
                (Tstruct _TreeClock noattr)) _clocks
              (tptr (Tstruct _Clock noattr))))
          (Sset _vprime_clocks
            (Ebinop Oadd (Etempvar _t'11 (tptr (Tstruct _Clock noattr)))
              (Etempvar _vprime_tid tint) (tptr (Tstruct _Clock noattr)))))
        (Ssequence
          (Ssequence
            (Sset _t'10
              (Efield
                (Ederef (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                  (Tstruct _TreeClock noattr)) _clocks
                (tptr (Tstruct _Clock noattr))))
            (Sset _v_clocks
              (Ebinop Oadd (Etempvar _t'10 (tptr (Tstruct _Clock noattr)))
                (Etempvar _vprime_tid tint) (tptr (Tstruct _Clock noattr)))))
          (Ssequence
            (Sset _v_clock
              (Efield
                (Ederef (Etempvar _v_clocks (tptr (Tstruct _Clock noattr)))
                  (Tstruct _Clock noattr)) _clock_clk tint))
            (Ssequence
              (Ssequence
                (Sset _t'4
                  (Efield
                    (Ederef
                      (Etempvar _vprime_clocks (tptr (Tstruct _Clock noattr)))
                      (Tstruct _Clock noattr)) _clock_clk tint))
                (Sifthenelse (Ebinop Olt (Etempvar _v_clock tint)
                               (Etempvar _t'4 tint) tint)
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'9
                          (Efield
                            (Ederef
                              (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                              (Tstruct _TreeClock noattr)) _top tint))
                        (Sset _t'1
                          (Ecast
                            (Ebinop Oadd (Etempvar _t'9 tint)
                              (Econst_int (Int.repr 1) tint) tint) tint)))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                            (Tstruct _TreeClock noattr)) _top tint)
                        (Etempvar _t'1 tint)))
                    (Ssequence
                      (Sset _t'8
                        (Efield
                          (Ederef
                            (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                            (Tstruct _TreeClock noattr)) _S (tptr tint)))
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Etempvar _t'8 (tptr tint))
                            (Etempvar _t'1 tint) (tptr tint)) tint)
                        (Etempvar _vprime_tid tint))))
                  (Sifthenelse (Ebinop Oeq (Etempvar _vprime_tid tint)
                                 (Etempvar _targ tint) tint)
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'7
                            (Efield
                              (Ederef
                                (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                                (Tstruct _TreeClock noattr)) _top tint))
                          (Sset _t'2
                            (Ecast
                              (Ebinop Oadd (Etempvar _t'7 tint)
                                (Econst_int (Int.repr 1) tint) tint) tint)))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                              (Tstruct _TreeClock noattr)) _top tint)
                          (Etempvar _t'2 tint)))
                      (Ssequence
                        (Sset _t'6
                          (Efield
                            (Ederef
                              (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                              (Tstruct _TreeClock noattr)) _S (tptr tint)))
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Etempvar _t'6 (tptr tint))
                              (Etempvar _t'2 tint) (tptr tint)) tint)
                          (Etempvar _vprime_tid tint))))
                    (Ssequence
                      (Sset _t'5
                        (Efield
                          (Ederef
                            (Etempvar _vprime_clocks (tptr (Tstruct _Clock noattr)))
                            (Tstruct _Clock noattr)) _clock_aclk tint))
                      (Sifthenelse (Ebinop Ole (Etempvar _t'5 tint)
                                     (Etempvar _par_clock tint) tint)
                        Sbreak
                        Sskip)))))
              (Ssequence
                (Ssequence
                  (Sset _t'3
                    (Efield
                      (Ederef
                        (Etempvar _tc (tptr (Tstruct _TreeClock noattr)))
                        (Tstruct _TreeClock noattr)) _tree
                      (tptr (Tstruct _Node noattr))))
                  (Sset _nd
                    (Ebinop Oadd
                      (Etempvar _t'3 (tptr (Tstruct _Node noattr)))
                      (Etempvar _vprime_tid tint)
                      (tptr (Tstruct _Node noattr)))))
                (Sset _vprime_tid
                  (Efield
                    (Ederef (Etempvar _nd (tptr (Tstruct _Node noattr)))
                      (Tstruct _Node noattr)) _node_next tint))))))))))
|}.

Definition f_monotone_copy := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_self, (tptr (Tstruct _TreeClock noattr))) ::
                (_tc, (tptr (Tstruct _TreeClock noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_root_tid_this, tint) :: (_zprime_tid, tint) ::
               (_zprime_clocks, (tptr (Tstruct _Clock noattr))) ::
               (_z_node, (tptr (Tstruct _Node noattr))) ::
               (_z_clocks, (tptr (Tstruct _Clock noattr))) ::
               (_z_clock, tint) :: (_uprime_tid, tint) ::
               (_uprime_clocks, (tptr (Tstruct _Clock noattr))) ::
               (_u_node, (tptr (Tstruct _Node noattr))) ::
               (_u_clocks, (tptr (Tstruct _Clock noattr))) ::
               (_u_clock, tint) ::
               (_uprime_node, (tptr (Tstruct _Node noattr))) :: (_y, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'16, (tptr (Tstruct _Clock noattr))) ::
               (_t'15, (tptr (Tstruct _Node noattr))) ::
               (_t'14, (tptr (Tstruct _Clock noattr))) :: (_t'13, tint) ::
               (_t'12, tint) :: (_t'11, tint) :: (_t'10, (tptr tint)) ::
               (_t'9, (tptr (Tstruct _Clock noattr))) ::
               (_t'8, (tptr (Tstruct _Node noattr))) ::
               (_t'7, (tptr (Tstruct _Clock noattr))) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, (tptr (Tstruct _Node noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _root_tid_this
    (Efield
      (Ederef (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
        (Tstruct _TreeClock noattr)) _root_tid tint))
  (Ssequence
    (Sset _zprime_tid
      (Efield
        (Ederef (Etempvar _tc (tptr (Tstruct _TreeClock noattr)))
          (Tstruct _TreeClock noattr)) _root_tid tint))
    (Ssequence
      (Ssequence
        (Sset _t'16
          (Efield
            (Ederef (Etempvar _tc (tptr (Tstruct _TreeClock noattr)))
              (Tstruct _TreeClock noattr)) _clocks
            (tptr (Tstruct _Clock noattr))))
        (Sset _zprime_clocks
          (Ebinop Oadd (Etempvar _t'16 (tptr (Tstruct _Clock noattr)))
            (Etempvar _zprime_tid tint) (tptr (Tstruct _Clock noattr)))))
      (Ssequence
        (Ssequence
          (Sset _t'15
            (Efield
              (Ederef (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                (Tstruct _TreeClock noattr)) _tree
              (tptr (Tstruct _Node noattr))))
          (Sset _z_node
            (Ebinop Oadd (Etempvar _t'15 (tptr (Tstruct _Node noattr)))
              (Etempvar _zprime_tid tint) (tptr (Tstruct _Node noattr)))))
        (Ssequence
          (Ssequence
            (Sset _t'14
              (Efield
                (Ederef (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                  (Tstruct _TreeClock noattr)) _clocks
                (tptr (Tstruct _Clock noattr))))
            (Sset _z_clocks
              (Ebinop Oadd (Etempvar _t'14 (tptr (Tstruct _Clock noattr)))
                (Etempvar _zprime_tid tint) (tptr (Tstruct _Clock noattr)))))
          (Ssequence
            (Sset _z_clock
              (Efield
                (Ederef (Etempvar _z_clocks (tptr (Tstruct _Clock noattr)))
                  (Tstruct _Clock noattr)) _clock_clk tint))
            (Ssequence
              (Ssequence
                (Scall (Some _t'1)
                  (Evar _node_is_null (Tfunction
                                        (Tcons (tptr (Tstruct _Node noattr))
                                          Tnil) tint cc_default))
                  ((Etempvar _z_node (tptr (Tstruct _Node noattr))) :: nil))
                (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
                  (Sifthenelse (Ebinop One (Etempvar _zprime_tid tint)
                                 (Etempvar _root_tid_this tint) tint)
                    (Scall None
                      (Evar _detach_from_neighbors (Tfunction
                                                     (Tcons
                                                       (tptr (Tstruct _TreeClock noattr))
                                                       (Tcons tint
                                                         (Tcons
                                                           (tptr (Tstruct _Node noattr))
                                                           Tnil))) tvoid
                                                     cc_default))
                      ((Etempvar _self (tptr (Tstruct _TreeClock noattr))) ::
                       (Etempvar _zprime_tid tint) ::
                       (Etempvar _z_node (tptr (Tstruct _Node noattr))) ::
                       nil))
                    Sskip)
                  Sskip))
              (Ssequence
                (Ssequence
                  (Sset _t'13
                    (Efield
                      (Ederef
                        (Etempvar _zprime_clocks (tptr (Tstruct _Clock noattr)))
                        (Tstruct _Clock noattr)) _clock_clk tint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _z_clocks (tptr (Tstruct _Clock noattr)))
                        (Tstruct _Clock noattr)) _clock_clk tint)
                    (Etempvar _t'13 tint)))
                (Ssequence
                  (Ssequence
                    (Sset _t'12
                      (Efield
                        (Ederef
                          (Etempvar _zprime_clocks (tptr (Tstruct _Clock noattr)))
                          (Tstruct _Clock noattr)) _clock_aclk tint))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _z_clocks (tptr (Tstruct _Clock noattr)))
                          (Tstruct _Clock noattr)) _clock_aclk tint)
                      (Etempvar _t'12 tint)))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _z_node (tptr (Tstruct _Node noattr)))
                          (Tstruct _Node noattr)) _node_par tint)
                      (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _z_node (tptr (Tstruct _Node noattr)))
                            (Tstruct _Node noattr)) _node_prev tint)
                        (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _z_node (tptr (Tstruct _Node noattr)))
                              (Tstruct _Node noattr)) _node_next tint)
                          (Eunop Oneg (Econst_int (Int.repr 1) tint) tint))
                        (Ssequence
                          (Scall None
                            (Evar _get_updated_nodes_copy_chn (Tfunction
                                                                (Tcons
                                                                  (tptr (Tstruct _TreeClock noattr))
                                                                  (Tcons
                                                                    (tptr (Tstruct _TreeClock noattr))
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tint
                                                                    (Tcons
                                                                    tint
                                                                    Tnil)))))
                                                                tvoid
                                                                cc_default))
                            ((Etempvar _self (tptr (Tstruct _TreeClock noattr))) ::
                             (Etempvar _tc (tptr (Tstruct _TreeClock noattr))) ::
                             (Etempvar _zprime_tid tint) ::
                             (Etempvar _z_clock tint) ::
                             (Etempvar _root_tid_this tint) :: nil))
                          (Ssequence
                            (Sloop
                              (Ssequence
                                (Ssequence
                                  (Sset _t'11
                                    (Efield
                                      (Ederef
                                        (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                                        (Tstruct _TreeClock noattr)) _top
                                      tint))
                                  (Sifthenelse (Ebinop Oge
                                                 (Etempvar _t'11 tint)
                                                 (Econst_int (Int.repr 0) tint)
                                                 tint)
                                    Sskip
                                    Sbreak))
                                (Ssequence
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'2
                                        (Efield
                                          (Ederef
                                            (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                                            (Tstruct _TreeClock noattr)) _top
                                          tint))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                                            (Tstruct _TreeClock noattr)) _top
                                          tint)
                                        (Ebinop Osub (Etempvar _t'2 tint)
                                          (Econst_int (Int.repr 1) tint)
                                          tint)))
                                    (Ssequence
                                      (Sset _t'10
                                        (Efield
                                          (Ederef
                                            (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                                            (Tstruct _TreeClock noattr)) _S
                                          (tptr tint)))
                                      (Sset _uprime_tid
                                        (Ederef
                                          (Ebinop Oadd
                                            (Etempvar _t'10 (tptr tint))
                                            (Etempvar _t'2 tint) (tptr tint))
                                          tint))))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'9
                                        (Efield
                                          (Ederef
                                            (Etempvar _tc (tptr (Tstruct _TreeClock noattr)))
                                            (Tstruct _TreeClock noattr))
                                          _clocks
                                          (tptr (Tstruct _Clock noattr))))
                                      (Sset _uprime_clocks
                                        (Ebinop Oadd
                                          (Etempvar _t'9 (tptr (Tstruct _Clock noattr)))
                                          (Etempvar _uprime_tid tint)
                                          (tptr (Tstruct _Clock noattr)))))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'8
                                          (Efield
                                            (Ederef
                                              (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                                              (Tstruct _TreeClock noattr))
                                            _tree
                                            (tptr (Tstruct _Node noattr))))
                                        (Sset _u_node
                                          (Ebinop Oadd
                                            (Etempvar _t'8 (tptr (Tstruct _Node noattr)))
                                            (Etempvar _uprime_tid tint)
                                            (tptr (Tstruct _Node noattr)))))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'7
                                            (Efield
                                              (Ederef
                                                (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                                                (Tstruct _TreeClock noattr))
                                              _clocks
                                              (tptr (Tstruct _Clock noattr))))
                                          (Sset _u_clocks
                                            (Ebinop Oadd
                                              (Etempvar _t'7 (tptr (Tstruct _Clock noattr)))
                                              (Etempvar _uprime_tid tint)
                                              (tptr (Tstruct _Clock noattr)))))
                                        (Ssequence
                                          (Sset _u_clock
                                            (Efield
                                              (Ederef
                                                (Etempvar _u_clocks (tptr (Tstruct _Clock noattr)))
                                                (Tstruct _Clock noattr))
                                              _clock_clk tint))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'3)
                                                (Evar _node_is_null (Tfunction
                                                                    (Tcons
                                                                    (tptr (Tstruct _Node noattr))
                                                                    Tnil)
                                                                    tint
                                                                    cc_default))
                                                ((Etempvar _u_node (tptr (Tstruct _Node noattr))) ::
                                                 nil))
                                              (Sifthenelse (Eunop Onotbool
                                                             (Etempvar _t'3 tint)
                                                             tint)
                                                (Sifthenelse (Ebinop One
                                                               (Etempvar _uprime_tid tint)
                                                               (Etempvar _root_tid_this tint)
                                                               tint)
                                                  (Scall None
                                                    (Evar _detach_from_neighbors 
                                                    (Tfunction
                                                      (Tcons
                                                        (tptr (Tstruct _TreeClock noattr))
                                                        (Tcons tint
                                                          (Tcons
                                                            (tptr (Tstruct _Node noattr))
                                                            Tnil))) tvoid
                                                      cc_default))
                                                    ((Etempvar _self (tptr (Tstruct _TreeClock noattr))) ::
                                                     (Etempvar _uprime_tid tint) ::
                                                     (Etempvar _u_node (tptr (Tstruct _Node noattr))) ::
                                                     nil))
                                                  Sskip)
                                                Sskip))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'6
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _uprime_clocks (tptr (Tstruct _Clock noattr)))
                                                      (Tstruct _Clock noattr))
                                                    _clock_clk tint))
                                                (Sassign
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _u_clocks (tptr (Tstruct _Clock noattr)))
                                                      (Tstruct _Clock noattr))
                                                    _clock_clk tint)
                                                  (Etempvar _t'6 tint)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'5
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _uprime_clocks (tptr (Tstruct _Clock noattr)))
                                                        (Tstruct _Clock noattr))
                                                      _clock_aclk tint))
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _u_clocks (tptr (Tstruct _Clock noattr)))
                                                        (Tstruct _Clock noattr))
                                                      _clock_aclk tint)
                                                    (Etempvar _t'5 tint)))
                                                (Ssequence
                                                  (Ssequence
                                                    (Sset _t'4
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _tc (tptr (Tstruct _TreeClock noattr)))
                                                          (Tstruct _TreeClock noattr))
                                                        _tree
                                                        (tptr (Tstruct _Node noattr))))
                                                    (Sset _uprime_node
                                                      (Ebinop Oadd
                                                        (Etempvar _t'4 (tptr (Tstruct _Node noattr)))
                                                        (Etempvar _uprime_tid tint)
                                                        (tptr (Tstruct _Node noattr)))))
                                                  (Ssequence
                                                    (Sset _y
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _uprime_node (tptr (Tstruct _Node noattr)))
                                                          (Tstruct _Node noattr))
                                                        _node_par tint))
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _push_child 
                                                        (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _TreeClock noattr))
                                                            (Tcons tint
                                                              (Tcons tint
                                                                (Tcons
                                                                  (tptr (Tstruct _Node noattr))
                                                                  Tnil))))
                                                          tvoid cc_default))
                                                        ((Etempvar _self (tptr (Tstruct _TreeClock noattr))) ::
                                                         (Etempvar _y tint) ::
                                                         (Etempvar _uprime_tid tint) ::
                                                         (Etempvar _u_node (tptr (Tstruct _Node noattr))) ::
                                                         nil))
                                                      (Scall None
                                                        (Evar _get_updated_nodes_copy_chn 
                                                        (Tfunction
                                                          (Tcons
                                                            (tptr (Tstruct _TreeClock noattr))
                                                            (Tcons
                                                              (tptr (Tstruct _TreeClock noattr))
                                                              (Tcons tint
                                                                (Tcons tint
                                                                  (Tcons tint
                                                                    Tnil)))))
                                                          tvoid cc_default))
                                                        ((Etempvar _self (tptr (Tstruct _TreeClock noattr))) ::
                                                         (Etempvar _tc (tptr (Tstruct _TreeClock noattr))) ::
                                                         (Etempvar _uprime_tid tint) ::
                                                         (Etempvar _u_clock tint) ::
                                                         (Etempvar _root_tid_this tint) ::
                                                         nil))))))))))))))
                              Sskip)
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _self (tptr (Tstruct _TreeClock noattr)))
                                  (Tstruct _TreeClock noattr)) _root_tid
                                tint) (Etempvar _zprime_tid tint))))))))))))))))
|}.

Definition composites : list composite_definition :=
(Composite _Node Struct
   (Member_plain _node_next tint :: Member_plain _node_prev tint ::
    Member_plain _node_par tint :: Member_plain _node_headch tint :: nil)
   noattr ::
 Composite _Clock Struct
   (Member_plain _clock_clk tint :: Member_plain _clock_aclk tint :: nil)
   noattr ::
 Composite _TreeClock Struct
   (Member_plain _dim tint :: Member_plain _root_tid tint ::
    Member_plain _clocks (tptr (Tstruct _Clock noattr)) ::
    Member_plain _tree (tptr (Tstruct _Node noattr)) ::
    Member_plain _S (tptr tint) :: Member_plain _top tint :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons (tptr tvoid) Tnil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons (tptr tvoid) Tnil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons (tptr tvoid) Tnil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons (tptr tvoid) (Tcons tulong Tnil))
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Tfloat :: nil) AST.Tlong cc_default))
     (Tcons tdouble Tnil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tlong Tnil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Tlong :: nil) AST.Tfloat cc_default))
     (Tcons tulong Tnil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tlong Tnil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Tlong :: nil) AST.Tsingle cc_default))
     (Tcons tulong Tnil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tint Tnil)) tulong
     cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tint Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tulong (Tcons tulong Tnil)) tulong
     cc_default)) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Tlong :: nil) AST.Tlong cc_default))
     (Tcons tulong Tnil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Tint :: nil) AST.Tint16unsigned
                     cc_default)) (Tcons tushort Tnil) tushort cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tuint Tnil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tulong Tnil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Tsingle :: nil) AST.Tsingle cc_default))
     (Tcons tfloat Tnil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Tfloat :: nil) AST.Tfloat cc_default))
     (Tcons tdouble Tnil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Tlong :: AST.Tlong :: AST.Tlong :: AST.Tlong ::
                      nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid)
       (Tcons (tptr tvoid) (Tcons tulong (Tcons tulong Tnil)))) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tbool Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons (tptr tschar) Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tint
                     cc_default)) (Tcons (tptr tschar) (Tcons tint Tnil))
     tint cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Tlong :: AST.Tint :: nil) AST.Tvoid
                     cc_default)) (Tcons (tptr tvoid) (Tcons tuint Tnil))
     tvoid cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tvoid
                     cc_default))
     (Tcons (tptr tvoid) (Tcons (tptr tvoid) Tnil)) tvoid cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Tlong :: nil) AST.Tvoid cc_default))
     (Tcons (tptr tvoid) Tnil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Tlong :: AST.Tlong :: nil) AST.Tlong
                     cc_default)) (Tcons tlong (Tcons tlong Tnil)) tlong
     cc_default)) ::
 (___builtin_fence,
   Gfun(External (EF_builtin "__builtin_fence"
                   (mksignature nil AST.Tvoid cc_default)) Tnil tvoid
     cc_default)) ::
 (___builtin_cls,
   Gfun(External (EF_builtin "__builtin_cls"
                   (mksignature (AST.Tint :: nil) AST.Tint cc_default))
     (Tcons tint Tnil) tint cc_default)) ::
 (___builtin_clsl,
   Gfun(External (EF_builtin "__builtin_clsl"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tlong Tnil) tint cc_default)) ::
 (___builtin_clsll,
   Gfun(External (EF_builtin "__builtin_clsll"
                   (mksignature (AST.Tlong :: nil) AST.Tint cc_default))
     (Tcons tlong Tnil) tint cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Tfloat :: AST.Tfloat :: AST.Tfloat :: nil)
                     AST.Tfloat cc_default))
     (Tcons tdouble (Tcons tdouble (Tcons tdouble Tnil))) tdouble
     cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Tfloat :: AST.Tfloat :: nil) AST.Tfloat
                     cc_default)) (Tcons tdouble (Tcons tdouble Tnil))
     tdouble cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Tint :: nil) AST.Tvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (Tcons tint Tnil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_malloc,
   Gfun(External EF_malloc (Tcons tulong Tnil) (tptr tvoid) cc_default)) ::
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Tlong :: AST.Tint :: AST.Tlong :: nil)
                     AST.Tlong cc_default))
     (Tcons (tptr tvoid) (Tcons tint (Tcons tulong Tnil))) (tptr tvoid)
     cc_default)) :: (_node_is_null, Gfun(Internal f_node_is_null)) ::
 (_tree_clock_init, Gfun(Internal f_tree_clock_init)) ::
 (_increment_clock, Gfun(Internal f_increment_clock)) ::
 (_write_clock, Gfun(Internal f_write_clock)) ::
 (_read_clock, Gfun(Internal f_read_clock)) ::
 (_is_less_than_or_equal, Gfun(Internal f_is_less_than_or_equal)) ::
 (_detach_from_neighbors, Gfun(Internal f_detach_from_neighbors)) ::
 (_push_child, Gfun(Internal f_push_child)) ::
 (_get_updated_nodes_join_chn, Gfun(Internal f_get_updated_nodes_join_chn)) ::
 (_join, Gfun(Internal f_join)) ::
 (_get_updated_nodes_copy_chn, Gfun(Internal f_get_updated_nodes_copy_chn)) ::
 (_monotone_copy, Gfun(Internal f_monotone_copy)) :: nil).

Definition public_idents : list ident :=
(_monotone_copy :: _get_updated_nodes_copy_chn :: _join ::
 _get_updated_nodes_join_chn :: _push_child :: _detach_from_neighbors ::
 _is_less_than_or_equal :: _read_clock :: _write_clock :: _increment_clock ::
 _tree_clock_init :: _node_is_null :: _memset :: _malloc ::
 ___builtin_debug :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_clsll :: ___builtin_clsl :: ___builtin_cls ::
 ___builtin_fence :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.



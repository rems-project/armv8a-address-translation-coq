Require Import aarch64_types aarch64.
Require Import ZArith Sail.Prompt_monad Sail.Prompt bbv.Word Sail.Real Sail.Values.

Local Open Scope Z.

(*
(*<*)
(* Author: Thomas Bauereiss *)
theory Address_Translation_Orig
  imports "Sail-AArch64.Aarch64_lemmas"
begin
(*>*)

section \<open>Critical parts of original definition\<close>

text \<open>We copy a few parts of the translation table walk function in the original model,
in particular the table walk loop, into individual definitions in order to reason about them
separately.  Note that this just serves to make it easier to state some of the auxiliary
lemmas; the main proof refers only to the original model.\<close>
*)

Ltac remove_binders t :=
  let rec aux t :=
  lazymatch t with
  | (fun (x : ?T) => @?X x) =>
    let t' :=
      constr:(fun (x : T) =>
        ltac:(let t := eval cbv beta in (X x) in
              let r := (aux t) in
              exact r))
    in lazymatch t' with
    | (fun _ => ?X) => X
    | _ => t'
    end
  | ?X => X
  end in
  aux t.
(*
From Ltac2 Require Ltac2 Std Message.

Section loopbodydef.
Set Default Proof Mode "Classic".
Import Std.
Ltac2 fixdeltafn x := { rBeta := false; rMatch := false; rFix := true; rCofix := false; rZeta := false; rDelta := true; rConst := [x] }.
Ltac2 betafl := { rBeta := true; rMatch := false; rFix := false; rCofix := false; rZeta := false; rDelta := false; rConst := [] }.

(* cbn is good for fixpoints, terrible for lone definitions *)
Ltac2 loop_body fn appliedfn :=
  let fnbody := eval_cbn (fixdeltafn fn) appliedfn in
(*  let fnbody := eval hnf in fnbody in  TODO: hnf is too much *)
  let rec aux t :=
    (* TODO somehow try to keep original variable names *)
    (*let x1 := fresh "x1" in
    let x2 := fresh "x2" in*)
    lazy_match! t with
    | context [whileMT ?vars _ _ ?body] => body
    | context [untilMT ?vars _ _ ?body] => body
    | fun _ => ?x => aux x
    | (fun x1 : ?ty => @?x x1) =>
      constr:(fun (x1 : $ty) =>
                ltac2:(let t := eval_cbv betafl '($x &x1) in
                       let r := (aux t) in
                       exact $r))
(*
  | (fix foo (x1 : ?T1) (x2 : ?T2 x1) {struct x2} := @?X x1 x2) =>
      constr:(fun (x1 : T1) (x2 : T2 x1) =>
        ltac:(let t := eval cbv beta in (X x1 x2) in
              let r := (aux t) in
              exact r))*)
    | bind _ _ =>
      match! t with
      | bind ?m _ => aux m
      | bind _ ?f => aux f
      end
    | bind0 _ _ =>
      match! t with
      | bind0 ?m _ => aux m
      | bind0 _ ?m => aux m
      end
    | try_catch _ _ =>
      match! t with
      | try_catch ?m _ => aux m
      | try_catch _ ?h => aux h
      end
    | catch_early_return ?m => aux m
    | liftR ?m => aux m
    | try_catchR _ _ =>
      match! t with
      | try_catchR ?m _ => aux m
      | try_catchR _ ?h => aux h
      end
    | let x1 := _ in @?x x1 =>
      constr:(fun x1 =>
        ltac2:(let t := eval_cbv betafl '($x &x1) in
               let r := (aux t) in
               exact $r))
    | let '(x1, x2) := _ in @?x x1 x2 =>
      constr:(fun x1 x2 =>
        ltac2:(let t := eval_cbv betafl '($x &x1 &x2) in
               let r := (aux t) in
               exact $r))
    | let '(existT _ x1 x2) := _ in @?x x1 x2 =>
      constr:(fun x1 x2 =>
        ltac2:(let t := eval_cbv betafl '($x &x1 &x2) in
               let r := (aux t) in
               exact $r))
    | if ?g then _ else _ =>
      match! t with
      | if _ then ?x else _ => aux x
      | if _ then _ else ?x => aux x
      end
    | match _ with left _ => _ | right _ => _ end =>
      match! t with
      | match _ with left x1 => @?x x1 | right _ => _ end =>
          constr:(fun x1 =>
            ltac2:(let t := eval_cbv betafl '($x &x1) in
                   let r := (aux t) in
                   exact $r))
      | match _ with left _ => _ | right x1 => @?x x1 end =>
          constr:(fun x1 =>
            ltac2:(let t := eval_cbv betafl '($x &x1) in
                   let r := (aux t) in
                   exact $r))
      end
(*    | ?x _ => (*idtac "app" x;*) fail
    | _ =>
      match! t with
      | ?x => is_var x; idtac "var"
      | ?x => let ty := type of x in idtac "mystery term" x "of type" ty
      end*)
    end in
  aux fnbody.

End loopbodydef.
*)
(*
Goal forall (x : Sail.Values.mword 16), True.
  intro x.
  set (tm := _ChooseRandomNonExcludedTag x).
cbn delta [_ChooseRandomNonExcludedTag] in tm.
cbv delta [_ChooseRandomNonExcludedTag] in tm.  
let t := loop_body _ChooseRandomNonExcludedTag (_ChooseRandomNonExcludedTag x) in
idtac t.
Abort.*)
(*Require Import String.
Local Open Scope Z.

Fixpoint test (x1 : Z) (b : bool) (_acc : Acc (Zwf 0) x1) {struct _acc} : M Z
with foo (x : Z) (_acc : Acc (Zwf 0) x) {struct _acc} : M Z.
exact (  assert_exp' (Z.geb x1 0) "bad" >>= fun _ =>
  ((assert_exp (x1 >=? 1) "bad" >>                                      
               let '(a,b,c) := (3,4,5) in
               ((aarch64_extras.undefined_nat tt)) >>= fun '(existT _ w__23 _ : {n : Z & ArithFact (n >= 0)}) =>
  if Sumbool.sumbool_of_bool (2 <=? x1) then
    returnm (1,build_ex 2,3) >>= fun '((y,existT _ z _,w) : Z * {x : Z & ArithFact (x <= x1)} * Z) =>
                        whileMT (x1 + z) (fun x => x) (fun x => returnm (Z.geb x 1)) (fun x => returnm (x - 1 + a - y))
  else returnm 5) : M Z)).
exact (returnm x).
Defined.

Require LoopExtract.

Definition xyz (x : Z) `{ArithFact (x > 5)} := x.
(*Goal forall x : Z, True.
  intros x.
Set Debug Ltac.
  let t := constr:(fun (_: x > 5) => xyz x) in
  let rec f t :=
      lazymatch t with
      | fun (_ : ?T) => ?X => constr:(fun _ : T => ltac:(let t := (f X) in exact t))
      | fun (x : ?T) => @?X x => constr:(fun x : T => ltac:(let t := eval cbv beta in (X x) in let t := (f t) in exact t))
      | _ => constr:(t + 1)
      end in
  let t := f t in
  idtac t.
Abort.*) (*  
  match t with 
  | fun (x : ?T) => @?X x => let t' := constr:(fun x : T => ltac:(let t := eval cbv beta in (X x) in
    match t with 
    | fun (x : ?T) => @?X x => let t' := constr:(fun x : T => ltac:(let t := eval cbv beta in (X x) in exact t)) in exact t'
    end)) in idtac t'
  end.
*)
Goal forall (xx1 : Z) (b:bool) (_acc : Acc (Zwf 0) xx1), True.
  intros xx1 b [_acc].

  let t := ltac2:(LoopExtract.loop_body  reference:(&test) constr:(test xx1 b (Acc_intro xx1 _acc))) in
  set (x := t).

  let t0 := eval cbv delta [x] in x in
  let t := remove_binders t0 in
  idtac t.

Abort.

Definition TranslationTableWalk_loop_body
 (singlepriv : bool) (apply_nvnv1_effect : bool) (hierattrsdisabled : bool) (largegrain : bool)
 (outputsize : Z) (ipaddress : word 52) (reversedescriptors : bool) (s2fs1walk : bool)
 (iswrite : bool) (acctype : AccType) (vaddress : word 64) (secondstage : bool)
 (inputaddr : word 64) (grainsize : Z) (stride : Z)
 : AccessDescriptor * Z * Z * word 2 * word 52 * bool * word 64 * AddressDescriptor *
   AddressDescriptor * bool * Z * word 1 * word 1 * TLBRecord * word 1 ->
   monad register_value (AccessDescriptor *
                                          Z * Z * word 2 *
                                                       word 52 *
                                                       bool *
                                                       word 64 *
                                                       AddressDescriptor *
                                                       AddressDescriptor * bool * Z * word 1 * word 1 * TLBRecord * word 1)
                                          (TLBRecord + exception).
assert (Acc (Zwf 0) 1) as acc.
apply Zwf_guarded.
generalize (Sail.Operators_mwords.vec_of_bits (Sail.Values.B0::nil)). intro s1_nonsecure.
generalize 1. intro size.
destruct acc as [acc].

let t := loop_body  _rec_AArch64_TranslationTableWalk
           (_rec_AArch64_TranslationTableWalk ipaddress s1_nonsecure vaddress acctype iswrite secondstage s2fs1walk size 1 (Acc_intro 1 acc)) in
let t := remove_binders t in
set (body := t).



assert (H1 : (1 >=? 0) = true) by reflexivity.

let t := eval cbv delta [full] in full in
    let t := remove_binders t in
    let t := eval cbv beta in (t H1) in
    match t with
    | context [H1] => idtac "found"
    | _ => idtac "not present"
    end.
idtac t.

let t := loop_body  _rec_AArch64_TranslationTableWalk
           (_rec_AArch64_TranslationTableWalk ipaddress s1_nonsecure vaddress acctype iswrite secondstage s2fs1walk size 1 (Acc_intro 1 acc)) in
let t := remove_binders t in
set (body := t).

(*
Goal True.

let t := loop_body _rec_AArch64_TranslationTableWalk in
idtac t.
*)
Definition TranslationTableWalk_loop_body
 (singlepriv : bool) (apply_nvnv1_effect : bool) (hierattrsdisabled : bool) (largegrain : bool)
 (outputsize : Z) (ipaddress : word 52) (reversedescriptors : bool) (s2fs1walk : bool)
 (iswrite : bool) (acctype : AccType) (vaddress : word 64) (secondstage : bool)
 (inputaddr : word 64) (grainsize : Z) (stride : Z)
 : AccessDescriptor * Z * Z * word 2 * word 52 * bool * word 64 * AddressDescriptor *
   AddressDescriptor * bool * Z * word 1 * word 1 * TLBRecord * word 1 ->
   monad register_value (AccessDescriptor *
                                          Z * Z * word 2 *
                                                       word 52 *
                                                       bool *
                                                       word 64 *
                                                       AddressDescriptor *
                                                       AddressDescriptor * bool * Z * word 1 * word 1 * TLBRecord * word 1)
                                          (TLBRecord + exception).
let t := loop_body _rec_AArch64_TranslationTableWalk in
exact t.
admit.
Admitted.

(*let s1_nonsecure := fresh "s1_nonsecure" in
let size := fresh "size" in
let _reclimit := fresh "_reclimit" in
let _acc := fresh "_acc" in
let s1_nonsecure := constr:(WS false WO) in
let size := constr:(1%Z:Z) in
let _reclimit := constr:(1%Z) in
let _acc := constr:(Zwf_guarded 1) in
let fn := constr:(_rec_AArch64_TranslationTableWalk ipaddress s1_nonsecure vaddress acctype iswrite secondstage s2fs1walk size _reclimit _acc) in
let fnbody := eval simpl in fn in
match fnbody with
| context [untilMT _ _ _ ?body] => exact body
end.
  TranslationTableWalk_loop_body                =
            (\<lambda> varstup . 
            (let (accdesc,
                 addrselectbottom,
                 addrselecttop,
                 ap_table,
                 baseaddress,
                 blocktranslate,
                 desc,
                 descaddr,
                 descaddr2,
                 hwupdatewalk,
                 level,
                 ns_table,
                 pxn_table,
                 result,
                 xn_table) = varstup in
              (let addrselectbottom =
                ((((((( 3 :: int)::ii) - ((ex_int level)))) * ((ex_int stride))))
                  +
                  ((ex_int grainsize))) in
              liftR ((ZeroExtend_slice_append (( 52 :: int)::ii) inputaddr addrselectbottom
                        ((((((ex_int addrselecttop)) - ((ex_int addrselectbottom))))
                            +
                            (( 1 :: int)::ii))) (vec_of_bits [B0,B0,B0]  ::  3 Word.word)
                       :: ( 52 Word.word) M)) \<bind> (\<lambda> (index1 :: 52 bits) . 
              (let (tmp_210 :: FullAddress) = ((AddressDescriptor_paddress   descaddr)) in
              (let tmp_210 =
                ((tmp_210 (|
                  FullAddress_physicaladdress := ((or_vec baseaddress index1  ::  52 Word.word))|))) in
              (let descaddr = ((descaddr (| AddressDescriptor_paddress := tmp_210 |))) in
              (let (tmp_220 :: FullAddress) = ((AddressDescriptor_paddress   descaddr)) in
              (let tmp_220 = ((tmp_220 (| FullAddress_NS := ns_table |))) in
              (let descaddr = ((descaddr (| AddressDescriptor_paddress := tmp_220 |))) in
              or_boolM (return secondstage)
                (liftR (HasS2Translation () ) \<bind> (\<lambda> (w__143 :: bool) .  return ((\<not> w__143)))) \<bind> (\<lambda> (w__144 ::
                bool) . 
              (if w__144 then
                 (let (descaddr2 :: AddressDescriptor) = descaddr in
                 return (descaddr2, hwupdatewalk, result))
               else
                 (let hwupdatewalk = False in
                 liftR (AArch64_SecondStageWalk descaddr vaddress acctype iswrite (( 8 :: int)::ii)
                          hwupdatewalk) \<bind> (\<lambda> (w__145 :: AddressDescriptor) . 
                 (let descaddr2 = w__145 in
                 (if ((IsFault descaddr2)) then
                    (let (tmp_230 :: AddressDescriptor) = ((TLBRecord_addrdesc   result)) in
                    (let tmp_230 =
                      ((tmp_230 (| AddressDescriptor_fault := ((AddressDescriptor_fault   descaddr2))|))) in
                    (let result = ((result (| TLBRecord_addrdesc := tmp_230 |))) in
                    (early_return result :: (unit, TLBRecord) MR) \<then> return result)))
                  else return result) \<bind> (\<lambda> (result :: TLBRecord) . 
                 return (descaddr2, hwupdatewalk, result)))))) \<bind> (\<lambda> varstup .  (let ((descaddr2 ::
                AddressDescriptor), (hwupdatewalk :: bool), (result :: TLBRecord)) = varstup in
              liftR ((ZeroExtend__1 (( 64 :: int)::ii) vaddress  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__146 :: 64 bits) . 
              (let descaddr2 = ((descaddr2 (| AddressDescriptor_vaddress := w__146 |))) in
              liftR (CreateAccessDescriptorPTW acctype secondstage s2fs1walk level) \<bind> (\<lambda> (w__147 ::
                AccessDescriptor) . 
              (let accdesc = w__147 in
              liftR ((aget__Mem descaddr2 (( 8 :: int)::ii) accdesc  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__148 :: 64
                bits) . 
              (let desc = w__148 in
              (if reversedescriptors then liftR ((BigEndianReverse desc  :: ( 64 Word.word) M))
               else return desc) \<bind> (\<lambda> (desc :: 64 bits) . 
              (if (((((((vec_of_bits [access_vec_dec desc (( 0 :: int)::ii)]  ::  1 Word.word) = (vec_of_bits [B0]  ::  1 Word.word)))) \<or> ((((((((slice desc (( 0 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word)) = (vec_of_bits [B0,B1]  ::  2 Word.word)))) \<and> (((((ex_int level)) = (( 3 :: int)::ii))))))))))
               then
                 (let (tmp_240 :: AddressDescriptor) = ((TLBRecord_addrdesc   result)) in
                 liftR (AArch64_TranslationFault ipaddress level acctype iswrite secondstage
                          s2fs1walk) \<bind> (\<lambda> (w__150 :: FaultRecord) . 
                 (let tmp_240 = ((tmp_240 (| AddressDescriptor_fault := w__150 |))) in
                 (let result = ((result (| TLBRecord_addrdesc := tmp_240 |))) in
                 (early_return result :: (unit, TLBRecord) MR) \<then>
                 return (addrselecttop,
                         ap_table,
                         baseaddress,
                         blocktranslate,
                         level,
                         ns_table,
                         pxn_table,
                         result,
                         xn_table)))))
               else if ((((((((slice desc (( 0 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word)) = (vec_of_bits [B0,B1]  ::  2 Word.word)))) \<or> (((((ex_int level)) = (( 3 :: int)::ii)))))))
               then
                 (let (blocktranslate :: bool) = True in
                 return (addrselecttop,
                         ap_table,
                         baseaddress,
                         blocktranslate,
                         level,
                         ns_table,
                         pxn_table,
                         result,
                         xn_table))
               else
                 or_boolM
                   (return ((((((((((ex_int outputsize)) < (( 52 :: int)::ii))) \<and> largegrain))) \<and> ((\<not> ((IsZero ((slice desc (( 12 :: int)::ii) (( 4 :: int)::ii)  ::  4 Word.word))))))))))
                   (and_boolM (return ((((ex_int outputsize)) < (( 48 :: int)::ii))))
                      (liftR (IsZero_slice desc outputsize
                                ((((- ((ex_int outputsize)))) + (( 48 :: int)::ii)))) \<bind> (\<lambda> (w__151 ::
                         bool) . 
                       return ((\<not> w__151))))) \<bind> (\<lambda> (w__153 :: bool) . 
                 if w__153 then
                   (let (tmp_250 :: AddressDescriptor) = ((TLBRecord_addrdesc   result)) in
                   liftR (AArch64_AddressSizeFault ipaddress level acctype iswrite secondstage
                            s2fs1walk) \<bind> (\<lambda> (w__154 :: FaultRecord) . 
                   (let tmp_250 = ((tmp_250 (| AddressDescriptor_fault := w__154 |))) in
                   (let result = ((result (| TLBRecord_addrdesc := tmp_250 |))) in
                   (early_return result :: (unit, TLBRecord) MR) \<then>
                   return (addrselecttop,
                           ap_table,
                           baseaddress,
                           blocktranslate,
                           level,
                           ns_table,
                           pxn_table,
                           result,
                           xn_table)))))
                 else
                   (let gsz = grainsize in
                   liftR (assert_exp True ('''')) \<then>
                   ((let (baseaddress :: 52 bits) =
                     (if (((((ex_int outputsize)) = (( 52 :: int)::ii)))) then
                       (concat_vec ((slice desc (( 12 :: int)::ii) (( 4 :: int)::ii)  ::  4 Word.word))
                          ((slice_zeros_concat
                              ((((((- gsz)) + (( 48 :: int)::ii))) + gsz)) desc
                              gsz ((((- gsz)) + (( 48 :: int)::ii))) gsz
                             ::  48 Word.word))
                         ::  52 Word.word)
                     else
                       (place_slice (( 52 :: int)::ii) desc gsz ((((- gsz)) + (( 48 :: int)::ii)))
                          gsz
                         ::  52 Word.word)) in
                   (let (ns_table :: 1 bits) =
                     (if ((\<not> secondstage)) then
                       (or_vec ns_table (vec_of_bits [access_vec_dec desc (( 63 :: int)::ii)]  ::  1 Word.word)
                         ::  1 Word.word)
                     else ns_table) in
                   (let ((ap_table :: 2 bits), (pxn_table :: 1 bits), (xn_table :: 1 bits)) =
                     (if (((((\<not> secondstage)) \<and> ((\<not> hierattrsdisabled))))) then
                       (let (ap_table :: 2 bits) =
                         ((set_slice (( 2 :: int)::ii) (( 1 :: int)::ii) ap_table (( 1 :: int)::ii)
                            ((or_vec (vec_of_bits [access_vec_dec ap_table (( 1 :: int)::ii)]  ::  1 Word.word)
                                (vec_of_bits [access_vec_dec desc (( 62 :: int)::ii)]  ::  1 Word.word)
                               ::  1 Word.word))
                           ::  2 Word.word)) in
                       (let ((pxn_table :: 1 bits), (xn_table :: 1 bits)) =
                         (if apply_nvnv1_effect then
                           (let (pxn_table :: 1 bits) =
                             ((or_vec pxn_table
                                (vec_of_bits [access_vec_dec desc (( 60 :: int)::ii)]  ::  1 Word.word)
                               ::  1 Word.word)) in
                           (pxn_table, xn_table))
                         else
                           (let (xn_table :: 1 bits) =
                             ((or_vec xn_table
                                (vec_of_bits [access_vec_dec desc (( 60 :: int)::ii)]  ::  1 Word.word)
                               ::  1 Word.word)) in
                           (pxn_table, xn_table))) in
                       (let ((ap_table :: 2 bits), (pxn_table :: 1 bits)) =
                         (if ((\<not> singlepriv)) then
                           (let ((ap_table :: 2 bits), (pxn_table :: 1 bits)) =
                             (if ((\<not> apply_nvnv1_effect)) then
                               (let (pxn_table :: 1 bits) =
                                 ((or_vec pxn_table
                                    (vec_of_bits [access_vec_dec desc (( 59 :: int)::ii)]  ::  1 Word.word)
                                   ::  1 Word.word)) in
                               (let (ap_table :: 2 bits) =
                                 ((set_slice (( 2 :: int)::ii) (( 1 :: int)::ii) ap_table (( 0 :: int)::ii)
                                    ((or_vec
                                        (vec_of_bits [access_vec_dec ap_table (( 0 :: int)::ii)]  ::  1 Word.word)
                                        (vec_of_bits [access_vec_dec desc (( 61 :: int)::ii)]  ::  1 Word.word)
                                       ::  1 Word.word))
                                   ::  2 Word.word)) in
                               (ap_table, pxn_table)))
                             else (ap_table, pxn_table)) in
                           (ap_table, pxn_table))
                         else (ap_table, pxn_table)) in
                       (ap_table, pxn_table, xn_table))))
                     else (ap_table, pxn_table, xn_table)) in
                   (let (level :: ii) = (((ex_int level)) + (( 1 :: int)::ii)) in
                   (let (addrselecttop :: ii) = (((ex_int addrselectbottom)) - (( 1 :: int)::ii)) in
                   (let (blocktranslate :: bool) = False in
                   return (addrselecttop,
                           ap_table,
                           baseaddress,
                           blocktranslate,
                           level,
                           ns_table,
                           pxn_table,
                           result,
                           xn_table))))))))))) \<bind> (\<lambda> varstup .  (let ((addrselecttop :: ii), (ap_table :: 2
                bits), (baseaddress :: 52 bits), (blocktranslate :: bool), (level :: ii), (ns_table :: 1
                bits), (pxn_table :: 1 bits), (result :: TLBRecord), (xn_table :: 1 bits)) = varstup in
              return (accdesc,
                      addrselectbottom,
                      addrselecttop,
                      ap_table,
                      baseaddress,
                      blocktranslate,
                      desc,
                      descaddr,
                      descaddr2,
                      hwupdatewalk,
                      level,
                      ns_table,
                      pxn_table,
                      result,
                      xn_table)))))))))))))))))))))))
*)

Definition TranslationTableWalk_loop_cond {rv e} : AccessDescriptor * Z * Z * word 2 * word 52 * bool * word 64 * AddressDescriptor *
   AddressDescriptor * bool * Z * word 1 * word 1 * TLBRecord * word 1 -> monad rv bool e :=
            (fun varstup =>
            (let '(accdesc,
                 addrselectbottom,
                 addrselecttop,
                 ap_table,
                 baseaddress,
                 blocktranslate,
                 desc,
                 descaddr,
                 descaddr2,
                 hwupdatewalk,
                 level,
                 ns_table,
                 pxn_table,
                 result,
                 xn_table) := varstup in
              returnm blocktranslate)).

Local Open Scope Z.

Definition TranslationTableWalk_loop_termination_precond 
 (vars : AccessDescriptor * Z * Z * word 2 * word 52 * bool * word 64 * AddressDescriptor *
   AddressDescriptor * bool * Z * word 1 * word 1 * TLBRecord * word 1 ) : Prop :=
     match vars with (accdesc,
                 addrselectbottom,
                 addrselecttop,
                 ap_table,
                 baseaddress,
                 blocktranslate,
                 desc,
                 descaddr,
                 descaddr2,
                 hwupdatewalk,
                 level,
                 ns_table,
                 pxn_table,
                 result,
                 xn_table) => level >= 0 /\ level < 4
     end.

(*
Definition
  "TranslationTableWalk_loop_variant vars =
     (case vars of (accdesc,
                 addrselectbottom,
                 addrselecttop,
                 ap_table,
                 baseaddress,
                 blocktranslate,
                 desc,
                 descaddr,
                 descaddr2,
                 hwupdatewalk,
                 level,
                 ns_table,
                 pxn_table,
                 result,
                 xn_table) \<Rightarrow> 4 - nat level)"
*)
*)
Import List.ListNotations.
Import Sail.Values Sail.Operators_mwords.

Definition calc_outputsize (PS : mword 3) (largegrain : bool) : Z :=
  if eq_vec PS (vec_of_bits [B0; B0; B0]) then 32
  else if eq_vec PS (vec_of_bits [B0; B0; B1]) then 36
  else if eq_vec PS (vec_of_bits [B0; B1; B0]) then 40
  else if eq_vec PS (vec_of_bits [B0; B1; B1]) then 42
  else if eq_vec PS (vec_of_bits [B1; B0; B0]) then 44
  else if eq_vec PS (vec_of_bits [B1; B0; B1]) then 48
  else if eq_vec PS (vec_of_bits [B1; B1; B0]) then if largegrain then 52 else 48 else 48.

Lemma calc_outputsize_bounds (*[simp]:*) PS largegrain :
  32 <= calc_outputsize PS largegrain <= 52.
(*  "52 < calc_outputsize PS largegrain \<longleftrightarrow> False"
  by (auto simp: calc_outputsize_def)*)
unfold calc_outputsize.
repeat match goal with |- context [if ?c then _ else _] => destruct c end; omega.
Qed.

(*
definition Parameters_EL0 where
  "Parameters_EL0 descaddr secondstage top1 (inputaddr :: 64 word) c =
     (if ((((vec_of_bits [access_vec_dec inputaddr top1]  ::  1 Word.word) = (vec_of_bits [B0]  ::  1 Word.word)))) then
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__82 :: 64 bits) . 
        (let inputsize =
          ((( 64 :: int)::ii) - ((Word.uint ((slice w__82 (( 0 :: int)::ii) (( 6 :: int)::ii)  ::  6 Word.word))))) in
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__83 :: 64 bits) . 
        (let largegrain =
          (((slice w__83 (( 14 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word)) = (vec_of_bits [B0,B1]  ::  2 Word.word)) in
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__84 :: 64 bits) . 
        (let midgrain =
          (((slice w__84 (( 14 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word)) = (vec_of_bits [B1,B0]  ::  2 Word.word)) in
        (let inputsize_max =
          (if (((((Have52BitVAExt () )) \<and> largegrain))) then (( 52 :: int)::ii)
          else (( 48 :: int)::ii)) in
        (if ((((ex_int inputsize)) > ((ex_int inputsize_max)))) then
           (let c = (ConstrainUnpredictable Unpredictable_RESTnSZ) in
           liftR (assert_exp ((((((c = Constraint_FORCE))) \<or> (((c = Constraint_FAULT)))))) ('''')) \<then>
           ((let (inputsize :: ii) =
             (if (((c = Constraint_FORCE))) then inputsize_max
             else inputsize) in
           return (c, inputsize))))
         else return (c, inputsize)) \<bind> (\<lambda> varstup .  (let ((c :: Constraint), (inputsize ::
          ii)) = varstup in
        (let inputsize_min = ((( 64 :: int)::ii) - (( 39 :: int)::ii)) in
        (if ((((ex_int inputsize)) < ((ex_int inputsize_min)))) then
           (let c = (ConstrainUnpredictable Unpredictable_RESTnSZ) in
           liftR (assert_exp ((((((c = Constraint_FORCE))) \<or> (((c = Constraint_FAULT)))))) ('''')) \<then>
           ((let (inputsize :: ii) =
             (if (((c = Constraint_FORCE))) then inputsize_min
             else inputsize) in
           return inputsize)))
         else return inputsize) \<bind> (\<lambda> (inputsize :: ii) . 
        and_boolM
          (return (((((((ex_int inputsize)) \<ge> ((ex_int inputsize_min)))) \<and> ((((ex_int inputsize)) \<le> ((ex_int inputsize_max))))))))
          (liftR ((IsZero_slice inputaddr inputsize
                     ((((((ex_int top1)) - ((ex_int inputsize)))) +
                         (( 1 :: int)::ii)))))) \<bind> (\<lambda> (w__86 :: bool) . 
        (let basefound = w__86 in
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__87 :: 64 bits) . 
        (let disabled =
          ((vec_of_bits [access_vec_dec w__87 (( 7 :: int)::ii)]  ::  1 Word.word) = (vec_of_bits [B1]  ::  1 Word.word)) in
        liftR ((read_reg TTBR0_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__88 :: 64 bits) . 
        (let baseregister = w__88 in
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__89 :: 64 bits) . 
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__90 :: 64 bits) . 
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__91 :: 64 bits) . 
        liftR (WalkAttrDecode ((slice w__89 (( 12 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word))
                 ((slice w__90 (( 10 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word))
                 ((slice w__91 (( 8 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word)) secondstage) \<bind> (\<lambda> (w__92 ::
          MemoryAttributes) . 
        (let descaddr = ((descaddr (| AddressDescriptor_memattrs := w__92 |))) in
        and_boolM (return ((AArch64_HaveHPDExt () )))
          (liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__93 :: 64 bits) . 
           return ((((vec_of_bits [access_vec_dec w__93 (( 41 :: int)::ii)]  ::  1 Word.word) = (vec_of_bits [B1]  ::  1 Word.word)))))) \<bind> (\<lambda> (w__94 :: bool) . 
        (let (hierattrsdisabled :: bool) = w__94 in
        return (basefound,
                baseregister,
                descaddr,
                disabled,
                hierattrsdisabled,
                inputsize,
                largegrain,
                midgrain)))))))))))))))))))))))))
      else
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__95 :: 64 bits) . 
        (let inputsize =
          ((( 64 :: int)::ii) - ((Word.uint ((slice w__95 (( 16 :: int)::ii) (( 6 :: int)::ii)  ::  6 Word.word))))) in
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__96 :: 64 bits) . 
        (let largegrain =
          (((slice w__96 (( 30 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word)) = (vec_of_bits [B1,B1]  ::  2 Word.word)) in
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__97 :: 64 bits) . 
        (let midgrain =
          (((slice w__97 (( 30 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word)) = (vec_of_bits [B0,B1]  ::  2 Word.word)) in
        (let inputsize_max =
          (if (((((Have52BitVAExt () )) \<and> largegrain))) then (( 52 :: int)::ii)
          else (( 48 :: int)::ii)) in
        (if ((((ex_int inputsize)) > ((ex_int inputsize_max)))) then
           (let c = (ConstrainUnpredictable Unpredictable_RESTnSZ) in
           liftR (assert_exp ((((((c = Constraint_FORCE))) \<or> (((c = Constraint_FAULT)))))) ('''')) \<then>
           ((let (inputsize :: ii) =
             (if (((c = Constraint_FORCE))) then inputsize_max
             else inputsize) in
           return (c, inputsize))))
         else return (c, inputsize)) \<bind> (\<lambda> varstup .  (let ((c :: Constraint), (inputsize ::
          ii)) = varstup in
        (let inputsize_min = ((( 64 :: int)::ii) - (( 39 :: int)::ii)) in
        (if ((((ex_int inputsize)) < ((ex_int inputsize_min)))) then
           (let c = (ConstrainUnpredictable Unpredictable_RESTnSZ) in
           liftR (assert_exp ((((((c = Constraint_FORCE))) \<or> (((c = Constraint_FAULT)))))) ('''')) \<then>
           ((let (inputsize :: ii) =
             (if (((c = Constraint_FORCE))) then inputsize_min
             else inputsize) in
           return inputsize)))
         else return inputsize) \<bind> (\<lambda> (inputsize :: ii) . 
        and_boolM
          (return (((((((ex_int inputsize)) \<ge> ((ex_int inputsize_min)))) \<and> ((((ex_int inputsize)) \<le> ((ex_int inputsize_max))))))))
          (liftR ((IsOnes_slice inputaddr inputsize
                     ((((((ex_int top1)) - ((ex_int inputsize)))) +
                         (( 1 :: int)::ii)))))) \<bind> (\<lambda> (w__99 :: bool) . 
        (let basefound = w__99 in
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__100 :: 64 bits) . 
        (let disabled =
          ((vec_of_bits [access_vec_dec w__100 (( 23 :: int)::ii)]  ::  1 Word.word) = (vec_of_bits [B1]  ::  1 Word.word)) in
        liftR ((read_reg TTBR1_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__101 :: 64 bits) . 
        (let baseregister = w__101 in
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__102 :: 64 bits) . 
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__103 :: 64 bits) . 
        liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__104 :: 64 bits) . 
        liftR (WalkAttrDecode ((slice w__102 (( 28 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word))
                 ((slice w__103 (( 26 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word))
                 ((slice w__104 (( 24 :: int)::ii) (( 2 :: int)::ii)  ::  2 Word.word)) secondstage) \<bind> (\<lambda> (w__105 ::
          MemoryAttributes) . 
        (let descaddr = ((descaddr (| AddressDescriptor_memattrs := w__105 |))) in
        and_boolM (return ((AArch64_HaveHPDExt () )))
          (liftR ((read_reg TCR_EL1_ref  :: ( 64 Word.word) M)) \<bind> (\<lambda> (w__106 :: 64 bits) . 
           return ((((vec_of_bits [access_vec_dec w__106 (( 42 :: int)::ii)]  ::  1 Word.word) = (vec_of_bits [B1]  ::  1 Word.word)))))) \<bind> (\<lambda> (w__107 :: bool) . 
        (let (hierattrsdisabled :: bool) = w__107 in
        return (basefound,
                baseregister,
                descaddr,
                disabled,
                hierattrsdisabled,
                inputsize,
                largegrain,
                midgrain))))))))))))))))))))))))))"
*)
Definition calc_startlevel inputsize grainsize stride :=
  Z.sub 4 (round_up (div_real (to_real (Z.sub inputsize grainsize)) (to_real stride))).

Definition calc_baseaddress (baseregister : mword 64) baselowerbound outputsize `{ArithFact (baselowerbound >=? 0)} :=
  if sumbool_of_bool ((Z.eqb outputsize 52)) then
    let 'z :=
        projT1
          (build_ex
             (if sumbool_of_bool ((Z.ltb baselowerbound 6)) then 6
              else baselowerbound)
           : {n : Z & ArithFact (n >=? 0)}) in
    liftR (assert_exp' (Z.geb (Z.add (Z.opp (projT1 (__id z))) 48) 0) "model/aarch_mem.sail 10457:41 - 10457:42") >>= fun _ =>
    let baseaddress : bits 52 :=
        autocast (concat_vec
                    (concat_vec (slice baseregister 2 4)
                                (slice baseregister z (Z.add (Z.opp z) 48))) (zeros z)) in
    returnm baseaddress
  else
    liftR ((ZeroExtend_slice_append 52 baseregister baselowerbound
                                    (Z.add (Z.opp baselowerbound) 48) (zeros baselowerbound)))
  : MR (mword 52) TLBRecord.

Definition calc_firstblocklevel_grainsize largegrain midgrain :=
  (if sumbool_of_bool (largegrain) then
     let grainsize := 16 in
     let firstblocklevel : Z := if ((Have52BitPAExt tt)) then 1 else 2 in
     (firstblocklevel, build_ex grainsize)
   else
     let '(firstblocklevel, existT _ grainsize _) :=
         (if sumbool_of_bool (midgrain) then
            let grainsize := 14 in
            let firstblocklevel : Z := 2 in
            (firstblocklevel, build_ex grainsize)
          else
            let grainsize := 12 in
            let firstblocklevel : Z := 1 in
            (firstblocklevel, build_ex grainsize))
         : (Z * {n : Z & ArithFact (n >=? 0)}) in
     (firstblocklevel, build_ex grainsize))
  : (Z * {n : Z & ArithFact (n >=? 0)}).

Definition calc_contiguousbitcheck inputsize largegrain midgrain level :=
  if sumbool_of_bool (largegrain) then andb (Z.eqb level 2) (Z.ltb inputsize 34)
  else if sumbool_of_bool (midgrain) then andb (Z.eqb level 2) (Z.ltb inputsize 30)
  else andb (Z.eqb level 1) (Z.ltb inputsize 34).


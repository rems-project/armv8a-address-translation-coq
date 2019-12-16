Require Import Sail2_values Sail2_values_lemmas Sail2_operators_mwords Sail2_state_monad Word.
Require Import aarch64_types aarch64 Address_Translation_Orig AArch64_Aux.

Import Word.Notations.
Import ListNotations.
Local Open Scope word_scope.
Local Open Scope bool.
Local Open Scope Z.

(*
(*<*)
(* Author: Thomas Bauereiss *)
theory Address_Translation_Pure
  imports AArch64_Aux Address_Translation_Orig
begin
(*>*)

section \<open>Pure characterisation\<close>

subsection \<open>Types\<close>

text \<open>Translation tables are represented as a list of entries, each of which might recursively
contain another table.\<close>
*)

Inductive TableEntry : Type :=
  Invalid
  | Descriptor : word 64 -> TableEntry (* 64-bit block or page descriptor *)
  | Table : word 52 -> bool -> bool -> bool -> bool -> bool -> list TableEntry -> TableEntry. (* base address, table attributes, entries *)

(*text \<open>A record for the main parameters of the translation, e.g. address size or page size.\<close>*)

Record Parameters := {
  inputsize : Z;
  outputsize : Z;
  grainsize : Z;
  firstblocklevel : Z;
  updateAF : bool;
  SH : word 2;
  ORGN : word 2;
  IRGN : word 2
}.

(* TODO: move *)
Notation "v !! n" := (getBit v n) (at level 20).
(*
Lemma cast_to_mword 
  @cast_to_mword m n w E = 
*)

(*
Notation "'word_slice' i v n" :=
 (@Word_slice (ltac:(
   let ty := type of v in
   match ty with
   | word ?len => constr:((len - i - n)%nat)
   | mword ?len => constr:((Z.to_nat len - i - n)%nat)
   end)) n i v) (at level 10, i, v at level 9).

Notation "'word_slice' i v n" :=
 (ltac:(
   let ty := type of v in
   let m := match ty with
   | word ?len => constr:((len - i - n)%nat)
(*   | mword ?len => constr:((Z.to_nat len - i - n)%nat)*)
   end in constr:(@Word_slice m n i v))) (at level 10, i, v at level 9).
*)
Definition word_size {n} (_ : word n) := n.

Import ConversionNotations.

(*subsection \<open>Auxiliary functions for our pure characterisation, e.g. for reading the translation
parameters from the control registers or decoding descriptor attributes.\<close>*)

Definition read_params (high : bool) (s : sequential_state regstate) : Parameters :=
  let largegrain := if high then weqb (slice (TCR_EL1 (ss_regstate s)) 30 2) $3
                    else weqb (slice (TCR_EL1 (ss_regstate s)) 14 2) ($1 : word 2) in
  let midgrain := if high then weqb (slice (TCR_EL1 (ss_regstate s)) 30 2) ($1 : word 2)
                  else weqb (slice (TCR_EL1 (ss_regstate s)) 14 2) ($2 : word 2) in
  let grainsize := if largegrain then 16 else if midgrain then 14 else 12 in
  let outputsize := calc_outputsize (slice (TCR_EL1 (ss_regstate s)) 32 3) largegrain in
  let inputsize_max := if largegrain then 52 else 48 in
  let inputsize := 64 - (projT1 (uint (slice (TCR_EL1 (ss_regstate s)) (if high then 16 else 0) 6))) in
    {| inputsize := Z.min (Z.max inputsize 25) inputsize_max;
       outputsize := outputsize;
       grainsize := grainsize;
       firstblocklevel := (if andb (negb largegrain) midgrain then 2 else 1);
       updateAF := TCR_EL1 (ss_regstate s) !! 39;
       SH := slice (TCR_EL1 (ss_regstate s)) (if high then 28 else 12) 2;
       ORGN := slice (TCR_EL1 (ss_regstate s)) (if high then 26 else 10) 2;
       IRGN := slice (TCR_EL1 (ss_regstate s)) (if high then 24 else 8) 2 |}.

Lemma inputsize_range high s :
  0 <= inputsize (read_params high s) <= 52.
unfold read_params, inputsize.
(*match goal with |- context[projT1 ?x] =>
let v := fresh "v" in
let H := fresh "H" in
destruct x as [v H];
change (projT1 (existT _ v H)) with v
end.*)
repeat match goal with |- context[if ?b then _ else _] => destruct b end;
omega with Z.
Qed.

Lemma grainsize_range high s :
  12 <= grainsize (read_params high s) <= 16.
unfold read_params, grainsize.
repeat match goal with |- context[if ?b then _ else _] => destruct b end;
omega with Z.
Qed.

Lemma grainsize_split high s :
  grainsize (read_params high s) = 12 \/
  grainsize (read_params high s) = 14 \/
  grainsize (read_params high s) = 16.
unfold read_params, grainsize.
repeat match goal with |- context[if ?b then _ else _] => destruct b end; auto.
Qed.

Definition largegrain p := Z.eqb (grainsize p) 16.
Definition midgrain p := Z.eqb (grainsize p) 14.

Definition startlevel (p : Parameters) : Z :=
  calc_startlevel (inputsize p) (grainsize p) (grainsize p - 3).

(* TODO: move *)
Require Import Sail2_real Reals Psatz.

Lemma IZRdiv m n :
  0 < m -> 0 < n ->
  (IZR (m / n) <= IZR m / IZR n)%R.
intros.
apply Rmult_le_reg_l with (r := IZR n).
auto using IZR_lt.
unfold Rdiv.
rewrite <- Rmult_assoc.
rewrite Rinv_r_simpl_m.
rewrite <- mult_IZR.
apply IZR_le.
apply Z.mul_div_le.
assumption.
discrR.
omega.
Qed.

Lemma round_up_div m n :
  0 < m -> 0 < n ->
  round_up (div_real (to_real m) (to_real n)) = (m + n - 1) / n.
intros.
unfold round_up, round_down, div_real, to_real.
apply Z.eq_opp_l.
apply Z.sub_move_r.
symmetry.
apply up_tech.

rewrite Ropp_Ropp_IZR.
apply Ropp_le_contravar.
apply Rmult_le_reg_l with (r := IZR n).
auto using IZR_lt.
unfold Rdiv.
rewrite <- Rmult_assoc.
rewrite Rinv_r_simpl_m.
rewrite <- mult_IZR.
apply IZR_le.
assert (diveq : n*((m+n-1)/n) = (m+n-1) - (m+n-1) mod n).
apply Zplus_minus_eq.
rewrite (Z.add_comm ((m+n-1) mod n)).
apply Z.div_mod.
omega.
rewrite diveq.
assert (modmax : (m+n-1) mod n < n).
specialize (Z.mod_pos_bound (m+n-1) n). intuition.
omega.

discrR; omega.

rewrite <- Z.opp_sub_distr.
rewrite Ropp_Ropp_IZR.
apply Ropp_lt_contravar.
apply Rmult_lt_reg_l with (r := IZR n).
auto using IZR_lt.
unfold Rdiv.
rewrite <- Rmult_assoc.
rewrite Rinv_r_simpl_m.
2: { discrR. omega. }
rewrite <- mult_IZR.
apply IZR_lt.
rewrite Z.mul_sub_distr_l.
apply Z.le_lt_trans with (m := m+n-1-n*1).
apply Z.sub_le_mono_r.
apply Z.mul_div_le.
assumption.
omega.
Qed.


Lemma startlevel_bounds high s :
  0 <= startlevel (read_params high s) < 4.
unfold startlevel, read_params, calc_startlevel, inputsize, grainsize.
rewrite round_up_div.

split.
apply Zle_minus_le_0.

repeat match goal with |- context[if ?b then _ else _] => destruct b end;
try match goal with |- context[uint ?v] => destruct (uint v) as [i [H]]; simpl (projT1 _) end;
match goal with |- _ / ?denom <= _ => change 4 with ((4*denom + denom - 1)/denom); apply Z.div_le_mono end;
try simpl in H;
try omega with Z.

apply Z.lt_sub_pos.
apply Z.div_str_pos.
repeat match goal with |- context[if ?b then _ else _] => destruct b end;
try match goal with |- context[uint ?v] => destruct (uint v) as [i [H]]; simpl (projT1 _) end;
try simpl in H;
try omega with Z.

repeat match goal with |- context[if ?b then _ else _] => destruct b end;
try match goal with |- context[uint ?v] => destruct (uint v) as [i [H]]; simpl (projT1 _) end;
try simpl in H;
try omega with Z.

repeat match goal with |- context[if ?b then _ else _] => destruct b end;
try match goal with |- context[uint ?v] => destruct (uint v) as [i [H]]; simpl (projT1 _) end;
try simpl in H;
try omega with Z.
Qed.

Lemma startlevel_largegrain_bounds high s p :
  p = read_params high s ->
  grainsize p = 16 ->
  1 <= startlevel p.
intros -> GRAINSIZE.
unfold startlevel, read_params, calc_startlevel, inputsize, grainsize in *.
rewrite round_up_div.
2,3: repeat match goal with |- context[if ?b then _ else _] => destruct b end;
try match goal with |- context[uint ?v] => destruct (uint v) as [i [H]]; simpl (projT1 _) end;
try simpl in H;
omega with Z.

apply Zle_0_minus_le.
rewrite <- Z.sub_add_distr.
rewrite Z.add_comm.
rewrite Z.sub_add_distr.
simpl (4 - 1).
apply Zle_minus_le_0.

repeat match goal with |- context[if ?b then _ else _] => destruct b end;
  try match goal with |- context[uint ?v] => destruct (uint v) as [i [H]]; simpl (projT1 _) end;
  match goal with |- ?nom / ?denom <= ?rhs => change (nom / denom <= rhs) with (nom / denom <= ((rhs*denom + denom - 1)/denom)); apply Z.div_le_mono end;
  try simpl in H;
  omega with Z.
Qed.

Definition baselowerbound (p : Parameters) : Z :=
  3 + (inputsize p) - ((3 - startlevel p) * (grainsize p - 3) + (grainsize p)).

Lemma mul_div_pos_range a b :
  0 <= a ->
  0 < b ->
  a - b < b * (a / b) <= a.
intro H.
split; auto using Z.mul_div_le.
specialize (Z.div_mod a b ltac:(omega)).
specialize (Z.mod_bound_pos a b).
generalize (a mod b).
generalize (b * (a / b)).
intros.
subst.
omega with Z.
Qed.

Lemma baselowerbound_bounds high s :
  0 < baselowerbound (read_params high s) < 48.
unfold baselowerbound, read_params, startlevel, calc_startlevel, grainsize, inputsize.
match goal with |- context[uint ?v] => destruct (uint v) as [i [H1]]; simpl (projT1 _) end;
simpl in H1.
rewrite round_up_div.

split;

repeat match goal with |- context[if ?b then _ else _] => destruct b end;
zify;
rewrite !Z.mul_sub_distr_r;
match goal with |- context[(Z.div ?nom ?denom) * ?denom] => specialize (mul_div_pos_range nom denom); generalize (Z.div nom denom) end;
intros;
omega.

repeat match goal with |- context[if ?b then _ else _] => destruct b end;
omega with Z.

repeat match goal with |- context[if ?b then _ else _] => destruct b end;
omega with Z.
Qed.

Lemma baselowerbound_bounds' high s p :
  p = read_params high s ->
  0 < baselowerbound p < 48.
intros ->.
apply baselowerbound_bounds.
Qed.

Definition contiguousbitcheck p level :=
  calc_contiguousbitcheck (inputsize p) (largegrain p) (midgrain p) level.

Definition baseaddress (baseregister : mword 64) (baselowerbound_arg : Z) `{ArithFact (0 <? baselowerbound_arg <? 48)} (outputsize_arg : Z) : mword 52 :=
  if Z.eqb outputsize_arg 52 then
    let z := Z.max baselowerbound_arg 6 in
                 autocast (concat_vec
                             (concat_vec (slice baseregister 2 4)
                                (slice baseregister z (Z.add (Z.opp z) 48))) (zeros z))
  else
autocast (concat_vec (zeros 4) (concat_vec (slice baseregister baselowerbound_arg (48 - baselowerbound_arg)) (zeros baselowerbound_arg))).

(* TODO: move *)
Ltac clear_proof_bodies :=
  repeat match goal with
  | H := _ : ?ty |- _ =>
    match type of ty with
    | Prop => clearbody H
    end
  end.
Ltac run_solver ::= clear_proof_bodies; solve_arithfact.

Lemma addrtop_inputsize_pos addrtop high s :
  55 <= addrtop ->
  let p := read_params high s in
  0 <= addrtop - inputsize p + 1.
intros.
specialize (inputsize_range high s) as H1.
unfold p.
omega.
Qed.
Hint Resolve addrtop_inputsize_pos : sail.

Lemma inputsize_range' high s p :
  p = read_params high s ->
  0 <= inputsize p <= 52.
intro; subst.
apply inputsize_range.
Qed.

Definition valid_vaddr (addr : mword 64) (addrtop : Z) `{ArithFact (55 <=? addrtop)} (s : sequential_state regstate) : bool :=
  let high := addr !! Z.to_nat addrtop in
  let p := read_params high s in
  let _ := inputsize_range' high s p eq_refl in
  if high
  then IsOnes (slice addr (inputsize p) (addrtop - inputsize p + 1))
  else IsZero (slice addr (inputsize p) (addrtop - inputsize p + 1)).

Definition IsBlockDescriptor (desc : mword 64) : bool :=
  weqb (slice desc 0 2) $1.

Definition ValidDescriptor (level : Z) (grainsize_arg : Z) (outputsize_arg : Z) (desc : mword 64) : bool :=
  desc !! 0 &&
  negb (IsBlockDescriptor desc && Z.eqb level 3) &&
  implb (negb (IsBlockDescriptor desc) && Z.ltb level 3)
     ((implb (Z.ltb outputsize_arg 52 && Z.eqb grainsize_arg 16) (weqb (slice desc 12 4) $0)) &&
      (if sumbool_of_bool (Z.ltb outputsize_arg 48) then IsZero (slice desc outputsize_arg (48 - outputsize_arg)) else true)).


Definition read_WalkAttrDecode (SH_arg : mword 2) (ORGN_arg : mword 2) (IRGN_arg : mword 2) (secondstage : bool) (s : sequential_state regstate) : MemoryAttributes :=
     {| MemoryAttributes_typ := MemType_Normal;
        MemoryAttributes_device := DeviceType_GRE;
        MemoryAttributes_inner :=
          {| MemAttrHints_attrs :=
               if negb secondstage && implb (read_SCTLR (read_S1TranslationRegime (read_EL s) s) s !! 2) (eq_vec IRGN_arg $0) ||
                     secondstage && (HCR_EL2 (ss_regstate s) !! 32 || eq_vec IRGN_arg $0)
                  then $0 else if eq_vec IRGN_arg $1 || negb (eq_vec IRGN_arg $2) then $3 else $2;
             MemAttrHints_hints :=
               if negb secondstage && implb (read_SCTLR (read_S1TranslationRegime (read_EL s) s) s !! 2) (eq_vec IRGN_arg $0) ||
                       secondstage && (HCR_EL2 (ss_regstate s) !! 32 || eq_vec IRGN_arg $0)
                    then MemHint_No else if eq_vec IRGN_arg $1 then MemHint_RWA else MemHint_RA;
             MemAttrHints_transient := false |};
        MemoryAttributes_outer :=
          {| MemAttrHints_attrs :=
               if negb secondstage && implb (read_SCTLR (read_S1TranslationRegime (read_EL s) s) s !! 2) (eq_vec ORGN_arg $0) ||
                     secondstage && (HCR_EL2 (ss_regstate s) !! 32 || eq_vec ORGN_arg $0)
               then $0 else if eq_vec ORGN_arg $1 || negb (eq_vec ORGN_arg $2) then $3 else $2;
             MemAttrHints_hints :=
               if negb secondstage && implb (read_SCTLR (read_S1TranslationRegime (read_EL s) s) s !! 2) (eq_vec ORGN_arg $0) ||
                       secondstage && (HCR_EL2 (ss_regstate s) !! 32 || eq_vec ORGN_arg $0)
                    then MemHint_No else if eq_vec ORGN_arg $1 then MemHint_RWA else MemHint_RA;
             MemAttrHints_transient := false |};
        MemoryAttributes_shareable :=
               if negb secondstage then implb (read_SCTLR (read_S1TranslationRegime (read_EL s) s) s !! 2) (eq_vec IRGN_arg $0) && eq_vec ORGN_arg $0 || eq_vec SH_arg $1
               else (HCR_EL2 (ss_regstate s) !! 32 || eq_vec IRGN_arg $0) && (HCR_EL2 (ss_regstate s) !! 32 || eq_vec ORGN_arg $0) || SH_arg !! 1;
        MemoryAttributes_outershareable :=
               if negb secondstage then implb (read_SCTLR (read_S1TranslationRegime (read_EL s) s) s !! 2) (eq_vec IRGN_arg $0) && eq_vec ORGN_arg $0 || eq_vec SH_arg $2
               else (HCR_EL2 (ss_regstate s) !! 32 || eq_vec IRGN_arg $0) && (HCR_EL2 (ss_regstate s) !! 32 || eq_vec ORGN_arg $0) || eq_vec SH_arg $2;
        MemoryAttributes_tagged := false
|}.

Definition read_S1CacheDisabled (acctype : AccType) (s : sequential_state regstate) : bool :=
  let sctlr := read_SCTLR (read_S1TranslationRegime (read_EL s) s) s in
  if generic_eq acctype AccType_IFETCH then negb(sctlr !! 12) else negb (sctlr !! 2).

Definition read_LongConvertAttrsHints (attrfield : mword 4) (acctype : AccType) (s : sequential_state regstate) : MemAttrHints :=
  {| MemAttrHints_attrs :=
        if read_S1CacheDisabled acctype s || eq_vec attrfield $4 then MemAttr_NC else
        if weqb (slice attrfield 2 2) ($0 : word 2) then MemAttr_WT else
        if weqb (slice attrfield 2 2) ($1 : word 2) then slice attrfield 0 _ else
        slice attrfield 2 2;
     MemAttrHints_hints :=
        if read_S1CacheDisabled acctype s || eq_vec attrfield $4 then MemHint_No else
        if weqb (slice attrfield 2 2) ($0 : word 2) then slice attrfield 0 _ else
        if weqb (slice attrfield 2 2) ($1 : word 2) then MemAttr_WB else (* Is this intentional? *)
        slice attrfield 0 _;
     MemAttrHints_transient :=
        if read_S1CacheDisabled acctype s then false else
        neq_vec attrfield $4 && negb(attrfield !! 3) |}.

Definition read_S1AttrDecode (SH_arg : mword 2) (attr : mword 2) (acctype : AccType) (s : sequential_state regstate) : MemoryAttributes :=
  let mair := read_MAIR (read_S1TranslationRegime (read_EL s) s) s in
  let attrslo := slice mair (8 * wordToZ attr) 4 in
  let attrshi := slice mair (4 + (8 * wordToZ attr)) 4 in
  let ihints := read_LongConvertAttrsHints attrslo acctype s in
  let ohints := read_LongConvertAttrsHints attrshi acctype s in
  {| MemoryAttributes_typ := if eq_vec attrslo $0 || eq_vec attrshi $0 then MemType_Device else MemType_Normal;
   MemoryAttributes_device :=
     if eq_vec attrslo $0 || eq_vec attrshi $0 then
       (if eq_vec attrslo $0 then DeviceType_nGnRnE
        else if eq_vec attrslo $4 then DeviceType_nGnRE
        else if eq_vec attrslo $8 then DeviceType_nGRE
        else if eq_vec attrslo $12 then DeviceType_GRE
        else DeviceType_nGnRnE)
     else DeviceType_GRE;
   MemoryAttributes_inner :=
     if neq_vec attrslo $0 && neq_vec attrshi $0 then ihints
     else {| MemAttrHints_attrs := $0; MemAttrHints_hints := $0; MemAttrHints_transient := false |};
   MemoryAttributes_outer :=
     if neq_vec attrslo $0 && neq_vec attrshi $0 then ohints
     else {| MemAttrHints_attrs := $0; MemAttrHints_hints := $0; MemAttrHints_transient := false |};
   MemoryAttributes_shareable :=
     eq_vec attrslo $0 || eq_vec attrshi $0 ||
     eq_vec (MemAttrHints_attrs ihints) $0 && eq_vec (MemAttrHints_attrs ohints) $0 ||
     SH_arg !! 1;
   MemoryAttributes_outershareable :=
     eq_vec attrslo $0 || eq_vec attrshi $0 ||
     eq_vec (MemAttrHints_attrs ihints) $0 && eq_vec (MemAttrHints_attrs ohints) $0 ||
     eq_vec SH_arg $2;
   MemoryAttributes_tagged :=
     if eq_vec attrslo $0 || eq_vec attrshi $0 then false else true
 |}.

Definition read_TTBR0 s :=
  let el := read_S1TranslationRegime (read_EL s) s in
  if eq_vec el $3 then TTBR0_EL3 (ss_regstate s) else
  if eq_vec el $2 then TTBR0_EL2 (ss_regstate s) else TTBR0_EL1 (ss_regstate s).

Definition read_TTBR1 s :=
  let el := read_S1TranslationRegime (read_EL s) s in
  if eq_vec el $3 then TTBR0_EL3 (ss_regstate s) else
  if eq_vec el $2 then TTBR1_EL2 (ss_regstate s) else TTBR1_EL1 (ss_regstate s).

Definition read_TTBR (high : bool) (s : sequential_state regstate) : mword 64 :=
  if high then read_TTBR1 s else read_TTBR0 s.

Definition TTBR_valid_for_vaddr (addr : mword 64) (addrtop : Z) (s : sequential_state regstate) : bool :=
  let high := addr !! Z.to_nat addrtop in
  let p := read_params high s in
  if sumbool_of_bool (outputsize p <? 48) then IsZero (slice (read_TTBR high s) (outputsize p) (48 - outputsize p)) else true.

Definition addrselecttop (level : Z) (p : Parameters) : Z :=
  Z.min (inputsize p) ((4 - level) * (grainsize p - 3) + grainsize p) - 1.

Definition addrselectbottom (level : Z) (p : Parameters) : Z :=
  (3 - level) * (grainsize p - 3) + grainsize p.

Lemma addrselectbottom_bounds level high s p :
  p = read_params high s ->
  0 <= level < 4 ->
  (grainsize p = 16 -> 1 <= level) ->
  0 <= addrselectbottom level p <= 48.
intros -> LEVEL LEVEL1.
unfold addrselectbottom.
destruct (grainsize_split high s) as [->| [-> | EQ]]; try omega.
rewrite EQ in *.
omega.
Qed.

Definition stride (level : Z) (p : Parameters) : Z :=
  addrselecttop level p - addrselectbottom level p + 1.

Fixpoint read_table_aux (level : Z) (high : bool) (baseaddr : mword 52) (s : sequential_state regstate) (acc : Acc (Zwf.Zwf_up 4) level) : list TableEntry. refine (
  let p := read_params high s in
  let stride := stride level p in
  let descaddrs := List.map (fun idx => wor baseaddr (shiftl (mword_of_int idx : mword 52) 3)) (index_list 0 (Z.shiftl 1 (stride - 1)) 1) in
  let read_desc :=
      fun addr : mword 52 =>
        match read_mem_word addr 8 s with
        | None => Invalid
        | Some desc =>
          let desc := if read_bigendian s then reverse_endianness desc else desc in
          if ValidDescriptor level (grainsize p) (outputsize p) desc && Z.geb level 0 && Z.ltb level 4 then
            if sumbool_of_bool (IsBlockDescriptor desc || Z.geb level 3)
            then Descriptor desc
            else
              let lbaseaddr := (shiftl (slice desc (grainsize p) _) (grainsize p)) : mword 48 in
              let ubaseaddr := (if Z.eqb (outputsize p) 52 then slice desc 12 _ else $0) : mword 4 in
              let baseaddr := concat_vec ubaseaddr lbaseaddr : mword 52 in
              let ns := desc !! 63 in let ap1 := desc !! 62 in let ap0 := desc !! 61 in let xn := desc !! 60 in let pxn := desc !! 59 in
                                                                                                                Table baseaddr ns ap1 ap0 xn pxn (read_table_aux (level + 1) high baseaddr s _)
          else Invalid
        end in
  map read_desc descaddrs).
refine (Acc_inv acc _).
unfold Zwf.Zwf_up.
unbool_comparisons.
omega.
Defined.

Definition read_table (level : Z) (high : bool) (baseaddr : mword 52) (s : sequential_state regstate) : list TableEntry :=
  read_table_aux level high baseaddr s (Zwf.Zwf_up_well_founded _ _).

Fixpoint walk_table_aux (inputaddr : mword 64) (level : Z) (p : Parameters) (baseaddr : mword 52) (table : list TableEntry) (acc : Acc (Zwf.Zwf_up 4) level) : option (mword 64 * mword 52 * mword 52 * Z * bool * bool * bool * bool * bool). refine (
  if sumbool_of_bool (level >=? 4) then None else
  let index := projT1 (uint (slice inputaddr (addrselectbottom level p) (Z.max 0 (stride level p)))) in
  let descaddr := wor baseaddr (shiftl (mword_of_int index : mword 52) 3) in
  match List.nth (Z.to_nat index) table Invalid with
    Invalid => None
  | Descriptor desc => Some (desc, descaddr, baseaddr, level, false, false, false, false, false)
  | Table baseaddr ns ap1 ap0 xn pxn table =>
    match walk_table_aux inputaddr (level + 1) p baseaddr table _ with
      None => None
    | Some (desc, descaddr, baseaddr, level, ns', ap1', ap0', xn', pxn') =>
      Some (desc, descaddr, baseaddr, level, ns || ns', ap1 || ap1', ap0 || ap0', xn || xn', pxn || pxn')
    end
  end).
refine (Acc_inv acc _).
unfold Zwf.Zwf_up.
clearbody index.
abstract (unbool_comparisons; omega).
Defined.

Definition walk_table (inputaddr : mword 64) (level : Z) (p : Parameters) (baseaddr : mword 52) (table : list TableEntry) : option (mword 64 * mword 52 * mword 52 * Z * bool * bool * bool * bool * bool) := walk_table_aux inputaddr level p baseaddr table (Zwf.Zwf_up_well_founded _ _).

Lemma walk_table_level {inputaddr level p baseaddr table x1 x2 x3 level' x4 x5 x6 x7 x8} :
  walk_table inputaddr level p baseaddr table = Some (x1, x2, x3, level', x4, x5, x6, x7, x8) ->
  level <= level' < 4.
unfold walk_table.
generalize (Zwf.Zwf_up_well_founded 4 level).
destruct (Z_le_dec 0 (4 - level)) as [LE|GT].
* assert (level = 4 - (4 - level)) by omega. revert H.
  set (fmlevel := 4-level) in *. clearbody fmlevel.
  intros EQ acc.
  revert level baseaddr table EQ acc x4 x5 x6 x7 x8.
  apply Wf_Z.natlike_ind with (x := fmlevel).
  + intros level baseaddr table -> [acc].
    discriminate.
  + intros foursublevel pos IH level baseaddr table LEVEL [acc] ?*.
    cbn -[Z.add].
    destruct (sumbool_of_bool (level >=? 4)); [ discriminate | ].
    match goal with |- context [nth ?i ?l ?def] => destruct (nth i l def) end;
    [ discriminate | | auto ].
    - match goal with |- context [wor ?l ?r] => generalize (wor l r) end.
      intros ? [=]. subst level'.
      unbool_comparisons.
      omega.
    - match goal with
        |- context [walk_table_aux ?i ?lev ?p ?w ?l ?acc] =>
        specialize (IH lev w l ltac:(omega) acc);
          destruct (walk_table_aux i lev p w l acc) as [[[[[[[[[desc descaddr] baseaddr0] level0] ns'] ap1'] ap0'] xn'] pxn'] | ]; [ | discriminate ]
      end.
      intros [=]; subst x1 x2 x3 level' x4 x5 x6 x7 x8.
      specialize (IH _ _ _ _ _ eq_refl).
      omega.
  + assumption.
* intros [acc].
  cbn.
  destruct (sumbool_of_bool (level >=? 4)) as [GE | LT]; [ discriminate | ].
  exfalso.
  unbool_comparisons.
  omega.
Qed.

(*declare walk_table.simps[simp del]*)

Definition default_FaultRecord :=
  {| FaultRecord_typ := Fault_None;
     FaultRecord_acctype := AccType_NORMAL;
     FaultRecord_ipaddress := {| FullAddress_address := $0; FullAddress_NS := $1 (* TODO? *) |};
     FaultRecord_s2fs1walk := false;
     FaultRecord_write := false;
     FaultRecord_level := 0;
     FaultRecord_extflag := $0;
     FaultRecord_secondstage := false;
     FaultRecord_domain := $0;
     FaultRecord_errortype := $0;
     FaultRecord_debugmoe := $0
  |}.

Definition valid_perms (perms : Permissions) (acctype : AccType) (iswrite : bool) (s : sequential_state regstate) : bool :=
  let wxn := SCTLR_EL1 (ss_regstate s) !! 19 in
  let r := Permissions_ap perms !! 1 in
  let w := weqb (slice (Permissions_ap perms) 1 2) ($1 : mword 2) in
  let xn := weqb (Permissions_xn perms) $1 || (w && wxn) in
  if generic_eq acctype AccType_IFETCH then negb xn
  else if generic_eq acctype AccType_ATOMICRW || generic_eq acctype AccType_ORDEREDRW then r && w
  else if iswrite then w
  else r.

Lemma read_AddrTop_EL0_bounds' addr acc s top :
  top = read_AddrTop_EL0 addr acc s ->
  55 <= top < 64.
intros ->.
apply read_AddrTop_EL0_bounds.
Qed.

Instance bits_Bitvector {a : Z} `{ArithFact (a >=? 0)} : Bitvector (bits a) := mword_Bitvector.
Instance bits1_Bitvector : Bitvector (bits 1) := mword_Bitvector.

Definition lookup_TLBRecord (vaddress : mword 64) (acctype : AccType) (s : sequential_state regstate) : option TLBRecord. refine (
  let top := read_AddrTop_EL0 vaddress (generic_eq acctype AccType_IFETCH) s in
  let _ := read_AddrTop_EL0_bounds' _ _ _ top eq_refl in
  let high := vaddress !! Z.to_nat top in
  let p := read_params high s in
  let blb_bound := baselowerbound_bounds' _ _ p eq_refl in (* not sure why this has to be explicit - wasn't appearing in the context otherwise *)
  let baseaddress := @baseaddress (read_TTBR high s) (baselowerbound p) _ (outputsize p) in
  let hierattrs := negb (if high then TCR_EL1 (ss_regstate s) !! 42 else TCR_EL1 (ss_regstate s) !! 41) in
  let secure := negb (SCR_EL3 (ss_regstate s) !! 0) in
  match walk_table vaddress (startlevel p) p baseaddress
          (read_table (startlevel p) high baseaddress s) as x return _ = x -> _ with
    None => fun _ => None
  | Some (desc, descaddr, baseaddr, level, ns, ap1, ap0, xn, pxn) => fun LEVEL =>
      let _ := walk_table_level LEVEL in
      let addrselectbottom := addrselectbottom level p in
      let asb_bounds := addrselectbottom_bounds level _ _ p eq_refl _ _ in
      let walkattrs := read_WalkAttrDecode (SH p) (ORGN p) (IRGN p) false s in
      let memattrs := read_S1AttrDecode (slice desc 8 _) (slice desc 2 _) acctype s in
      let perms := {|
             Permissions_ap := of_bools [negb (desc !! 51) && desc !! 7 || hierattrs && ap1; desc !! 6 && negb(hierattrs && ap0); true];
             Permissions_xn := of_bools [desc !! 54 || hierattrs && xn];
             Permissions_xxn := $0;
             Permissions_pxn := of_bools [desc !! 53 || hierattrs && pxn] |} in
      if Z.geb level (firstblocklevel p) &&
         valid_vaddr vaddress top s &&
         TTBR_valid_for_vaddr vaddress top s &&
         (if sumbool_of_bool (outputsize p <? 48) then
            eq_vec (slice desc (outputsize p) (48 - outputsize p)) (mword_of_int 0) else true) &&
         (implb ((outputsize p <? 52) && largegrain p) (weqb (slice desc 12 4) ($0 : mword 4))) &&
         (implb (contiguousbitcheck p level) (negb (desc !! 52)))
      then
        let outputaddr : mword 52 :=
          if outputsize p =? 52
          then autocast (concat_vec (slice desc 12 4)
                 (concat_vec (slice desc addrselectbottom (48 - addrselectbottom))
                             (slice vaddress 0 addrselectbottom)))
          else zero_extend (concat_vec (slice desc addrselectbottom (48 - addrselectbottom)) (slice vaddress 0 addrselectbottom)) 52 in
        Some {|
            TLBRecord_perms := perms;
            TLBRecord_nG := of_bools [desc !! 11 || (secure && ns)];
            TLBRecord_domain := $0;
            TLBRecord_GP := of_bools [desc !! 50];
            TLBRecord_contiguous := desc !! 52;
            TLBRecord_level := level;
            TLBRecord_blocksize := 2 ^ addrselectbottom;
            TLBRecord_descupdate := {|
              DescriptorUpdate_AF := negb (desc !! 10);
              DescriptorUpdate_AP := desc !! 51 && desc !! 7;
              DescriptorUpdate_descaddr := {|
                AddressDescriptor_fault := default_FaultRecord;
                AddressDescriptor_memattrs := walkattrs;
                AddressDescriptor_paddress := {|
                  FullAddress_address := descaddr;
                  FullAddress_NS := of_bools [ns || negb secure]
                |};
                AddressDescriptor_vaddress := vaddress
              |}
            |};
            TLBRecord_CnP := of_bools [read_TTBR high s !! 0];
            TLBRecord_addrdesc := {|
              AddressDescriptor_fault := default_FaultRecord;
              AddressDescriptor_memattrs := memattrs;
              AddressDescriptor_paddress := {|
                FullAddress_address := outputaddr;
                FullAddress_NS := of_bools [desc !! 5 || ns || negb secure]
              |};
              AddressDescriptor_vaddress := vaddress
            |}
          |}
      else None
  end eq_refl).
specialize (startlevel_bounds high s).
change (read_params high s) with p.
clearbody a0. omega.

intro LARGE.
specialize (startlevel_largegrain_bounds high s p eq_refl LARGE).
clearbody a0.
omega.
Defined.

Require HexString.

Definition translate_address (vaddress : mword 64) (acctype : AccType) (iswrite : bool) (wasaligned : bool) (s : sequential_state regstate) : option TLBRecord :=
  match lookup_TLBRecord vaddress acctype s with
    None => None
  | Some r =>
      let top := read_AddrTop_EL0 vaddress (generic_eq acctype AccType_IFETCH) s in
      if valid_perms (TLBRecord_perms r) acctype iswrite s &&
         neq_vec (AddressDescriptor_physicaladdress (DescriptorUpdate_descaddr (TLBRecord_descupdate r))) (mword_of_int (HexString.to_Z "0x13000000")) && (* debug console hard-coded in this ASL model *)
         (implb (generic_eq (MemoryAttributes_typ (AddressDescriptor_memattrs (TLBRecord_addrdesc r))) MemType_Device)
          (wasaligned && (generic_eq acctype AccType_IFETCH || generic_eq acctype AccType_DCZVA)))
      then Some r else None
  end.

Definition read_descriptor (addr : mword 52) (s: sequential_state regstate) : option (mword 64) :=
  match read_mem_word addr 8 s with
    None => None
  | Some desc => Some (if read_bigendian s then reverse_endianness desc else desc)
  end.

Definition write_descriptor (addr : mword 52) (desc : mword 64) (s : sequential_state regstate) : sequential_state regstate :=
  let desc := if read_bigendian s then reverse_endianness desc else desc in
  write_mem_bytes (Z.to_nat (projT1 (uint addr))) 8 (mem_bytes_of_word desc) s.

Definition update_descriptor (descupd : DescriptorUpdate) (acctype : AccType) (iswrite : bool) (s : sequential_state regstate) : sequential_state regstate :=
  match read_descriptor (AddressDescriptor_physicaladdress (DescriptorUpdate_descaddr descupd)) s with
    None => s
  | Some desc =>
      let ap := DescriptorUpdate_AP descupd &&
                (iswrite || generic_eq acctype AccType_ATOMICRW || generic_eq acctype AccType_ORDEREDRW) &&
                generic_neq acctype AccType_AT && generic_neq acctype AccType_DC in
      let af := DescriptorUpdate_AF descupd in
      let desc := if af then setBit desc 10 true else desc in
      let desc := if ap then setBit desc 7 false else desc in
      let addr := AddressDescriptor_physicaladdress (DescriptorUpdate_descaddr descupd) in
      if af || ap
      then write_descriptor addr desc s
      else s
  end.

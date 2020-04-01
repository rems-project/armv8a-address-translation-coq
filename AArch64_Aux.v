Require Import Sail2_values Sail2_operators_mwords Word.
Require Import Sail2_prompt_monad Sail2_prompt.
Require Import Sail2_state_monad Sail2_state Sail2_state_lifting Hoare.
Require Import Sail2_state_monad_lemmas Sail2_state_lemmas.
Require Import Setoid Equivalence.
Require Import aarch64_types aarch64 AArch64_Trivia.

Import List.ListNotations.
Import Word.Notations.
Local Open Scope list_scope.
Local Open Scope word_scope.
Local Open Scope equiv_scope.
Local Open Scope Z.

(* TODO: move *)
Notation "v !! n" := (getBit v n) (at level 20).

Hint Transparent bits : PrePostE_specs.

(* TODO: produce an aarch64_lemmas file with this
  maybe needs a hint unfold, or possibly just use notation instead?
 *)
(*Definition liftS {A E} := @liftState _ _ A E register_accessors.*)
Notation "'liftS' m" := (liftState register_accessors m) (at level 10).

(*
(*<*)
(* Author: Thomas Bauereiss *)
theory AArch64_Aux
  imports AArch64_Trivia
begin
(*>*)

text \<open>Lemmas about auxiliary functions in the original model, e.g. for reading system registers or
reading and writing memory.\<close>

Lemma PrePostE_BigEndianReverse (*[PrePostE_atomI]:*) Regs Ex a (w : mword a) Q (E : Ex -> predS Regs) :
  List.In a [8; 16; 32; 64; 128] ->
  PrePostE (Q (reverse_endianness w)) (liftS (BigEndianReverse w)) Q E.
  using assms unfolding BigEndianReverse_def
  by (auto simp: liftState_simp)
*)

Lemma BigEndianReverse_8_word (*[simp]:*) (w : mword 8) :
  BigEndianReverse w = returnm w.
reflexivity.
Qed.

Definition UsingAArch64 s := weqb (ProcState_nRW (PSTATE (ss_regstate s))) $0.
Definition AArchConsistent s := UsingAArch64 s = true -> __highest_el_aarch32 (ss_regstate s) = false.

Lemma PrePostE_UsingAArch32 (*[PrePostE_atomI]:*) Q (E : ex exception -> predS _) :
  PrePostE (fun s => AArchConsistent s /\ Q (negb (UsingAArch64 s)) s)
           (liftS (UsingAArch32 tt)) Q E.
unfold AArchConsistent, UsingAArch64, UsingAArch32, HighestELUsingAArch32, bind0.
PrePostE_rewrite liftState.
simpl (negb (HaveAnyAArch32 tt)).
cbn iota.
PrePostE_rewrite state.

eapply PrePostE_strengthen_pre.

repeat PrePostE_step.

+ intros s [Consistent H].
  destruct (__highest_el_aarch32 (ss_regstate s)); simpl.
  * shatter_word (ProcState_nRW (PSTATE (ss_regstate s)) : word 1).
    destruct x. apply H. specialize (Consistent eq_refl). discriminate.
  * shatter_word (ProcState_nRW (PSTATE (ss_regstate s)) : word 1).
    destruct x; apply H.
Qed.

Hint Resolve PrePostE_UsingAArch32 : PrePostE_specs.

Lemma PrePostE_HaveEL (Q : bool -> predS regstate) E el :
  PrePostE (Q true) (liftS (HaveEL el)) Q E.
unfold HaveEL.
change (mword 2) with (word 2) in el.
shatter_word el.
destruct x, x0; 
apply PrePostE_returnS.
Qed.

Lemma PrePostE_HighestELUsingAArch32 (Q : bool -> predS regstate) E :
  PrePostE (fun s => Q (__highest_el_aarch32 (ss_regstate s)) s) (liftS (HighestELUsingAArch32 tt)) Q E.
unfold HighestELUsingAArch32, UsingAArch64.
PrePostE_rewrite liftState.
eapply PrePostE_strengthen_pre.
apply PrePostE_readS.
auto.
Qed.

Ltac PPE_apply id :=
lazymatch goal with
| |- PrePostE _ _ ?q ?e => apply id with (Q := q) (E := e)
end.

Hint Resolve PrePostE_HaveEL : PrePostE_specs.
Hint Resolve PrePostE_HighestELUsingAArch32 : PrePostE_specs.

Definition HasAArch32EL el s := __highest_el_aarch32 (ss_regstate s) || negb (eq_vec el EL3).

Ltac hammer_if :=
match goal with
| |- if ?x then _ else _ =>
  let t := eval compute in x in
  match t with
  | true => change x with t
  | false => change x with t
  | left _ => change x with t
  | right _ => change x with t
  | _ =>
    let H := fresh "EQ" in
    match type of x with
    | bool =>
      destruct x eqn:H;
      rewrite ?H in *
    | sumbool (_ = true) (_ = false) =>
      destruct x as [H | H] eqn:?;
      rewrite ?H in *
    | _ => destruct x eqn:?
    end
  end; cbv match beta
end.

Lemma PrePostE_HaveAArch32EL (Q : bool -> predS regstate) E el :
  PrePostE (fun s => Q (HasAArch32EL el s) s) (liftS (HaveAArch32EL el)) Q E.
unfold HasAArch32EL, HaveAArch32EL.
simpl (negb (HaveAnyAArch32 tt)).
simpl (HighestEL tt).
PrePostE_rewrite liftState.
PrePostE_rewrite state.

eapply PrePostE_strengthen_pre.
repeat (cbn [negb sumbool_of_bool fst snd projT1 andb orb]; PrePostE_step).

intros s H.
simpl.
hammer_if; auto.

compute in el.
shatter_word el.
destruct x, x0; auto.
Qed.
Hint Resolve PrePostE_HaveAArch32EL : PrePostE_specs.

(* Ugh, the undefined case is annoying.  Ultimately determines the translation regime (where it's called directly for EL3 and on EL2 in ELIsInHost).  Let's avoid this...

Definition is_ELUsingAArch32 el s :=
  HasAArch32EL el s &&
  (__highest_el_aarch32 (ss_regstate s) ||
   let notsecure := SCR_EL3 (ss_regstate s) !! 0 in
   let aarch32_below_el3 := SCR_EL3 (ss_regstate s) !! 10 in
   let aarch32_at_el1 := aarch32_below_el3 || (SCR_EL3 (ss_regstate s) !! 18 || notsecure && negb (HCR_EL2 (ss_regstate s) !! 31)) && negb (HCR_EL2 (ss_regstate s) !! 34 && HCR_EL2 (ss_regstate s) !! 27) in
   if weqb el EL0 && negb aarch32_at_el1
   then negb (UsingAArch64 s)
   else aarch32_below_el3 && weqb el EL3 || aarch32_at_el1 && (weqb el EL1 || weqb el EL0)).

Definition defined_ELUsingAArch32 el s :=
  negb (HasAArch32EL el s) || negb (__highest_el_aarch32 (ss_regstate s)) ||
  *)

Definition AlwaysAArch64 s :=
  __highest_el_aarch32 (ss_regstate s) = false /\
  access_vec_dec (SCR_EL3 (ss_regstate s)) 10 = B1 /\ (* RW - EL2 is aarch64 *)
  access_vec_dec (HCR_EL2 (ss_regstate s)) 31 = B1 /\ (* RW - EL1 is aarch64 *)
  UsingAArch64 s = true.

Lemma PrePostE_ELUsingAArch32 (*[PrePostE_atomI]:*) (Q : bool -> predS regstate) E el :
  PrePostE (fun s => el <> EL0 /\ AlwaysAArch64 s /\ Q false s) (liftS (ELUsingAArch32 el)) Q E.
repeat unfold ELUsingAArch32, IsSecureBelowEL3, aget_SCR_GEN, get_SCR,
       (*HighestELUsingAArch32,*) ELStateUsingAArch32, ELStateUsingAArch32K,
       HaveAArch32EL, HaveAnyAArch32.
repeat match goal with
| |- context [negb ?x] => simpl (negb x)
| |- context [__IMPDEF_boolean ?s] => let t := constr:(__IMPDEF_boolean s) in
                                      let t' := eval cbv in t in
                                      change t with t'
end.
simpl (HighestEL tt).
simpl (HaveVirtHostExt tt).
simpl (HaveSecureEL2Ext tt).
repeat match goal with
| |- context[HasArchVersion ?x] =>
  let t := eval cbn in (HasArchVersion x) in
  change (HasArchVersion x) with t
end.
cbv match beta.
repeat match goal with
| |- context [projT1 (build_ex ?t)] => change (projT1 (build_ex t)) with t
end.

PrePostE_rewrite liftState.
PrePostE_rewrite state.

simpl (sumbool_of_bool true).
cbv match beta.

eapply PrePostE_strengthen_pre.

repeat (cbn [negb sumbool_of_bool fst snd projT1 andb orb]; PrePostE_step).

intros s (notEL0 & (highest64 & el2_64 & el1_64 & current64) & q).

assert (notEL0' : eq_vec el EL0 = false). {
  simpl in notEL0. rewrite <- weqb_true_iff in notEL0.
  apply Bool.not_true_iff_false in notEL0.
  apply notEL0.
}

rewrite !notEL0'.

unfold UsingAArch64 in current64. 
apply weqb_true_iff in current64.
rewrite !highest64, !el2_64, !el1_64.
simpl (sumbool_of_bool true); simpl (sumbool_of_bool false); cbv match beta.

intros.
repeat (hammer_if; intros; auto).

compute in el.
shatter_word el.
destruct x, x0; compute in notEL0', EQ, EQ0, EQ1; discriminate.
Qed.

Hint Resolve PrePostE_ELUsingAArch32 : PrePostE_specs.

Lemma PrePostE_IsSecureBelowEL3 (*[PrePostE_atomI]:*) (Q : bool -> predS regstate) E :
  PrePostE (fun s => AlwaysAArch64 s /\ Q (eq_bit (access_vec_dec (SCR_EL3 (ss_regstate s)) 0) B0) s) (liftS (IsSecureBelowEL3 tt)) Q E.
unfold IsSecureBelowEL3, aget_SCR_GEN, get_SCR.
PrePostE_rewrite liftState.

let t := constr:(liftState register_accessors (HaveEL EL3)) in
let t' := eval compute in t in
change t with t'.

match goal with
| |- context[fun s => [(Value ?v, s)]] => change (fun s => [(Value v, s)]) with (returnS (Regs := regstate) (E := exception) v)
end.
PrePostE_rewrite state.

simpl (sumbool_of_bool true).
cbv match beta.

eapply PrePostE_strengthen_pre.
repeat PrePostE_step.

simpl.
intros s [[A1 [A2 [A3 A4]]] q].
rewrite A1.
simpl.
(*destruct (access_vec_dec (SCR_EL3 (ss_regstate s)) 0); auto.*)
unfold access_vec_dec, access_mword_dec in *.
destruct (getBit (get_word (SCR_EL3 (ss_regstate s))) (Z.to_nat 0)); auto.
Qed.

Hint Resolve PrePostE_IsSecureBelowEL3 : PrePostE_specs.

Lemma PrePostE_IsSecure (Q : bool -> predS regstate) E :
  PrePostE (fun s => AArchConsistent s /\ AlwaysAArch64 s /\ forall b, Q b s) (liftS (IsSecure tt)) Q E.
unfold IsSecure.

PrePostE_rewrite liftState.

let t := constr:(liftState register_accessors (HaveEL EL3)) in
let t' := eval compute in t in
change t with t'.

eapply PrePostE_strengthen_pre.
repeat PrePostE_step.
apply PrePostE_returnS.
apply PrePostE_returnS.
intros s [consistent [always64 q]].
simpl.
split; auto.
repeat (hammer_if; intros; try split; auto).
Qed.

Hint Resolve PrePostE_IsSecure : PrePostE_specs.

Ltac split_ands :=
  repeat match goal with
  | |- and _ _ => split
  | |- forall _, _ => intro
  end.

Lemma PrePostE_IsSecureEL2Enabled (Q : bool -> predS regstate) E :
  PrePostE (fun s => AArchConsistent s /\ AlwaysAArch64 s /\ forall b, Q b s) (liftS (IsSecureEL2Enabled tt)) Q E.
unfold IsSecureEL2Enabled.
PrePostE_rewrite liftState.
eapply PrePostE_strengthen_pre.
repeat PrePostE_step.

intros s [consistent [always64 q]].
simpl (negb _).
cbv match beta.
hammer_if. split_ands; auto. discriminate. discriminate.
hammer_if; auto.
Qed.

Hint Resolve PrePostE_IsSecureEL2Enabled : PrePostE_specs.

Definition read_EL s := ProcState_EL (PSTATE (ss_regstate s)).
(*lemmas [simp] = EL0_def EL1_def EL2_def EL3_def*)

Definition read_ELIsInHost (el : mword 2) (s : sequential_state regstate) : bool :=
  eq_bit (access_vec_dec (HCR_EL2 (ss_regstate s)) 34) B1 &&
  (eq_vec el EL2 || (eq_vec el EL0 && eq_bit (access_vec_dec (HCR_EL2 (ss_regstate s)) 27) B1)).

Lemma access_vec_dec_bit {n} (v : mword n) i :
  access_vec_dec v i = B0 \/ access_vec_dec v i = B1.
unfold access_vec_dec, access_mword_dec.
destruct (get_word v !! Z.to_nat i); tauto.
Qed.
Ltac destruct_access_vec_dec v i :=
  let H := fresh "H" in
  destruct (access_vec_dec_bit v i) as [H|H];
  rewrite H in *;
  clear H;
  try discriminate.

Lemma inv_eq_vec_B0 len (v : mword len) n b :
  eq_vec (vec_of_bits [access_vec_dec v n]) (vec_of_bits [B0]) = b ->
  access_vec_dec v n = if b then B0 else B1.
unfold access_vec_dec, access_mword_dec.
destruct (_ !! _); compute; intros; subst; reflexivity.
Qed.

Lemma inv_eq_vec_B1 len (v : mword len) n b :
  eq_vec (vec_of_bits [access_vec_dec v n]) (vec_of_bits [B1]) = b ->
  access_vec_dec v n = if b then B1 else B0.
unfold access_vec_dec, access_mword_dec.
destruct (_ !! _); compute; intros; subst; reflexivity.
Qed.

Lemma PrePostE_ELIsInHost (*[PrePostE_atomI]:*) (el : word 2) Q E :
  PrePostE (fun s => AArchConsistent s /\ AlwaysAArch64 s /\ eq_bit (access_vec_dec (SCR_EL3 (ss_regstate s)) 0) B1 = true
/\ Q (read_ELIsInHost el s) s) (liftS (ELIsInHost el)) Q E.
unfold ELIsInHost, read_ELIsInHost.
PrePostE_rewrite liftState.

eapply PrePostE_strengthen_pre.
repeat PrePostE_step.

intros s [consistent [always64 [notsecure q]]].
split; auto; split; auto.
intros.

repeat (hammer_if; intros; split_ands; auto).

all: repeat match goal with
| H : eq_vec (vec_of_bits [access_vec_dec ?v ?i]) _ = _ |- _ => destruct_access_vec_dec v i
| H : eq_bit (access_vec_dec ?v ?i) _ = _ |- _ => destruct_access_vec_dec v i
end.
all: try apply q.

all: destruct_access_vec_dec (HCR_EL2 (ss_regstate s)) 27; apply q.
Qed.

Hint Resolve PrePostE_ELIsInHost : PrePostE_specs.

Definition read_S1TranslationRegime (el : mword 2) (s : sequential_state regstate) : mword 2 :=
  if eq_vec el EL0 then (if read_ELIsInHost EL0 s then EL2 else EL1) else el.

Lemma read_S1TranslationRegime_eq_0_false (*[simp]:*) el s :
  eq_vec (read_S1TranslationRegime el s) EL0 = false.
unfold read_S1TranslationRegime.
destruct (eq_vec el EL0) eqn:EQ; auto.
destruct (read_ELIsInHost EL0 s); reflexivity.
Qed.

Lemma read_S1TranslationRegime_def_EL0 (*[simp]:*) s :
  read_EL s = EL0 ->  (* unnecessary? *)
  read_ELIsInHost EL0 s = false ->
  read_S1TranslationRegime EL0 s = EL1.
intros ReadEL ReadELIn.
unfold read_S1TranslationRegime.
rewrite ReadELIn.
reflexivity.
Qed.

Lemma PrePostE_S1TranslationRegime__0 (*[PrePostE_atomI]:*) el Q E :
  PrePostE (fun s => AArchConsistent s /\ AlwaysAArch64 s /\ eq_bit (access_vec_dec (SCR_EL3 (ss_regstate s)) 0) B1 = true /\ Q (read_S1TranslationRegime el s) s) (liftS (S1TranslationRegime__0 el)) Q E.
unfold S1TranslationRegime__0, read_S1TranslationRegime, get_SCR.
PrePostE_rewrite liftState.
eapply PrePostE_strengthen_pre.
repeat PrePostE_step.

intros s (consistent & always64 & notsecure & q).
hammer_if.
* apply Bool.negb_true_iff in EQ.
  rewrite EQ in q.
  apply q.
* split. discriminate.
  split; auto.
  hammer_if. hammer_if. do 3 (split; auto).
  apply Bool.negb_false_iff in EQ.
  rewrite EQ in q.
  apply eq_vec_true_iff in EQ.
  rewrite EQ.
  destruct (read_ELIsInHost EL0 s); apply q.
Qed.

Hint Resolve PrePostE_S1TranslationRegime__0 : PrePostE_specs.

Lemma PrePostE_S1TranslationRegime__1 (*[PrePostE_atomI]:*) Q E :
  PrePostE (fun s => AArchConsistent s /\ AlwaysAArch64 s /\ eq_bit (access_vec_dec (SCR_EL3 (ss_regstate s)) 0) B1 = true /\ Q (read_S1TranslationRegime (read_EL s) s) s) (liftS (S1TranslationRegime__1 tt)) Q E.
unfold S1TranslationRegime__1.
PrePostE_rewrite liftState.
eapply PrePostE_strengthen_pre.
repeat PrePostE_step.

intuition.
Qed.
Hint Resolve PrePostE_S1TranslationRegime__1 : PrePostE_specs.

Definition read_SCTLR (regime : mword 2) (s : sequential_state regstate) : mword 64 :=
  if eq_vec regime EL2 then SCTLR_EL2 (ss_regstate s) else
  if eq_vec regime EL3 then SCTLR_EL3 (ss_regstate s) else
  SCTLR_EL1 (ss_regstate s).

Lemma PrePostE_aget_SCTLR__0 (*[PrePostE_atomI]:*) regime Q (E : ex exception -> predS _) :
  PrePostE (fun s => if eq_vec regime EL0 then forall msg, E (Failure msg) s else Q (read_SCTLR regime s) s) (liftS (aget_SCTLR__0 regime)) Q E.
unfold aget_SCTLR__0, read_SCTLR, Unreachable.
PrePostE_rewrite liftState.
PrePostE_rewrite state.

eapply PrePostE_strengthen_pre.
repeat PrePostE_step.

simpl.
compute in regime.
shatter_word regime.
destruct x, x0; simpl; auto.
Qed.
Hint Resolve PrePostE_aget_SCTLR__0 : PrePostE_specs.

Lemma PrePostE_aget_SCTLR__1 (*[PrePostE_compositeI]:*) Q E :
  PrePostE (fun s => AArchConsistent s /\ AlwaysAArch64 s /\ eq_bit (access_vec_dec (SCR_EL3 (ss_regstate s)) 0) B1 = true /\ Q (read_SCTLR (read_S1TranslationRegime (read_EL s) s) s) s) (liftS (aget_SCTLR__1 tt)) Q E.
unfold aget_SCTLR__1.
PrePostE_rewrite liftState.
eapply PrePostE_strengthen_pre.
repeat PrePostE_step.

intuition.
rewrite read_S1TranslationRegime_eq_0_false.
assumption.
Qed.
Hint Resolve PrePostE_aget_SCTLR__1 : PrePostE_specs.

Definition read_bigendian (s : sequential_state regstate) : bool :=
  read_SCTLR (read_S1TranslationRegime (read_EL s) s) s !! 25.

Definition read_MAIR (regime : mword 2) (s : sequential_state regstate) : mword 64 :=
  if eq_vec regime $2 then MAIR_EL2 (ss_regstate s) else
  if eq_vec regime $3 then MAIR_EL3 (ss_regstate s) else
  MAIR_EL1 (ss_regstate s).

Lemma PrePostE_aget_MAIR__0 (*[PrePostE_atomI]:*) (regime : mword 2) Q (E : _ -> _ -> Prop) :
  PrePostE (fun s => if eq_vec regime $0 then forall msg, E (Failure msg) s else Q (read_MAIR regime s) s) (liftS (aget_MAIR__0 regime)) Q E.
unfold aget_MAIR__0, read_MAIR, Unreachable.
PrePostE_rewrite liftState.
eapply PrePostE_strengthen_pre.
repeat PrePostE_step.

intros.
cbv match beta.
compute in regime.
shatter_word regime.
destruct x, x0; apply H.
Qed.
Hint Resolve PrePostE_aget_MAIR__0 : PrePostE_specs.

Lemma PrePostE_aget_MAIR__1 (*[PrePostE_atomI]:*) Q E :
  PrePostE (fun s => AArchConsistent s /\ AlwaysAArch64 s /\ eq_bit (access_vec_dec (SCR_EL3 (ss_regstate s)) 0) B1 = true /\ Q (read_MAIR (read_S1TranslationRegime (read_EL s) s) s) s) (liftS (aget_MAIR__1 tt)) Q E.
unfold aget_MAIR__1.
PrePostE_rewrite liftState.
eapply PrePostE_strengthen_pre.
repeat PrePostE_step.

intuition.
rewrite read_S1TranslationRegime_eq_0_false.
assumption.
Qed.
Hint Resolve PrePostE_aget_MAIR__1 : PrePostE_specs.

Definition read_mem_word {addrsize : Z} (addr : mword addrsize) (len : Z) `{ArithFact (len >=? 0)} (s : sequential_state regstate) : option (mword (8 * len)) :=
  option_bind (get_mem_bytes (wordToNat (get_word addr)) (Z.to_nat len) s)
              (fun '(bytes,_) => of_bits (bits_of_mem_bytes bytes)).

Lemma PrePostE_read_ram (*[PrePostE_atomI]:*) addrsize (addr : mword addrsize) len `{ArithFact (len >=? 0)} hexRAM Q (E : ex exception -> _ -> Prop) :
  PrePostE (fun s => (exists w, read_mem_word addr len s = Some w /\ Q w s)) (liftS (aarch64_extras.read_ram addrsize len hexRAM addr)) Q E.
unfold aarch64_extras.read_ram.
PrePostE_rewrite liftState.
unfold read_memS, read_memtS, read_memt_bytesS.

eapply PrePostE_strengthen_pre.
repeat PrePostE_step.

intros s [w [EQ q]].
unfold read_mem_word in EQ.
destruct (get_mem_bytes # (get_word addr) (Z.to_nat len) s) as [[bytes t]|]; try discriminate.
cbv [option_bind] in EQ.
simpl in EQ. simpl.
match goal with |- context[just_list ?v] => destruct (just_list v) end; try discriminate.
simpl in EQ |- *.
injection EQ.
replace_ArithFact_proof.
intro EQ'.
rewrite EQ'.
apply q.
Qed.
Hint Resolve PrePostE_read_ram : PrePostE_specs.

Definition AddressDescriptor_physicaladdress d := FullAddress_address (AddressDescriptor_paddress d).

Definition read_CNTControlBase s := __CNTControlBase (ss_regstate s).

Lemma PrePostE_impossible {A} (m : monadS _ A _) Q (E : ex exception -> predS regstate) :
  PrePostE (fun _ => False) m Q E.
intros s [].
Qed.

Lemma read_mem_word_addrextend addrsize (addr : mword addrsize) len (H : ArithFact (len >=? 0)) m (H' : ArithFact (m >=? addrsize)) s :
  read_mem_word addr len s = read_mem_word (zero_extend addr m) len s.
unfold read_mem_word, zero_extend.
f_equal.
* f_equal.
  unfold extz_vec.
  etransitivity.
  - symmetry.
    apply (wordToNat_zext (get_word addr) (Z.to_nat (m - addrsize))).
  - apply EqdepFacts.f_eq_dep_non_dep.
    apply EqdepFacts.eq_dep_sym.
    apply Mword.get_cast_to_mword.
* replace_ArithFact_proof. reflexivity. 
Qed.

Local Open Scope nat.
Lemma genlist_sum A (f : nat -> A) m n :
  genlist f (m + n) = genlist f m ++ genlist (fun i => f (m+i)) n.
unfold genlist.
generalize (@nil A) at 1 3.
induction n.
* simpl.
  rewrite Nat.add_0_r.
  induction m; auto; intros.
  simpl. rewrite IHm. rewrite (IHm [f m]).
  rewrite <- List.app_assoc.
  reflexivity.
* rewrite Nat.add_succ_r. simpl.
  auto.
Qed.

Lemma genlist_length A (f : nat -> A) n :
  List.length (genlist f n) = n.
unfold genlist.
enough (H:forall acc, List.length (genlist_acc f n acc) = List.length acc + n) by apply H.
induction n.
* intros. rewrite Nat.add_comm.
  reflexivity.
* intros.
  simpl.
  rewrite IHn.
  rewrite Nat.add_succ_r.
  reflexivity.
Qed.

Lemma just_list_length A (l : list (option A)) l' :
  just_list l = Some l' ->
  List.length l' = List.length l.
revert l'. induction l.
* intros ? [=].
  subst.
  reflexivity.
* destruct a; try discriminate.
  simpl.
  destruct (just_list l); try discriminate.
  intros ? [=]. subst.
  simpl. rewrite IHl; reflexivity.
Qed.

Local Close Scope nat.

Lemma just_list_app A (l1 l2 : list (option A)) l :
  just_list (l1 ++ l2) = Some l ->
  exists l1' l2', just_list l1 = Some l1' /\ just_list l2 = Some l2' /\ l = l1' ++ l2'.
revert l.
induction l1.
* intros l H.
  exists [], l.
  auto.
* intro l.
  destruct a.
  + simpl.
    destruct (just_list (l1 ++ l2)) eqn:J; try discriminate.
    intros [=].
    subst.
    destruct (IHl1 l0 eq_refl) as (l1' & l2' & H1 & H2 & H3).
    exists (a :: l1'), l2'.
    rewrite H1, H2, H3.
    auto.
  + discriminate.
Qed.

Add Parametric Morphism {A : Type} : (@genlist A)
  with signature equiv ==> eq ==> eq as genlist_morphism.
intros f g EQ n.
unfold genlist.
generalize (@nil A).
induction n.
reflexivity.
intro.
simpl.
rewrite IHn.
f_equal.
f_equal.
apply EQ.
Qed.

Lemma get_mem_bytes_adj addr m n (s : sequential_state regstate) l b :
  get_mem_bytes addr (m + n) s = Some (l,b) ->
  exists l1 l2 b1 b2,
    get_mem_bytes addr m s = Some (l1, b1) /\
    get_mem_bytes (addr + m) n s = Some (l2, b2) /\
    l = l1 ++ l2.
cbv delta [get_mem_bytes] beta.
rewrite genlist_sum.
repeat match goal with |- ((let x := ?t in @?P x) = ?r) -> ?c =>
  set (x := t);
  change ((P x = r) -> c); cbv beta
 end.
destruct (just_list (map (read_byte s) addrs)) eqn:MAP; try discriminate.
cbv beta iota delta [option_map].
intros [=].
subst.
match eval unfold addrs in addrs with ?a1 ++ ?a2 => set (addrs1 := a1) in *; set (addrs2 := a2) in * end.
change addrs with (addrs1 ++ addrs2) in MAP.
rewrite List.map_app in MAP.
apply just_list_app in MAP.
destruct MAP as (l1 & l2 & JL1 & JL2 & ->).
exists l1, l2. do 2 eexists.
match goal with
  |- ((let x := _ in let y := _ in let z := _ in @?P x y z) = ?r1 /\ ?r2) =>
  change (P addrs1 read_byte read_tag = r1 /\ r2) end.
cbv beta.
change NatMap.key with nat.
rewrite JL1.
split. reflexivity.
match goal with |- ((let x := ?a in _) = _) /\ _ => replace a with addrs2 end.
match goal with
  |- ((let x := _ in let y := _ in let z := _ in @?P x y z) = ?r1 /\ ?r2) =>
  change (P addrs2 read_byte read_tag = r1 /\ r2) end.
cbv beta.
rewrite JL2.
split; reflexivity.
unfold addrs2.
apply genlist_morphism; auto.
intro.
apply Nat.add_assoc.
Qed.

Lemma get_mem_bytes_length Regs addr len (s : sequential_state Regs) l b :
  get_mem_bytes addr len s = Some (l,b) ->
  List.length l = len.
unfold get_mem_bytes.
match goal with |- context[just_list ?l] => destruct (just_list l) eqn:JL; try discriminate end.
simpl.
intros [=]. subst.
rewrite (just_list_length _ _ _ JL).
rewrite List.map_length.
rewrite genlist_length.
reflexivity.
Qed.

Require Mword.

Lemma combine_eq n (v : word n) n' (v' : word n') m (w : word m) m' (w' : word m') :
  EqdepFacts.eq_dep _ word _ v _ v' ->
  EqdepFacts.eq_dep _ word _ w _ w' ->
  EqdepFacts.eq_dep _ word _ (combine v w) _ (combine v' w').
intros H1 H2.
destruct H1, H2.
constructor.
Qed.

Lemma wordFromBitlist_app l1 l2 :
  EqdepFacts.eq_dep _ word _ (wordFromBitlist (l1 ++ l2)) _ (combine (wordFromBitlist l2) (wordFromBitlist l1)).
unfold wordFromBitlist.
eapply EqdepFacts.eq_dep_trans. apply Mword.nat_cast_eq_dep.
rewrite (rev_app_distr l1 l2).
apply EqdepFacts.eq_dep_sym.
eapply EqdepFacts.eq_dep_trans.
eapply combine_eq; apply Mword.nat_cast_eq_dep.
induction (rev l2).
* simpl. constructor.
* simpl.
  destruct IHl.
  constructor.
Qed.

Lemma wordFromBitlist_app' l1 l2 :
 forall (E : _),
 wordFromBitlist (l1 ++ l2) = eq_rect _ _ (combine (wordFromBitlist l2) (wordFromBitlist l1)) _ E.
intro.
apply Eqdep_dec.eq_dep_eq_dec. apply Nat.eq_dec.
eapply EqdepFacts.eq_dep_trans.
apply wordFromBitlist_app.
eapply EqdepFacts.eq_dep_sym.
apply Mword.eq_rect_eq_dep.
Qed.

Lemma fit_bbv_word_eq_rect n m o E w :
  @fit_bbv_word n m (eq_rect o _ w _ E) = fit_bbv_word w.
subst.
reflexivity.
Qed.

Lemma nat_diff_eq T n ltf eqf gtf :
  @nat_diff T n n ltf eqf gtf = eqf.
revert dependent T.
induction n.
* reflexivity.
* simpl.
  intros.
  apply (IHn (fun x => T (S x))).
Qed.

Lemma fit_eq_word n m v w :
  EqdepFacts.eq_dep _ word n v m w ->
  fit_bbv_word v = w.
intro H.
unfold fit_bbv_word.
destruct H.
rewrite nat_diff_eq.
constructor.
Qed.

Lemma cast_T_mword p (w : mword (Z.pos p)) E :
   @cast_T mword (Z.of_nat (Pos.to_nat p)) (Z.pos p) (@mword_of_nat (Pos.to_nat p) w) E = w.
apply Eqdep_dec.eq_dep_eq_dec. apply Z.eq_dec.
eapply EqdepFacts.eq_dep_trans.
apply Mword.cast_T_eq_dep.
apply Mword.word_mword_eq_dep.
eapply EqdepFacts.eq_dep_trans. apply Mword.get_word_mword_of_nat.
constructor.
Qed.

Lemma concat_0_l n (o : mword 0) (w : mword n) :
  concat_vec o w = w.
simpl in o.
shatter_word o.
unfold concat_vec.
apply Eqdep_dec.eq_dep_eq_dec. apply Z.eq_dec.
apply Mword.word_mword_eq_dep.
eapply EqdepFacts.eq_dep_trans.
apply Mword.get_word_cast_to_mword.
rewrite combine_WO.
eapply EqdepFacts.eq_dep_trans.
apply Mword.eq_rect_eq_dep.
constructor.
Qed.

Lemma to_word_combine m n (v : word (Z.to_nat m)) (w : word (Z.to_nat n)) H1 H2 H3 :
  to_word H1 (fit_bbv_word (combine v w)) = concat_vec (to_word H2 w) (to_word H3 v).
destruct m.
* simpl in v. shatter_word v.
  unfold concat_vec.
  simpl.
  destruct n.
  + simpl in w. shatter_word w.
    reflexivity.
  + simpl.
    apply fit_eq_word.
    rewrite cast_T_mword.
    constructor.
  + exfalso. compute in H2. discriminate.
* destruct n.
  + simpl in w. shatter_word w. simpl.
    apply fit_eq_word.
    rewrite concat_0_l.
    rewrite combine_WO.
    eapply EqdepFacts.eq_dep_trans.
    apply Mword.eq_rect_eq_dep.
    constructor.
  + simpl.
    apply fit_eq_word.
    assert (E : (Pos.to_nat p + Pos.to_nat p0)%nat = Pos.to_nat (p + p0))
      by auto using Pos2Nat.inj_add.
    eapply EqdepFacts.eq_dep_trans.
    apply EqdepFacts.eq_dep_sym.
    apply Mword.eq_rect_eq_dep with (E := E).
    apply EqdepFacts.eq_dep_sym.
    unfold concat_vec.
    repeat match goal with |- context[Pos.to_nat ?p] => change (Pos.to_nat p) with (Z.to_nat (Z.pos p)) end.
    match goal with |- EqdepFacts.eq_dep _ _ _ ?x _ _ => change x with (get_word x) end.
    match goal with |- EqdepFacts.eq_dep _ _ _ _ _ ?x => change x with (get_word (x : mword (Z.pos (p + p0)))) end.
    eapply EqdepFacts.eq_dep_trans.
    apply Mword.get_word_cast_to_mword.
    apply EqdepFacts.eq_dep_sym.
    apply Mword.eq_rect_eq_dep.
  + exfalso. compute in H2. discriminate.
* compute in H3. discriminate.
Qed.

Lemma combine_dep_cong m n w v m' n' w' v' :
  EqdepFacts.eq_dep nat word m w m' w' ->
  EqdepFacts.eq_dep nat word n v n' v' ->
  EqdepFacts.eq_dep nat word (m+n)%nat (combine w v) (m'+n')%nat (combine w' v').
intros [] [].
constructor.
Qed.

Lemma fit_bbv_word_eq_dep m n w :
  m = n ->
  EqdepFacts.eq_dep nat word _ (@fit_bbv_word m n w) _ w.
intro; subst.
unfold fit_bbv_word.
rewrite nat_diff_eq.
constructor.
Qed.

Lemma of_bits_app m n bits1 bits2 (w : mword (m + n)) H :
  length_list bits1 = m ->
  length_list bits2 = n ->
  @of_bits _ (@mword_Bitvector _ H) (bits1 ++ bits2) = Some w ->
  exists H1 H2 (w1 : mword m) (w2 : mword n),
    @of_bits _ (@mword_Bitvector _ H1) bits1 = Some w1 /\
    @of_bits _ (@mword_Bitvector _ H2) bits2 = Some w2 /\
    w = concat_vec w1 w2.
intros L1 L2.
assert (M:m >= 0) by
  (unfold length_list in L1; rewrite <- L1; auto using Nat2Z.is_nonneg with zarith).
assert (N:n >= 0) by
  (unfold length_list in L2; rewrite <- L2; auto using Nat2Z.is_nonneg with zarith).
simpl.
match goal with |- context[just_list ?l] => destruct (just_list l) eqn:JL end; try discriminate.
rewrite List.map_app in JL.
apply just_list_app in JL.
destruct JL as (l1' & l2' & JL1 & JL2 & ->).
simpl.
intros [= EQ].
rewrite JL1, JL2.
simpl.
apply Z_geb_ge in M as M'.
apply Z_geb_ge in N as N'.
exists (Build_ArithFactP _ M'), (Build_ArithFactP _ N').
do 2 eexists.
split. reflexivity.
split. reflexivity.

unfold length_list in L1, L2.
assert (Lm: List.length l1' = Z.to_nat m). {
  rewrite (just_list_length _ _ _ JL1).
  rewrite List.map_length.
  rewrite <- L1.
  rewrite Nat2Z.id.
  reflexivity.
}
assert (Ln: List.length l2' = Z.to_nat n). {
  rewrite (just_list_length _ _ _ JL2).
  rewrite List.map_length.
  rewrite <- L2.
  rewrite Nat2Z.id.
  reflexivity.
}

rewrite <- EQ.
assert (E : (Datatypes.length l2' + Datatypes.length l1')%nat = Datatypes.length (l1' ++ l2')).
{ rewrite Nat.add_comm. symmetry. apply app_length. }
rewrite wordFromBitlist_app' with (E := E).
rewrite fit_bbv_word_eq_rect.
match goal with |- @to_word _ ?H1 _ = _ => set (F := H1) end.
rewrite <- to_word_combine with (H1 := F).
f_equal.
apply Eqdep_dec.eq_dep_eq_dec. apply Nat.eq_dec.
eapply EqdepFacts.eq_dep_trans. apply fit_bbv_word_eq_dep. rewrite Lm, Ln. rewrite Z2Nat.inj_add;
omega.
apply EqdepFacts.eq_dep_sym.
eapply EqdepFacts.eq_dep_trans. apply fit_bbv_word_eq_dep. rewrite Z2Nat.inj_add; omega.
apply combine_dep_cong; apply fit_bbv_word_eq_dep; auto.
Qed.

Lemma of_mem_bytes_app n b1 b2 (w : mword (n + n)) H :
  length_list (bits_of_mem_bytes b1) = n ->
  length_list (bits_of_mem_bytes b2) = n ->
  @of_bits _ (@mword_Bitvector _ H) (bits_of_mem_bytes (b2 ++ b1)) = Some w ->
  exists H1 H2 (w1 w2 : mword n),
    @of_bits _ (@mword_Bitvector _ H1) (bits_of_mem_bytes b1) = Some w1 /\
    @of_bits _ (@mword_Bitvector _ H2) (bits_of_mem_bytes b2) = Some w2 /\
    w = concat_vec w1 w2.
unfold bits_of_mem_bytes, bits_of_bytes.
rewrite List.rev_app_distr, List.map_app, List.concat_app.
apply of_bits_app.
Qed.

(* This doesn't work because the address might wrap around.  In any case, it appears
   to be unnecessary as aget__Mem is only used on smaller sizes.
Lemma read_mem_word_128 addrsize (addr : mword addrsize) (w w0 : mword 128) s :
  read_mem_word addr 16 s = Some w ->
  exists w1 w2,
  read_mem_word addr 8 s = Some w1 /\
  read_mem_word (add_vec_int addr 8) 8 s = Some w2 /\
  w = set_slice 128 64 (set_slice 128 64 w0 0 w1) 64 w2.
unfold read_mem_word.
destruct (get_mem_bytes # (get_word addr) (Z.to_nat 16)) as [[bytes b] | ] eqn:GET; try discriminate.
intros BYTES.
apply (get_mem_bytes_adj _ 8 8) in GET.
destruct GET as (bytes1 & bytes2 & b1 & b2 & GET1 & GET2 & ->).
cbv beta iota delta [option_bind] in BYTES.
change (8 * 16) with (8 * 8 + 8 * 8) in BYTES.
apply of_mem_bytes_app in BYTES.
destruct BYTES as (F1 & F2 & w1 & w2 & BYTES1 & BYTES2 & ->).
exists w1, w2.
replace_ArithFact_proof.
change (Z.to_nat 8) with 8%nat.
*)

Lemma sumbool_of_false (b : bool) (P : {b = true} + {b = false} -> Prop) (E : b = false) :
  P (right E) -> P (sumbool_of_bool b).
subst.
intro H. apply H.
Qed.

Lemma concat_zeros_extend m n (w : mword m) `{ArithFact (n >=? 0)} :
  concat_vec (zeros n) w = zero_extend w (n + m).
unfold concat_vec, zeros, zero_extend, extz_vec.
apply Eqdep_dec.eq_dep_eq_dec. apply Z.eq_dec.
apply Mword.word_mword_eq_dep.
eapply EqdepFacts.eq_dep_trans.
apply Mword.get_word_cast_to_mword.
apply EqdepFacts.eq_dep_sym.
eapply EqdepFacts.eq_dep_trans.
apply Mword.get_word_cast_to_mword.
unfold zext.
apply combine_dep_cong.
* constructor.
* apply EqdepFacts.eq_dep_sym.
  eapply EqdepFacts.eq_dep_trans.
  apply Mword.get_word_cast_to_mword.
  rewrite Z.add_simpl_r.
  constructor.
Qed.

(* Don't do len = 16, it doesn't appear to be used and seems to have an address wraparound
   corner case. (Could maybe use aligned to get around this?  But don't seem to need aligned
   anyway...) *)
Lemma PrePostE_aget__Mem (*[PrePostE_atomI]:*) len `{ArithFact (len >=? 0)} desc accdesc Q E :
  PrePostE (fun s => List.In len [1; 2; 4; 8] /\ aligned (AddressDescriptor_physicaladdress desc) len /\
(eq_vec (read_CNTControlBase s) $0 || neq_vec (and_vec (AddressDescriptor_physicaladdress desc) __CNTControlMask) (read_CNTControlBase s) = true) /\
                 (match read_mem_word (AddressDescriptor_physicaladdress desc) len s with Some w => Q w s | None => False end))
            (liftS (aget__Mem desc len accdesc)) Q E.
unfold aget__Mem, Align__1, Align__0, __ReadMemory, __ReadRAM, ZeroExtend__1, ZeroExtend__0, undefined_FaultRecord, aarch64_extras.undefined_int, undefined_FullAddress, undefined_AccType, undefined_Fault, aarch64_extras.internal_pick.

unfold __trickbox_enabled.
rewrite !Bool.andb_false_l.

PrePostE_rewrite liftState.
PrePostE_rewrite state.

eapply PrePostE_strengthen_pre.
repeat PrePostE_step.
* apply PrePostE_impossible.
* apply PrePostE_impossible.
* apply PrePostE_impossible.
* apply PrePostE_impossible.

* intros s (Len & Aligned & NotCNT & q).
  simpl (sumbool_of_bool false).
  cbv match beta.

  intro.
  simpl (projT1 (build_ex _)).
  match goal with |- let (x,_) := ?t in _ =>
                  destruct t as [[|] ?] eqn:CNTBase
  end.
  + intro.
    apply Bool.orb_true_iff in NotCNT.
    destruct NotCNT as [NoCNT | NotCNT].
    - apply eq_vec_true_iff in NoCNT.
      unfold read_CNTControlBase in NoCNT.
      rewrite NoCNT in CNTBase.
      simpl in CNTBase.
      discriminate.
    - unfold read_CNTControlBase, AddressDescriptor_physicaladdress, neq_vec in NotCNT.
      rewrite Bool.negb_true_iff in NotCNT.
      simpl (projT1 (existT _ _ _)).
      simpl in NotCNT.
      apply sumbool_of_false with (E := NotCNT).
      intros.
      assert (Len16 : len =? 16 = false). { apply Z.eqb_neq. compute in Len. omega. }
      apply sumbool_of_false with (E := Len16).
      hammer_if.

      destruct (read_mem_word (AddressDescriptor_physicaladdress desc) len s) as [read |] eqn:Read_mem.
      2: destruct q.
      intro.
      exists read.
      unfold AddressDescriptor_physicaladdress in Read_mem.
      simpl. 
      change (id (wzero (Pos.to_nat 4))) with (zeros 4).
      rewrite concat_zeros_extend.
      rewrite <- read_mem_word_addrextend.
      revert Read_mem.
      replace_ArithFact_proof.
      split; auto.

  + intro.
    simpl (projT1 (existT _ _ _)).
    simpl.
    intro.
    assert (Len16 : len =? 16 = false). { apply Z.eqb_neq. compute in Len. omega. }
    apply sumbool_of_false with (E := Len16).
    intro.

      destruct (read_mem_word (AddressDescriptor_physicaladdress desc) len s) as [read |] eqn:Read_mem.
      2: destruct q.
      exists read.
      unfold AddressDescriptor_physicaladdress in Read_mem.
      simpl. 
      change (id (wzero (Pos.to_nat 4))) with (zeros 4).
      rewrite concat_zeros_extend.
      rewrite <- read_mem_word_addrextend.
      revert Read_mem.
      replace_ArithFact_proof.
      split; auto.
Qed.
Hint Resolve PrePostE_aget__Mem : PrePostE_specs.

Definition write_mem_bytes (addr : nat) (len : Z) (bytes : list (list bitU)) (s : sequential_state regstate) : sequential_state regstate :=
  put_mem_bytes addr (Z.to_nat len) bytes B0 (* tag *) s.
(*     s\<lparr>memstate := foldl (\<lambda>mem (addr, b). mem(addr := Some b))
                         (memstate s)
                         (zip (index_list addr (addr + len - 1) 1) bytes)\<rparr>*)

Lemma PrePostE_write_ram addrlen len hexRAM addr w Q (E : ex exception -> predS _) :
  PrePostE (fun s => match mem_bytes_of_bits w with
                     | None => forall msg, E (Failure msg) s
                     | Some bytes => Q tt (write_mem_bytes (wordToNat (get_word addr)) len bytes s)
                     end)
            (liftS (aarch64_extras.write_ram addrlen len hexRAM addr w)) Q E.
unfold aarch64_extras.write_ram.
PrePostE_rewrite liftState.
PrePostE_rewrite state.
unfold write_memS, write_memtS.
destruct (mem_bytes_of_bits w).
* unfold write_mem_bytes, write_memt_bytesS, updateS.
  intros s pre. simpl.
  intros r s' [EQ | []]. injection EQ as; subst.
  apply pre.
* intros s pre. simpl.
  intros r s' [EQ | []]. injection EQ as; subst.
  apply pre.
Qed.
Hint Resolve PrePostE_write_ram : PrePostE_specs.

(*
lemmas undefined_defs = undefined_MemoryAttributes_def undefined_MemType_def
  undefined_DeviceType_def undefined_MemAttrHints_def undefined_Permissions_def
  undefined_Constraint_def undefined_int_def undefined_Fault_def undefined_FaultRecord_def
  undefined_FullAddress_def undefined_DescriptorUpdate_def undefined_AccessDescriptor_def

lemma PrePostE_internal_pickS_any[PrePostE_atomI]:
  "xs \<noteq> [] \<Longrightarrow> PrePostE (\<lambda>s. \<forall>x. Q x s) (internal_pickS xs) Q E"
  by (PrePost atomI: PrePostE_internal_pick)

lemma PrePostE_undefined_AccType_any[PrePostE_atomI]:
  "PrePostE (\<lambda>s. \<forall>r. Q r s) (liftS (undefined_AccType unit)) Q E"
  by (strong_cong_simp add: undefined_AccType_def) PrePost

lemma PrePostE_undefined_AddressDescriptor_any[PrePostE_atomI]:
  "PrePostE (\<lambda>s. \<forall>r. Q r s) (liftS (undefined_AddressDescriptor unit)) Q E"
  by (strong_cong_simp add: undefined_AddressDescriptor_def undefined_defs) PrePost

lemma PrePostE_undefined_TLBRecord_any[PrePostE_atomI]:
  "PrePostE (\<lambda>s. \<forall>r. Q r s) (liftS (undefined_TLBRecord unit)) Q E"
  by (strong_cong_simp add: undefined_TLBRecord_def undefined_defs) PrePost

lemma PrePostE_AArch64_CreateFaultRecord[PrePostE_atomI]:
  "PrePostE (\<lambda>s. Q (CreateFaultRecord typ1 ipaddress level acctype write1 extflag errortype secondstage s2fs1walk) s)
            (liftS (AArch64_CreateFaultRecord typ1 ipaddress level acctype write1 extflag errortype secondstage s2fs1walk))
            Q E"
  by (strong_cong_simp add: AArch64_CreateFaultRecord_def undefined_defs) PrePost

lemmas PrePostE_PSTATE_EL_0 = PrePostE_readS_pred[where f = "\<lambda>s. PSTATE (regstate s)", THEN PrePostE_bindS_left_pred_simp, where C = "\<lambda>a. ProcState_EL a = 0"]
lemmas PrePostE_PSTATE_EL_01 = PrePostE_readS_pred[where f = "\<lambda>s. PSTATE (regstate s)", THEN PrePostE_bindS_left_pred_simp, where C = "\<lambda>a. ProcState_EL a = 0 \<or> ProcState_EL a = 1"]

definition NonSecure_EL01 :: "regstate sequential_state \<Rightarrow> bool" where
  "NonSecure_EL01 s \<equiv> (read_EL s = 0 \<or> read_EL s = 1) \<and> SCR_EL3 (regstate s) !! 0 \<and> \<not> read_ELIsInHost (read_EL s) s"

lemma PrePostE_IsSecure[PrePostE_atomI]:
  "PrePostE (\<lambda>s. UsingAArch64 s \<and> Q (read_EL s = 3 \<or> \<not>(SCR_EL3 (regstate s) !! 0)) s)
            (liftS (IsSecure unit)) Q E"
  by (strong_cong_simp add: IsSecure_def) PrePostAuto

lemma PrePostE_HasS2Translation[PrePostE_atomI]:
  "PrePostE (\<lambda>s. UsingAArch64 s \<and> Q (NonSecure_EL01 s) s) (liftS (HasS2Translation unit)) Q E"
  by (strong_cong_simp add: HasS2Translation_def IsInHost_def NonSecure_EL01_def)
     (PrePost simp: app_if_distrib; auto)

lemma PrePostE_HasS2Translation_True:
  "PrePostE (\<lambda>s. UsingAArch64 s \<and> NonSecure_EL01 s \<and> Q s) (liftS (HasS2Translation unit)) (\<lambda>r s. r = True \<and> Q s) E"
  by (PrePostAuto )

lemma PrePostE_liftRS_HasS2Translation_True:
  "PrePostE (\<lambda>s. UsingAArch64 s \<and> NonSecure_EL01 s \<and> Q s) (liftRS (liftS (HasS2Translation unit))) (\<lambda>r s. r = True \<and> Q s) E"
  by (PrePostAuto)

lemmas PrePostE_bindS_HasS2Translation_True =
  PrePostE_bindS_left_const_simp[OF PrePostE_HasS2Translation_True]
  PrePostE_bindS_left_const_simp[OF PrePostE_liftRS_HasS2Translation_True]

abbreviation S2TranslationEnabled :: "regstate sequential_state \<Rightarrow> bool" where
  "S2TranslationEnabled s \<equiv> HCR_EL2 (regstate s) !! 0 \<or> HCR_EL2 (regstate s) !! 12"

lemmas PrePostE_HCR_EL2_s2disabled =
  PrePostE_readS_pred[where f = "\<lambda>s. HCR_EL2 (regstate s)", THEN PrePostE_bindS_left_pred_simp,
                      where C = "\<lambda>w. \<not>(w !! 0) \<and> \<not>(w !! 12)"]

lemma PrePostE_AArch64_SecondStageWalk_disabled:
  "PrePostE (\<lambda>s. NonSecure_EL01 s \<and> \<not>(S2TranslationEnabled s) \<and> UsingAArch64 s \<and> Q descaddr s)
            (liftS (AArch64_SecondStageWalk descaddr vaddress acctype iswrite sz hwupdatewalk)) Q E"
  by (strong_cong_simp add: AArch64_SecondStageWalk_def AArch64_SecondStageTranslate_def IsInHost_def undefined_defs)
     (PrePost compositeI: PrePostE_HCR_EL2_s2disabled PrePostE_bindS_HasS2Translation_True or_boolS_returnS_if)

lemma PrePostE_AArch64_TranslationFault[PrePostE_atomI]:
  "PrePostE (\<lambda>s. Q (CreateFaultRecord Fault_Translation ipaddress level acctype iswrite 0 0 secondstage s2fs1walk) s)
            (liftS (AArch64_TranslationFault ipaddress level acctype iswrite secondstage s2fs1walk)) Q E"
  by (strong_cong_simp add: AArch64_TranslationFault_def) PrePost

lemma PrePostE_AArch64_AddressSizeFault[PrePostE_atomI]:
  "PrePostE (\<lambda>s. Q (CreateFaultRecord Fault_AddressSize ipaddress level acctype iswrite 0 0 secondstage s2fs1walk) s)
            (liftS (AArch64_AddressSizeFault ipaddress level acctype iswrite secondstage s2fs1walk)) Q E"
  by (strong_cong_simp add: AArch64_AddressSizeFault_def) PrePost

lemma PrePostE_AArch64_AccessFlagFault[PrePostE_atomI]:
  "PrePostE (\<lambda>s. Q (CreateFaultRecord Fault_AccessFlag ipaddress level acctype iswrite 0 0 secondstage s2fs1walk) s)
            (liftS (AArch64_AccessFlagFault ipaddress level acctype iswrite secondstage s2fs1walk)) Q E"
  by (strong_cong_simp add: AArch64_AccessFlagFault_def) PrePost

lemma PrePostE_AArch64_NoFault[PrePostE_atomI]:
  "PrePostE (\<lambda>s. \<forall>iswrite. Q (CreateFaultRecord Fault_None 0 0 AccType_NORMAL iswrite 0 0 False False) s) (liftS (AArch64_NoFault unit)) Q E"
  by (strong_cong_simp add: AArch64_NoFault_def undefined_int_def) PrePost

lemma ZeroExtend_slice_append_simp:
  shows "ZeroExtend_slice_append outlen (xs :: 'x::len word) i l (ys :: 'y::len word) =
         return ((((ucast (xs AND slice_mask outlen i l >> nat i)) << LENGTH('y)) OR ucast ys) :: 'o::len word)"
  by (auto simp: ZeroExtend_slice_append_def ZeroExtend__1_def ZeroExtend__0_def slice_mask_mask)

lemma PrePostE_ZeroExtend_slice_append[PrePostE_atomI]:
  shows "PrePostE (Q ((word_cat ((xs AND slice_mask outlen i l) >> (nat i)) ys) :: 'o::len word))
                  (liftS (ZeroExtend_slice_append outlen (xs :: 'x::len word) i l (ys :: 'y::len word)))
                  Q E"
  by (strong_cong_simp add: ZeroExtend_slice_append_def ZeroExtend__1_def ZeroExtend__0_def word_cat_shiftl_OR slice_mask_def)
     PrePostAuto
*)

Lemma PrePostE_ZeroExtend__0 m n (xs : mword m) `{H1:ArithFact (n >=? m)} H2 (Q : mword n -> predS regstate) E :
  PrePostE (Q (zero_extend xs n)) (liftS (@ZeroExtend__0 _ xs n H2)) Q E.
unfold ZeroExtend__0, aarch64_extras.length, length_mword.
PrePostE_rewrite liftState.
eapply PrePostE_strengthen_pre.
repeat PrePostE_step.
destruct H1 as [GE].
intros s q.
rewrite GE at 1.
intro GE'.
rewrite concat_zeros_extend.
repeat replace_ArithFact_proof.
revert pf pf0.
replace (n - m + m) with n by omega.
intros.
rewrite !Mword.autocast_eq.
generalize_ArithFact_proof_in q.
apply q.
Qed.
Hint Resolve PrePostE_ZeroExtend__0 : PrePostE_specs.

Lemma PrePostE_ZeroExtend__1 m n (xs : mword m) `{H1:ArithFact (n >=? m)} H2 (Q : mword n -> predS regstate) E :
  PrePostE (Q (zero_extend xs n)) (liftS (@ZeroExtend__1 _ n xs H2)) Q E.
unfold ZeroExtend__1.
apply PrePostE_ZeroExtend__0.
Qed.
Hint Resolve PrePostE_ZeroExtend__1 : PrePostE_specs.

Lemma PrePostE_ZeroExtend_slice_append a b (xs : mword a) i l (ys : mword b) n (Q : mword n -> predS regstate) E H0 H1 H2 H3 :
  PrePostE (Q (@zero_extend _ (concat_vec (@slice _ xs i l H0) ys) n H1))
           (liftS (@ZeroExtend_slice_append l _ _ n xs i l ys H2 H3))
           Q E.
unfold ZeroExtend_slice_append.
PrePostE_rewrite liftState.
eapply PrePostE_strengthen_pre.
repeat PrePostE_step.

intros s q.
cbv beta.
match goal with |- if ?c then _ else _ => destruct c eqn:guard at 1 end.
intro.

repeat generalize_ArithFact_proof_in q.
apply q.
match goal with w:mword ?n |- _ => specialize (ArithFact_mword _ w); intro end.

unfold aarch64_extras.length, length_mword in guard.
exfalso.
prepare_for_solver.
omega.
Qed.
Hint Resolve PrePostE_ZeroExtend_slice_append : PrePostE_specs.

(*

lemma PrePostE_bindS_ELIsInHost_False:
  assumes f: "PrePostE P (f False) Q E"
  shows "PrePostE (\<lambda>s. \<not>read_ELIsInHost el s \<and> P s) (bindS (liftS (ELIsInHost el)) f) Q E"
  by (rule PrePostE_bindS_left_const[where a = False and R = P]; PrePostAuto atomI: f)

lemma PrePostE_bindS_IsInHost_False:
  assumes f: "PrePostE P (f False) Q E"
  shows "PrePostE (\<lambda>s. \<not>read_ELIsInHost (read_EL s) s \<and> P s) (bindS (liftRS (liftS (IsInHost unit))) f) Q E"
  unfolding IsInHost_def
  by (rule PrePostE_bindS_left_const[where a = False and R = P]; PrePostAuto atomI: f)

schematic_goal PrePostE_MemAttrDefaults[PrePostE_atomI]:
  shows "PrePostE ?P (liftS (MemAttrDefaults memattrs)) Q E"
  by (strong_cong_simp add: MemAttrDefaults_def undefined_defs liftState_simp)
     (PrePost simp: PrePost_if_distribs fun2_if_distrib[where f = Q] if_then_all_distrib atomI: PrePostE_chooseS_any)
*)

Definition read_AddrTop_EL0 (address : mword 64) (isinstr : bool) (s : sequential_state regstate) : Z :=
  let tbi := TCR_EL1 (ss_regstate s) !! (if address !! 55 then 38 else 37) in
  let tbd := TCR_EL1 (ss_regstate s) !! (if address !! 55 then 52 else 51) in
  if tbi && (negb tbd || negb isinstr) then 55 else 63.

Lemma read_AddrTop_EL0_bounds (*[simp]:*) address isinstr s :
  55 <= read_AddrTop_EL0 address isinstr s /\
  read_AddrTop_EL0 address isinstr s < 64.
unfold read_AddrTop_EL0.
repeat match goal with |- context [if ?b then _ else _] => destruct b end; omega.
Qed.

Ltac norm_getBit :=
match goal with
| H : context[@getBit (Pos.to_nat ?n) ?v ?i] |- _ =>
  let n0 := constr:(Pos.to_nat n) in
  let n' := eval cbv in n0 in
  change (@getBit (Pos.to_nat n) v i) with (@getBit n' v i) in H
| H : context[@getBit (Z.to_nat ?n) ?v ?i] |- _ =>
  let n0 := constr:(Z.to_nat n) in
  let n' := eval cbv in n0 in
  change (@getBit (Z.to_nat n) v i) with (@getBit n' v i) in H
| H : context[@getBit ?n ?v (Pos.to_nat ?i)] |- _ =>
  let i0 := constr:(Pos.to_nat i) in
  let i' := eval cbv in i0 in
  change (@getBit n v (Pos.to_nat i)) with (@getBit n v i') in H
| H : context[@getBit ?n ?v (Z.to_nat ?i)] |- _ =>
  let i0 := constr:(Z.to_nat i) in
  let i' := eval cbv in i0 in
  change (@getBit n v (Z.to_nat i)) with (@getBit n v i') in H
| H : context[@getBit ?n (get_word ?v) ?i] |- _ =>
  change (@getBit n (get_word v) i) with (@getBit n v i) in H
| |- context[@getBit (Pos.to_nat ?n) ?v ?i] =>
  let n0 := constr:(Pos.to_nat n) in
  let n' := eval cbv in n0 in
  change (@getBit (Pos.to_nat n) v i) with (@getBit n' v i)
| |- context[@getBit (Z.to_nat ?n) ?v ?i] =>
  let n0 := constr:(Z.to_nat n) in
  let n' := eval cbv in n0 in
  change (@getBit (Z.to_nat n) v i) with (@getBit n' v i)
| |- context[@getBit ?n ?v (Pos.to_nat ?i)] =>
  let i0 := constr:(Pos.to_nat i) in
  let i' := eval cbv in i0 in
  change (@getBit n v (Pos.to_nat i)) with (@getBit n v i')
| |- context[@getBit ?n ?v (Z.to_nat ?i)]  =>
  let i0 := constr:(Z.to_nat i) in
  let i' := eval cbv in i0 in
  change (@getBit n v (Z.to_nat i)) with (@getBit n v i')
| |- context[@getBit ?n (get_word ?v) ?i]  =>
  change (@getBit n (get_word v) i) with (@getBit n v i)
end.

Ltac bitdestruct v i :=
let ty := type of v in
let ty' := eval compute in ty in
let i' := eval compute in i in
match ty' with
| word ?n => destruct (@getBit n v i')
end.

Lemma PrePostE_AddrTop_EL0 el address isinstr Q E :
  PrePostE (fun s => AArchConsistent s /\ AlwaysAArch64 s /\ eq_bit (access_vec_dec (SCR_EL3 (ss_regstate s)) 0) B1 = true /\ read_S1TranslationRegime el s = $1 /\ Q (read_AddrTop_EL0 address isinstr s) s) (liftS (AddrTop address isinstr el)) Q E.
unfold AddrTop.
PrePostE_rewrite liftState.
eapply PrePostE_strengthen_pre.
repeat PrePostE_step.

intros s (aarchconsistent & always64 & el3 & s1regime & q).
intros _.
split_ands; auto.
* rewrite s1regime. discriminate.
* simpl (sumbool_of_bool false). cbv beta match.
  rewrite s1regime.
  unfold read_AddrTop_EL0 in q.
  repeat hammer_if.
  + unfold access_vec_dec, access_mword_dec in EQ |- *.
    repeat norm_getBit.
    bitdestruct address 55%nat; try discriminate.
    bitdestruct (TCR_EL1 (ss_regstate s)) 38%nat;
    bitdestruct (TCR_EL1 (ss_regstate s)) 52%nat;
    destruct isinstr;
    apply q.
  + unfold access_vec_dec, access_mword_dec in EQ |- *.
    repeat norm_getBit.
    bitdestruct address 55%nat; try discriminate.
    bitdestruct (TCR_EL1 (ss_regstate s)) 37%nat;
    bitdestruct (TCR_EL1 (ss_regstate s)) 51%nat;
    destruct isinstr;
    apply q.
Qed.
Hint Resolve PrePostE_AddrTop_EL0 : PrePostE_specs.
(*
lemma PrePostE_undefined_AddressDescriptor[PrePostE_atomI]:
  "PrePostE (\<lambda>s. \<forall>f a b ba bb bc t d bd be bf.
                   Q \<lparr>AddressDescriptor_fault = CreateFaultRecord f 0 0 a ba 0 0 bb b,
                         AddressDescriptor_memattrs =
                           \<lparr>MemoryAttributes_typ = t, MemoryAttributes_device = d,
                              MemoryAttributes_inner = \<lparr>MemAttrHints_attrs = 0, MemAttrHints_hints = 0, MemAttrHints_transient = bc\<rparr>,
                              MemoryAttributes_outer = \<lparr>MemAttrHints_attrs = 0, MemAttrHints_hints = 0, MemAttrHints_transient = bd\<rparr>,
                              MemoryAttributes_shareable = be, MemoryAttributes_outershareable = bf\<rparr>,
                         AddressDescriptor_paddress = \<lparr>FullAddress_physicaladdress = 0, FullAddress_NS = 0\<rparr>, AddressDescriptor_vaddress = 0\<rparr>
                    s)
            (liftS (undefined_AddressDescriptor unit)) Q E"
  by (strong_cong_simp add: undefined_AddressDescriptor_def undefined_defs liftState_simp) PrePost

lemma PrePostE_HaltOnBreakpointOrWatchpoint_DebugDisabled:
  "\<lbrace>\<lambda>s. DBGEN (regstate s) = LOW \<and> \<not>MDSCR_EL1 (regstate s) !! 15 \<and> UsingAArch64 s \<and> Q False s\<rbrace>
   \<lbrakk>HaltOnBreakpointOrWatchpoint ()\<rbrakk>\<^sub>S
   \<lbrace>Q \<bar> E\<rbrace>"
  by (strong_cong_simp add: HaltingAllowed_def Halted_def DoubleLockStatus_def HaltOnBreakpointOrWatchpoint_def
                            ExternalSecureInvasiveDebugEnabled_def ExternalInvasiveDebugEnabled_def)
     (PrePostAuto)

lemma PrePostE_AArch64_GenerateDebugExceptions_ignore:
  "\<lbrace>\<lambda>s. UsingAArch64 s \<and> (\<forall>r. Q r s)\<rbrace> \<lbrakk>AArch64_GenerateDebugExceptions ()\<rbrakk>\<^sub>S \<lbrace>Q \<bar> E\<rbrace>"
  by (strong_cong_simp add: AArch64_GenerateDebugExceptions_def AArch64_GenerateDebugExceptionsFrom_def
                            Halted_def DoubleLockStatus_def)
     (PrePost simp: app_if_distrib)

lemma PrePostE_AArch64_CheckDebug_DebugDisabled:
  "\<lbrace>\<lambda>s. DBGEN (regstate s) = LOW \<and> \<not>MDSCR_EL1 (regstate s) !! 15 \<and> UsingAArch64 s \<and>
        (\<forall>r. FaultRecord_typ r = Fault_None \<longrightarrow> Q r s)\<rbrace>
   \<lbrakk>AArch64_CheckDebug vaddress acctype iswrite size1\<rbrakk>\<^sub>S
   \<lbrace>Q \<bar> E\<rbrace>"
  by (strong_cong_simp add: AArch64_CheckDebug_def liftState_simp,
      PrePostAuto atomI: PrePostE_any[of "\<lbrakk>AArch64_CheckWatchpoint vaddress acctype iswrite size1\<rbrakk>\<^sub>S"]
                          PrePostE_any[of "\<lbrakk>AArch64_CheckBreakpoint vaddress size1\<rbrakk>\<^sub>S"]
                          PrePostE_HaltOnBreakpointOrWatchpoint_DebugDisabled
                          PrePostE_AArch64_GenerateDebugExceptions_ignore)

end
*)

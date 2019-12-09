
Lemma cast_T_eq_dep (T : Z -> Type) (m n : Z) (x : T m) E :
  EqdepFacts.eq_dep Z T n (cast_T x E) m x.
subst.
rewrite cast_T_refl.
constructor.
Qed.

Lemma mword_to_nat_inj n m (w : mword n) (v : mword m) :
  Z.to_nat n = Z.to_nat m ->
  n = m.
intro H.
apply ArithFact_mword in w.
apply ArithFact_mword in v.
destruct w,v.
rewrite <- Z2Nat.id with (n := n). 2: omega.
rewrite <- Z2Nat.id with (n := m). 2: omega.
rewrite H.
reflexivity.
Qed.

Lemma mword_get_word_inj n (w v : mword n) :
  get_word w = get_word v ->
  w = v.
destruct n; auto.
destruct w.
Qed.

Lemma word_mword_eq_dep m w n v :
  EqdepFacts.eq_dep nat word (Z.to_nat m) (get_word w) (Z.to_nat n) (get_word v) ->
  EqdepFacts.eq_dep Z mword m w n v.
intro H.
inversion H.
apply mword_to_nat_inj in H1; auto.
subst.
apply Eqdep_dec.eq_dep_eq_dec in H; auto using Nat.eq_dec.
apply mword_get_word_inj in H.
subst.
constructor.
Qed.

Lemma get_word_eq x y w v :
  EqdepFacts.eq_dep Z mword x w y v ->
  EqdepFacts.eq_dep nat word (Z.to_nat x) (get_word w) (Z.to_nat y) (get_word v).
intro H.
inversion H.
subst.
constructor.
Qed.

Lemma nat_cast_eq_dep P n m E x :
  EqdepFacts.eq_dep nat P m (nat_cast P E x) n x.
subst.
rewrite nat_cast_same.
constructor.
Qed.

Lemma get_word_mword_of_nat n (w : word n) :
  EqdepFacts.eq_dep nat word _ (get_word (mword_of_nat w)) n w.
destruct n.
* reflexivity.
* change (get_word (mword_of_nat w)) with (mword_of_nat w).
  eapply EqdepFacts.eq_dep_trans.
  apply nat_cast_eq_dep.
  constructor.
Qed.

Lemma eq_rect_eq_dep T P i x j E :
  EqdepFacts.eq_dep T P j (eq_rect i P x j E) i x.
subst.
constructor.
Qed.

Lemma zero_extend_id m w H :
  @zero_extend m w m H = w.
destruct m.
* simpl in w.
  shatter_word w.
  reflexivity.
* simpl in w.
  apply Eqdep_dec.eq_dep_eq_dec; auto using Z.eq_dec.
  unfold zero_extend, extz_vec.
  unfold cast_to_mword.
  eapply EqdepFacts.eq_dep_trans.
  apply cast_T_eq_dep.
  rewrite Z.sub_diag.
  simpl (Z.to_nat 0).
  apply word_mword_eq_dep.
  eapply EqdepFacts.eq_dep_trans.
  apply get_word_mword_of_nat.
  rewrite zext_zero.
  eapply EqdepFacts.eq_dep_trans.
  apply eq_rect_eq_dep.
  constructor.
* destruct w.
Qed.

Lemma cast_positive_eq_dep T p q x H :
  EqdepFacts.eq_dep _ _ q (cast_positive T p q x H) p x.
subst.
rewrite cast_positive_refl.
constructor.
Qed.

Lemma eq_dep_lift (S T : Type) (P : T -> Type) (f : S -> T) i x j y :
  EqdepFacts.eq_dep S (fun s => P (f s)) i x j y ->
  EqdepFacts.eq_dep T P (f i) x (f j) y.
inversion 1.
subst.
constructor.
Qed.

Ltac remove_get_word :=
  match goal with |- context[get_word ?w] => change (get_word w) with w end.

Lemma get_word_cast_to_mword m n (w : word n) (H:Z.of_nat n = m) :
  EqdepFacts.eq_dep nat word _ (get_word (cast_to_mword w H)) n w.
destruct n.
* simpl in H.
  subst.
  shatter_word w.
  constructor.
* simpl in H. subst.
  remove_get_word.
  unfold cast_to_mword.
  eapply EqdepFacts.eq_dep_trans.
  rewrite cast_T_refl.
  apply nat_cast_eq_dep.
  constructor.
Qed.

Eval compute in (slice (mword_of_int 10 : mword 8) 1 3).
Eval compute in (Word_slice (n := 3) 1 (mword_of_int 10 : mword 8)).

Lemma autocast_eq_dep T m n x EQ :
  EqdepFacts.eq_dep Z T n (@autocast T m n x EQ) m x.
destruct EQ.
subst.
unfold autocast.
apply cast_T_eq_dep.
Qed.

Lemma split1_eq_dep sz1 sz2 x sz1' sz2' x' :
  sz1 = sz1' ->
  sz2 = sz2' ->
  EqdepFacts.eq_dep nat word _ x _ x' ->
  EqdepFacts.eq_dep nat word _ (split1 sz1 sz2 x) _ (split1 sz1' sz2' x').
intros; subst.
apply Eqdep_dec.eq_dep_eq_dec in H1.
subst.
reflexivity.
apply Nat.eq_dec.
Qed.

Lemma split2_eq_dep sz1 sz2 x sz1' sz2' x' :
  sz1 = sz1' ->
  sz2 = sz2' ->
  EqdepFacts.eq_dep nat word _ x _ x' ->
  EqdepFacts.eq_dep nat word _ (split2 sz1 sz2 x) _ (split2 sz1' sz2' x').
intros; subst.
apply Eqdep_dec.eq_dep_eq_dec in H1.
subst.
reflexivity.
apply Nat.eq_dec.
Qed.

Lemma cast_word_eq_dep m n x E :
  EqdepFacts.eq_dep _ _ _ (@cast_word m n x E) _ x.
unfold cast_word.
apply nat_cast_eq_dep.
Qed.

Lemma sliceok m n i v :
  @Word_slice m n i v = cast_word (get_word (slice (mword_of_nat v) (Z.of_nat i) (Z.of_nat n))) (Nat2Z.id _).
unfold Word_slice, slice.
match goal with |- context[sumbool_of_bool ?b] => destruct (sumbool_of_bool b) end.
* destruct (Bool.orb_prop _ _ e).
  + apply Z.eqb_eq in H.
    assert (n = 0%nat) by omega.
    subst.
    rewrite split2_WO.
    reflexivity.
  + apply Z.ltb_lt in H.
    exfalso.
    omega.
* destruct (Bool.orb_false_elim _ _ e) as [N _].
  apply Z.eqb_neq in N.
  assert ((n > 0)%nat) by omega. clear N.
  match goal with |- context[sumbool_of_bool ?b] => destruct (sumbool_of_bool b) end.
  + exfalso.
    rewrite Z.geb_leb in e0.
    apply Z.leb_le in e0.
    rewrite !Nat2Z.inj_add in e0.
    omega.
  + apply Eqdep_dec.eq_dep_eq_dec; auto using Nat.eq_dec.
    apply EqdepFacts.eq_dep_sym.
    eapply EqdepFacts.eq_dep_trans.
    apply nat_cast_eq_dep.
    eapply EqdepFacts.eq_dep_trans.
    apply get_word_eq.
    apply autocast_eq_dep.
    unfold subrange_vec_dec.
    eapply EqdepFacts.eq_dep_trans.
    apply get_word_cast_to_mword.
    generalize e0 as E0. intro.
    rewrite Z.geb_leb in e0.
    apply Z.leb_gt in e0.
    apply split2_eq_dep.
    - apply Nat2Z.id.
    - rewrite Nat2Z.id.
      rewrite <- Nat2Z.inj_add.
      change 1 with (Z.of_nat 1).
      rewrite <- Nat2Z.inj_sub.
      rewrite Nat2Z.id.
      omega.
      omega.
    - eapply EqdepFacts.eq_dep_trans.
      apply cast_word_eq_dep.
      apply split1_eq_dep.
      rewrite <- Nat2Z.inj_add.
      change 1 with (Z.of_nat 1).
      rewrite <- Nat2Z.inj_sub.
      rewrite Nat2Z.id.
      omega.
      omega.
      rewrite <- Nat2Z.inj_add.
      change 1 with (Z.of_nat 1).
      rewrite <- Nat2Z.inj_sub.
      rewrite !Nat2Z.id.
      omega.
      omega.
      eapply EqdepFacts.eq_dep_trans.
      apply cast_word_eq_dep.
      apply get_word_mword_of_nat.
Qed.

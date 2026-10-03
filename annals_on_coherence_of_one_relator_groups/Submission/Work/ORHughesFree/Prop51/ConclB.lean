/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The conclusion of [JZLA20, Proposition 5.1] with an explicit complexity bound

`ConclB d b T` is the conclusion `Prop51Concl d b` of [JZLA20, Proposition 5.1] with the
`H`-complexity `Tree_H b` of `b` replaced by an arbitrary bound `T` on the complexities of the
coefficients.  It is the shape in which the three inductive cases of the proposition (sum,
product, `⋄`) are composed:

* `Prop51Concl d b` is `ConclB d b (d.treeH b)` (`prop51Concl_iff_conclB`);
* `ConclB d x T₁ → ConclB d y T₂ → ConclB d (x+y) (T₁+T₂)`;
* `ConclB d x T₁ → ConclB d y T₂ → ConclB d (x*y) (T₁*T₂)` (for bounds of width one);
* `ConclB d x T₁ → ConclB d x⋄ (exp (exp T₁))`.

The file also contains the elementary complexity estimates on which those three proofs rest
(`treeH_le_add`, `treeH_le_mul`, `treeH_le_sum`, `treeH_conj_le`, `treeH_conj_eq`,
`treeH_ratOp_le`), and — in the `Tree` namespace — the order on `Option Tree` with the logarithm
operations `dlog`, `d2log` and their interaction with sums and products of trees, which is what
makes the estimates of [JZLA20, Lemma 4.3(vii)–(x)] available in the form used by the induction.
-/
import Mathlib
import Submission.Work.ORHughesFree.Prop51
import Submission.Work.ORHughesFree.SkewLaurentSeriesInstances
import Submission.Work.ORHughesFree.SkewLaurentSeries.VanishesBelow
import Submission.Work.ORHughesFree.Prop51.ofGroup_t_pow
import Submission.Work.ORHughesFree.Prop51.treeH_ofGroup
import Submission.Work.ORHughesFree.Tree.Log
import Submission.Work.ORHughesFree.Tree.log_add
import Submission.Work.ORHughesFree.Tree.log_mul
import Submission.Work.ORHughesFree.Tree.log_mono
import Submission.Work.ORHughesFree.Tree.lt_of_log_lt
import Submission.Work.ORHughesFree.Tree.lt_exp_exp

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORHughesFree

namespace Tree

/-! ### The order on `Option Tree` with `none` least -/

/-- The order on `Option Tree` for which `none` is the least element and `some a ≤ some b` iff
`a ≤ b`.  This is the order in which the logarithms of [JZLA20, Lemma 4.3(vii)–(x)] take their
values, `none` standing for `-∞`. -/
def Ole : Option Tree → Option Tree → Prop
  | none, none => True
  | none, some _ => True
  | some _, none => False
  | some a, some b => Tree.le a b

/-- The strict part of `Ole`. -/
def Olt (a b : Option Tree) : Prop := Ole a b ∧ ¬ Ole b a

theorem ole_refl (a : Option Tree) : Ole a a := by
  cases a with
  | none => trivial
  | some x => exact Or.inl rfl

theorem ole_none_left (a : Option Tree) : Ole none a := by cases a <;> trivial

theorem not_ole_some_none (a : Tree) : ¬ Ole (some a) none := fun h => h

theorem ole_some_some_iff {a b : Tree} : Ole (some a) (some b) ↔ Tree.le a b := Iff.rfl

theorem ole_some_some {a b : Tree} (h : Tree.le a b) : Ole (some a) (some b) := h

theorem lt_of_le_of_lt' {a b c : Tree} (h1 : Tree.le a b) (h2 : Tree.lt b c) : Tree.lt a c := by
  rcases h1 with h1 | h1
  · rw [h1]; exact h2
  · exact Tree.lt_trans h1 h2

theorem ole_some_of_lt {a b : Tree} (h : Tree.lt a b) : Olt (some a) (some b) := by
  refine ⟨Tree.le_of_lt h, fun hba => ?_⟩
  have hab : a = b := Tree.le_antisymm (Tree.le_of_lt h) hba
  exact Tree.lt_irrefl (hab ▸ h)

theorem ole_trans {a b c : Option Tree} (hab : Ole a b) (hbc : Ole b c) : Ole a c := by
  cases a with
  | none => exact ole_none_left c
  | some x =>
    cases b with
    | none => exact (hab : False).elim
    | some y =>
      cases c with
      | none => exact (hbc : False).elim
      | some z => exact Tree.le_trans hab hbc

theorem ole_antisymm {a b : Option Tree} (hab : Ole a b) (hba : Ole b a) : a = b := by
  cases a with
  | none => cases b with
    | none => rfl
    | some y => exact (hba : False).elim
  | some x => cases b with
    | none => exact (hab : False).elim
    | some y => exact congrArg some (Tree.le_antisymm hab hba)

theorem olt_iff_le_ne {a b : Option Tree} : Olt a b ↔ Ole a b ∧ a ≠ b := by
  constructor
  · intro h; exact ⟨h.1, fun he => h.2 (he ▸ ole_refl b)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun hba => h2 (ole_antisymm h1 hba)⟩

theorem olt_of_olt_some {a b : Tree} (h : Olt (some a) (some b)) : Tree.lt a b := by
  have h' : Tree.le a b ∧ ¬ Tree.le b a := h
  refine Tree.lt_of_le_of_ne h'.1 (fun hab => h'.2 ?_)
  rw [hab]
  exact Tree.le_refl b

theorem ole_total (a b : Option Tree) : Ole a b ∨ Ole b a := by
  cases a with
  | none => exact Or.inl (ole_none_left b)
  | some x => cases b with
    | none => exact Or.inr (ole_none_left (some x))
    | some y => exact (Tree.le_total x y).elim Or.inl Or.inr

theorem olt_ole_trans {a b c : Option Tree} (hab : Olt a b) (hbc : Ole b c) : Olt a c :=
  ⟨ole_trans hab.1 hbc, fun hca => hab.2 (ole_trans hbc hca)⟩

theorem ole_olt_trans {a b c : Option Tree} (hab : Ole a b) (hbc : Olt b c) : Olt a c :=
  ⟨ole_trans hab hbc.1, fun hca => hbc.2 (ole_trans hca hab)⟩

/-! ### The maximum of two optional trees -/

theorem omax_eq_left_or_right (a b : Option Tree) : Tree.omax a b = a ∨ Tree.omax a b = b := by
  cases a with
  | none => exact Or.inr rfl
  | some x => cases b with
    | none => exact Or.inl rfl
    | some y =>
      classical
      simp only [Tree.omax]
      split
      · exact Or.inr rfl
      · exact Or.inl rfl

theorem ole_omax_left (a b : Option Tree) : Ole a (Tree.omax a b) := by
  cases a with
  | none => exact ole_none_left _
  | some x => cases b with
    | none => exact ole_refl _
    | some y =>
      classical
      simp only [Tree.omax]
      by_cases h : Tree.le x y
      · rw [if_pos h]; exact h
      · rw [if_neg h]; exact ole_refl _

theorem ole_omax_right (a b : Option Tree) : Ole b (Tree.omax a b) := by
  cases a with
  | none => exact ole_refl _
  | some x => cases b with
    | none => exact ole_none_left _
    | some y =>
      classical
      simp only [Tree.omax]
      by_cases h : Tree.le x y
      · rw [if_pos h]; exact ole_refl _
      · rw [if_neg h]
        exact (Tree.le_total x y).resolve_left h

theorem ole_omax_of {a b c : Option Tree} (ha : Ole a c) (hb : Ole b c) :
    Ole (Tree.omax a b) c := by
  cases a with
  | none => simpa [Tree.omax_none_left] using hb
  | some x => cases b with
    | none => simpa [Tree.omax_none_right] using ha
    | some y =>
      classical
      simp only [Tree.omax]
      by_cases h : Tree.le x y
      · rw [if_pos h]; exact hb
      · rw [if_neg h]; exact ha

theorem ole_omax_iff {a b c : Option Tree} : Ole (Tree.omax a b) c ↔ Ole a c ∧ Ole b c :=
  ⟨fun h => ⟨ole_trans (ole_omax_left a b) h, ole_trans (ole_omax_right a b) h⟩,
   fun h => ole_omax_of h.1 h.2⟩

theorem ole_self_omax {a b c : Option Tree} (h : Ole c (Tree.omax a b)) :
    Ole c a ∨ Ole c b := by
  rcases omax_eq_left_or_right a b with h' | h'
  · exact Or.inl (h' ▸ h)
  · exact Or.inr (h' ▸ h)

theorem olt_omax_of {a b c : Option Tree} (ha : Olt a c) (hb : Olt b c) :
    Olt (Tree.omax a b) c := by
  refine ⟨ole_omax_of ha.1 hb.1, fun h => ?_⟩
  rcases omax_eq_left_or_right a b with h' | h'
  · rw [h'] at h; exact ha.2 h
  · rw [h'] at h; exact hb.2 h

/-- The maximum of a finite list of optional trees. -/
noncomputable def listOMax : List (Option Tree) → Option Tree
  | [] => none
  | a :: l => Tree.omax a (listOMax l)

theorem ole_listOMax {l : List (Option Tree)} {c : Option Tree} :
    Ole (listOMax l) c ↔ ∀ a ∈ l, Ole a c := by
  induction l with
  | nil =>
    rw [listOMax]
    exact ⟨fun _ => by simp, fun _ => ole_none_left c⟩
  | cons a l ih =>
    simp only [listOMax, List.mem_cons]
    rw [ole_omax_iff, ih]
    constructor
    · rintro ⟨h1, h2⟩ b (rfl | hb)
      · exact h1
      · exact h2 b hb
    · intro h; exact ⟨h a (Or.inl rfl), fun b hb => h b (Or.inr hb)⟩

theorem ole_of_listOMax {l : List (Option Tree)} {c : Option Tree} (h : Ole c (listOMax l))
    (hne : l ≠ []) : ∃ a ∈ l, Ole c a := by
  induction l with
  | nil => exact absurd rfl hne
  | cons b l ih =>
    have h1 : Ole c b ∨ Ole c (listOMax l) := by
      simp only [listOMax] at h
      exact ole_self_omax h
    rcases h1 with h1 | h1
    · exact ⟨b, by simp, h1⟩
    · cases l with
      | nil =>
        simp only [listOMax] at h1
        refine ⟨b, by simp, ?_⟩
        cases c with
        | none => exact ole_none_left b
        | some x => exact (h1 : False).elim
      | cons d l' =>
        obtain ⟨e, he, hec⟩ := ih h1 (by simp)
        exact ⟨e, List.mem_cons_of_mem b he, hec⟩

theorem olt_listOMax {l : List (Option Tree)} {c : Option Tree} (hne : l ≠ [])
    (h : ∀ a ∈ l, Olt a c) : Olt (listOMax l) c := by
  refine ⟨(ole_listOMax).mpr fun a ha => (h a ha).1, fun hc => ?_⟩
  obtain ⟨b, hb, hbc⟩ := ole_of_listOMax hc hne
  exact (h b hb).2 hbc

/-! ### The absorbing sum of two optional trees -/

/-- The "sum" of optional trees in which `none` (`-∞`) is absorbing; it is the operation under
which the logarithm of a product of complexities is additive. -/
noncomputable def oadd : Option Tree → Option Tree → Option Tree
  | none, _ => none
  | some _, none => none
  | some a, some b => some (a + b)

theorem oadd_none_left (b : Option Tree) : oadd none b = none := rfl

theorem oadd_none_right (a : Option Tree) : oadd a none = none := by cases a <;> rfl

theorem oadd_some_some (a b : Tree) : oadd (some a) (some b) = some (a + b) := rfl

theorem ole_oadd_mono {a a' b b' : Option Tree} (ha : Ole a a') (hb : Ole b b') :
    Ole (oadd a b) (oadd a' b') := by
  cases a with
  | none => cases a' with
    | none => exact ole_none_left _
    | some _ => exact ole_none_left _
  | some x => cases a' with
    | none => exact (ha : False).elim
    | some x' => cases b with
      | none => cases b' with
        | none => exact ole_none_left _
        | some _ => exact ole_none_left _
      | some y => cases b' with
        | none => exact (hb : False).elim
        | some y' => exact Tree.le_add ha hb

theorem ole_oadd_some {a b : Option Tree} {A B : Tree} (ha : Ole a (some A))
    (hb : Ole b (some B)) : Ole (oadd a b) (some (A + B)) := by
  cases a with
  | none => exact ole_none_left _
  | some x => cases b with
    | none => exact ole_none_left _
    | some y => exact Tree.le_add ha hb

theorem olt_oadd_some {a b : Option Tree} {A B : Tree} (ha : Ole a (some A))
    (hb : Ole b (some B)) (h : ¬ (a = some A ∧ b = some B)) :
    Olt (oadd a b) (some (A + B)) := by
  refine ⟨ole_oadd_some ha hb, fun hba => ?_⟩
  cases a with
  | none => exact not_ole_some_none (A + B) hba
  | some x => cases b with
    | none => exact not_ole_some_none (A + B) hba
    | some y =>
      have hx : Tree.le x A := ha
      have hy : Tree.le y B := hb
      have hba' : Tree.le (A + B) (x + y) := hba
      have heq : x + y = A + B := Tree.le_antisymm (Tree.le_add hx hy) hba'
      obtain ⟨e1, e2⟩ := (Tree.le_add_eq hx hy).mp heq
      exact h ⟨by rw [e1], by rw [e2]⟩

/-! ### The (double) logarithm of a tree -/

/-- The logarithm of a tree, as an element of `Option Tree` (`none` for the one-vertex tree). -/
noncomputable def dlog (x : Tree) : Option Tree := Tree.log x

/-- The double logarithm of a tree, as an element of `Option Tree`. -/
noncomputable def d2log (x : Tree) : Option Tree :=
  match Tree.log x with
  | none => none
  | some a => Tree.log a

theorem dlog_zero : dlog (0 : Tree) = none := (Tree.log_spec 0).1 rfl

theorem dlog_eq_none {x : Tree} (h : Tree.log x = none) : dlog x = none := by
  simp only [dlog, h]

theorem d2log_zero : d2log (0 : Tree) = none := by
  simp only [d2log, (Tree.log_spec 0).1 rfl]

theorem d2log_eq_none {x : Tree} (h : Tree.log x = none) : d2log x = none := by
  simp only [d2log, h]

theorem d2log_eq_some {x a : Tree} (h : Tree.log x = some a) : d2log x = Tree.log a := by
  simp only [d2log, h]

theorem log_exp (x : Tree) : Tree.log (Tree.exp x) = some x := by
  obtain ⟨b, hb⟩ := (Tree.log_spec (Tree.exp x)).2.2 (Tree.exp_ne_zero x)
  rw [hb]
  congr 1
  have hmem := ((Tree.log_spec (Tree.exp x)).2.1 b hb).1
  rw [Tree.fam_exp] at hmem
  exact Multiset.mem_singleton.mp hmem

theorem dlog_exp (x : Tree) : dlog (Tree.exp x) = some x := log_exp x

theorem d2log_exp_exp (x : Tree) : d2log (Tree.exp (Tree.exp x)) = some x := by
  rw [d2log_eq_some (log_exp (Tree.exp x)), log_exp x]

theorem dlog_eq_none_iff {x : Tree} : dlog x = none ↔ x = 0 := by
  rw [dlog]
  constructor
  · intro h
    by_contra hne
    obtain ⟨b, hb⟩ := (Tree.log_spec x).2.2 hne
    rw [h] at hb; exact absurd hb (by simp)
  · rintro rfl; exact (Tree.log_spec 0).1 rfl

theorem ole_dlog_of_le {x y : Tree} (h : Tree.le x y) : Ole (dlog x) (dlog y) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [dlog_zero]; exact ole_none_left _
  · have hy0 : y ≠ 0 := by
      intro hy
      rw [hy] at h
      rcases h with h | h
      · exact hx0 h
      · exact Tree.not_lt_zero h
    obtain ⟨a, ha⟩ := (Tree.log_spec x).2.2 hx0
    obtain ⟨b, hb⟩ := (Tree.log_spec y).2.2 hy0
    rw [dlog, dlog, ha, hb]
    exact Tree.log_mono h ha hb

theorem ole_d2log_of_le {x y : Tree} (h : Tree.le x y) : Ole (d2log x) (d2log y) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [d2log_zero]
    rcases hy : Tree.log y with _ | b
    · rw [d2log_eq_none hy]; exact ole_refl _
    · rw [d2log_eq_some hy]; exact ole_none_left _
  · have hy0 : y ≠ 0 := by
      intro hy
      rw [hy] at h
      rcases h with h | h
      · exact hx0 h
      · exact Tree.not_lt_zero h
    obtain ⟨a, ha⟩ := (Tree.log_spec x).2.2 hx0
    obtain ⟨b, hb⟩ := (Tree.log_spec y).2.2 hy0
    have hab : Tree.le a b := Tree.log_mono h ha hb
    rw [d2log_eq_some ha, d2log_eq_some hb]
    exact ole_dlog_of_le hab

theorem d2log_le_self (x : Tree) : Ole (d2log x) (some x) := by
  rcases hx : Tree.log x with _ | a
  · rw [d2log_eq_none hx]; exact ole_none_left _
  · rw [d2log_eq_some hx]
    rcases ha : Tree.log a with _ | b
    · exact ole_none_left _
    · have hmema : a ∈ Tree.fam x := ((Tree.log_spec x).2.1 a hx).1
      have hb : b ∈ Tree.fam a := ((Tree.log_spec a).2.1 b ha).1
      exact Tree.le_of_lt (Tree.lt_trans (Tree.lt_of_mem_fam hb) (Tree.lt_of_mem_fam hmema))

theorem olt_d2log_self (x : Tree) : Olt (d2log x) (some x) := by
  refine ⟨d2log_le_self x, fun h => ?_⟩
  rcases hx : Tree.log x with _ | a
  · rw [d2log_eq_none hx] at h; exact not_ole_some_none x h
  · rcases ha : Tree.log a with _ | b
    · rw [d2log_eq_some hx, ha] at h; exact not_ole_some_none x h
    · rw [d2log_eq_some hx, ha] at h
      have hmema : a ∈ Tree.fam x := ((Tree.log_spec x).2.1 a hx).1
      have hb : b ∈ Tree.fam a := ((Tree.log_spec a).2.1 b ha).1
      have hbx : Tree.lt b x :=
        Tree.lt_trans (Tree.lt_of_mem_fam hb) (Tree.lt_of_mem_fam hmema)
      have hxb : x = b := Tree.le_antisymm h (Tree.le_of_lt hbx)
      rw [hxb] at hbx
      exact Tree.lt_irrefl hbx

theorem lt_of_olt_dlog {x y : Tree} (h : Olt (dlog x) (dlog y)) : Tree.lt x y := by
  have hy0 : y ≠ 0 := by
    intro hy
    rw [hy, dlog_zero] at h
    exact h.2 (ole_none_left _)
  rcases eq_or_ne x 0 with rfl | hx0
  · exact Tree.lt_of_le_of_ne (Tree.le_zero y) (fun h0 => hy0 h0.symm)
  · obtain ⟨a, ha⟩ := (Tree.log_spec x).2.2 hx0
    have hyn : Tree.log y ≠ none := by
      intro hy'
      rw [dlog, dlog, ha, hy'] at h
      exact h.2 (ole_none_left _)
    rcases hb : Tree.log y with _ | b
    · exact absurd hb hyn
    · rw [dlog, dlog, ha, hb] at h
      exact Tree.lt_of_log_lt ha hb (olt_of_olt_some h)

/-- If all children of `z` are strictly below `A`, then `z` is strictly below `exp A`. -/
theorem lt_exp_of_fam_lt {z A : Tree} (h : ∀ c ∈ Tree.fam z, Tree.lt c A) :
    Tree.lt z (Tree.exp A) := by
  rw [Tree.lt_iff]
  exact ⟨0, Tree.fam z, {A}, by simp, by simp, by rw [Tree.fam_exp]; simp,
    fun c hc => ⟨A, Multiset.mem_singleton_self A, h c hc⟩⟩

/-- The double-log version of `lt_of_olt_dlog`, for the target `exp (exp A)`: if the double
logarithm of `x` is strictly below `A` then `x` is strictly below `exp (exp A)`. -/
theorem lt_exp_exp_of_olt_d2log {x A : Tree} (h : Olt (d2log x) (some A)) :
    Tree.lt x (Tree.exp (Tree.exp A)) := by
  rcases hx : Tree.log x with _ | a
  · have hx0 : x = 0 := dlog_eq_none_iff.mp (dlog_eq_none hx)
    rw [hx0]
    exact Tree.lt_of_le_of_ne (Tree.le_zero _) (fun h0 => Tree.exp_ne_zero _ h0.symm)
  · rcases ha : Tree.log a with _ | c
    · rw [d2log_eq_some hx, ha] at h
      have ha0 : a = 0 := by
        by_contra hne
        obtain ⟨e, he⟩ := (Tree.log_spec a).2.2 hne
        rw [ha] at he; exact absurd he (by simp)
      refine lt_exp_of_fam_lt (fun b hb => ?_)
      have hle : Tree.le b a := ((Tree.log_spec x).2.1 a hx).2 b hb
      rw [ha0] at hle
      have hb0 : b = 0 := Tree.le_antisymm hle (Tree.le_zero b)
      rw [hb0]
      exact Tree.lt_of_le_of_ne (Tree.le_zero _) (fun h0 => Tree.exp_ne_zero A h0.symm)
    · rw [d2log_eq_some hx, ha] at h
      have hcA : Tree.lt c A := olt_of_olt_some h
      have ha_lt : Tree.lt a (Tree.exp A) :=
        lt_exp_of_fam_lt (fun b hb => lt_of_le_of_lt' (((Tree.log_spec a).2.1 c ha).2 b hb) hcA)
      exact lt_exp_of_fam_lt
        (fun b hb => lt_of_le_of_lt' (((Tree.log_spec x).2.1 a hx).2 b hb) ha_lt)

theorem ole_dlog_add (x y : Tree) : Ole (dlog (x + y)) (Tree.omax (dlog x) (dlog y)) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Tree.zero_add]
    exact ole_omax_right _ _
  · rcases eq_or_ne y 0 with rfl | hy0
    · rw [Tree.add_zero]
      exact ole_omax_left _ _
    · rw [dlog, dlog, dlog, Tree.log_add hx0 hy0]
      exact ole_refl _

theorem ole_dlog_mul (x y : Tree) : Ole (dlog (x * y)) (oadd (dlog x) (dlog y)) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Tree.zero_mul, dlog_zero]
    exact ole_none_left _
  · rcases eq_or_ne y 0 with rfl | hy0
    · rw [Tree.mul_zero, dlog_zero]
      exact ole_none_left _
    · obtain ⟨a, ha⟩ := (Tree.log_spec x).2.2 hx0
      obtain ⟨b, hb⟩ := (Tree.log_spec y).2.2 hy0
      rw [dlog, dlog, dlog, ha, hb, Tree.log_mul ha hb, oadd_some_some]
      exact ole_refl _

theorem ole_d2log_add (x y : Tree) :
    Ole (d2log (x + y)) (Tree.omax (d2log x) (d2log y)) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Tree.zero_add]
    exact ole_omax_right _ _
  · rcases eq_or_ne y 0 with rfl | hy0
    · rw [Tree.add_zero]
      exact ole_omax_left _ _
    · obtain ⟨a, ha⟩ := (Tree.log_spec x).2.2 hx0
      obtain ⟨b, hb⟩ := (Tree.log_spec y).2.2 hy0
      by_cases h : Tree.le a b
      · have hlog : Tree.log (x + y) = some b := by
          rw [Tree.log_add hx0 hy0, ha, hb, Tree.omax_some_some_of_le h]
        rw [d2log_eq_some hlog, d2log_eq_some ha, d2log_eq_some hb]
        exact ole_omax_right _ _
      · have hlog : Tree.log (x + y) = some a := by
          rw [Tree.log_add hx0 hy0, ha, hb, Tree.omax_some_some_of_not_le h]
        rw [d2log_eq_some hlog, d2log_eq_some ha, d2log_eq_some hb]
        exact ole_omax_left _ _

theorem ole_d2log_mul (x y : Tree) :
    Ole (d2log (x * y)) (Tree.omax (d2log x) (d2log y)) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Tree.zero_mul, d2log_zero]
    exact ole_none_left _
  · rcases eq_or_ne y 0 with rfl | hy0
    · rw [Tree.mul_zero, d2log_zero]
      exact ole_none_left _
    · obtain ⟨a, ha⟩ := (Tree.log_spec x).2.2 hx0
      obtain ⟨b, hb⟩ := (Tree.log_spec y).2.2 hy0
      have hmul : Tree.log (x * y) = some (a + b) := Tree.log_mul ha hb
      rw [d2log_eq_some hmul, d2log_eq_some ha, d2log_eq_some hb]
      rcases eq_or_ne a 0 with rfl | ha0
      · rw [Tree.zero_add]
        exact ole_omax_right _ _
      · rcases eq_or_ne b 0 with rfl | hb0
        · rw [Tree.add_zero]
          exact ole_omax_left _ _
        · rw [Tree.log_add ha0 hb0]
          exact ole_refl _

end Tree

namespace Prop51

open Work.ORHughesFree

variable {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
  [MulSemiringAction (Multiplicative ℤ) ↥DN]

/-- The complexity of `0 ∈ D_{H,P}` is `0`. -/
theorem treeH_zero (d : Prop51Data Γ P DN) : d.treeH 0 = 0 :=
  (d.treeH_eq_zero_iff d.DH.zero_mem).mpr rfl

/-- The conclusion of [JZLA20, Proposition 5.1] for a fixed element `b ∈ D_{H,P}`, with the
`H`-complexity of `b` replaced by an explicit bound `T` on the complexities of the coefficients.

`Prop51Concl d b` is the special case `T = d.treeH b` (`prop51Concl_iff_conclB`); the extra
generality is what makes the sum, product and `⋄` steps of the induction of
[JZLA20, Proposition 5.1] composable, since the bound one gets for `x + y` is `T₁ + T₂` and not
`Tree_H (x + y)`. -/
def ConclB (d : Prop51Data Γ P DN) (b : P) (T : Tree) : Prop :=
  ∃ f : SkewLaurentSeries ↥DN, d.laurentEmbed f = b ∧
    (∀ k : ℤ, Tree.le (d.treeH (d.coeffToP (f.1 k))) T) ∧
    (∀ k : ℤ, d.treeH (d.coeffToP (f.1 k)) = T → ∀ j : ℤ, j ≠ k → f.1 j = 0)

theorem prop51Concl_iff_conclB (d : Prop51Data Γ P DN) (b : P) :
    Prop51Concl d b ↔ ConclB d b (d.treeH b) := by
  constructor
  · rintro ⟨f, h1, h2, h3⟩
    refine ⟨f, h1, fun k => ?_, h3⟩
    by_cases hk : f.1 k = 0
    · rw [hk]
      have hc : d.coeffToP (0 : ↥DN) = 0 := rfl
      rw [hc, treeH_zero d]
      exact Tree.le_zero _
    · exact h2 k hk
  · rintro ⟨f, h1, h2, h3⟩
    exact ⟨f, h1, fun k hk => h2 k, h3⟩

theorem conclB_zero (d : Prop51Data Γ P DN) {T : Tree} (hT : T ≠ 0) : ConclB d 0 T := by
  refine ⟨0, map_zero d.laurentEmbed, fun k => ?_, fun k hk => ?_⟩
  · have hc : d.coeffToP ((0 : SkewLaurentSeries ↥DN).1 k) = 0 := rfl
    rw [hc, treeH_zero d]
    exact Tree.le_zero T
  · have hc : d.coeffToP ((0 : SkewLaurentSeries ↥DN).1 k) = 0 := rfl
    rw [hc, treeH_zero d] at hk
    exact absurd hk.symm hT

theorem conclB_mono {d : Prop51Data Γ P DN} {b : P} {T T' : Tree} (h : ConclB d b T)
    (hle : Tree.le T T') : ConclB d b T' := by
  obtain ⟨f, h1, h2, h3⟩ := h
  refine ⟨f, h1, fun k => Tree.le_trans (h2 k) hle, fun k hk j hj => ?_⟩
  exact h3 k (hk.trans (Tree.le_antisymm hle (hk ▸ h2 k)).symm) j hj

/-! ### Elementary complexity estimates -/

/-- The complexity of a sum is at most the sum of the complexities. -/
theorem treeH_le_add (d : Prop51Data Γ P DN) {x y : P} (hx : x ∈ d.DH) (hy : y ∈ d.DH) :
    Tree.le (d.treeH (x + y)) (d.treeH x + d.treeH y) := by
  obtain ⟨α, hα, hαt⟩ := d.exists_realizing hx
  obtain ⟨β, hβ, hβt⟩ := d.exists_realizing hy
  have h := (d.treeH_spec (x + y) (d.DH.add_mem hx hy)).2 (α + β) (by rw [map_add, hα, hβ])
  rw [Rat.treeOfRat_add, hαt, hβt] at h
  exact h

/-- The complexity of a product is at most the product of the complexities. -/
theorem treeH_le_mul (d : Prop51Data Γ P DN) {x y : P} (hx : x ∈ d.DH) (hy : y ∈ d.DH) :
    Tree.le (d.treeH (x * y)) (d.treeH x * d.treeH y) := by
  obtain ⟨α, hα, hαt⟩ := d.exists_realizing hx
  obtain ⟨β, hβ, hβt⟩ := d.exists_realizing hy
  have h := (d.treeH_spec (x * y) (d.DH.mul_mem hx hy)).2 (α * β) (by rw [map_mul, hα, hβ])
  rw [Rat.treeOfRat_mul, hαt, hβt] at h
  exact h

/-- The complexity of a finite sum is at most the sum of the complexities. -/
theorem treeH_le_sum {d : Prop51Data Γ P DN} {ι : Type*} (s : Finset ι) (f : ι → P)
    (hf : ∀ i ∈ s, f i ∈ d.DH) :
    Tree.le (d.treeH (∑ i ∈ s, f i)) (∑ i ∈ s, d.treeH (f i)) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, treeH_zero]
    exact Tree.le_refl _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Tree.le_trans
      (treeH_le_add d (hf a (Finset.mem_insert_self a s))
        (d.DH.sum_mem fun i hi => hf i (Finset.mem_insert_of_mem hi)))
      (Tree.le_add (Tree.le_refl _) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- The complexity is bounded by the complexity before conjugation by `Φ (ofGroup (t^k))`, a unit
of complexity one. -/
theorem treeH_conj_le (d : Prop51Data Γ P DN) (k : ℤ) {z : P} (hz : z ∈ d.DH) :
    Tree.le (d.treeH (d.Φ (RatU.ofGroup (d.t ^ k)) * z * d.Φ (RatU.ofGroup (d.t ^ (-k)))))
      (d.treeH z) := by
  have hmem : d.Φ (RatU.ofGroup (d.t ^ k)) ∈ d.DH := d.map_mem _
  have hmem' : d.Φ (RatU.ofGroup (d.t ^ (-k))) ∈ d.DH := d.map_mem _
  have h1 : Tree.le (d.treeH (d.Φ (RatU.ofGroup (d.t ^ k)) * z * d.Φ (RatU.ofGroup (d.t ^ (-k)))))
      (d.treeH (d.Φ (RatU.ofGroup (d.t ^ k)) * z)) := by
    have h := treeH_le_mul d (d.DH.mul_mem hmem hz) hmem'
    rw [treeH_ofGroup d (d.t ^ (-k)), mul_one] at h
    exact h
  have h2 : Tree.le (d.treeH (d.Φ (RatU.ofGroup (d.t ^ k)) * z)) (d.treeH z) := by
    have h := treeH_le_mul d hmem hz
    rw [treeH_ofGroup d (d.t ^ k), one_mul] at h
    exact h
  exact Tree.le_trans h1 h2

/-- The complexity is invariant under conjugation by `Φ (ofGroup (t^k))`. -/
theorem treeH_conj_eq (d : Prop51Data Γ P DN) (k : ℤ) {z : P} (hz : z ∈ d.DH) :
    d.treeH (d.Φ (RatU.ofGroup (d.t ^ k)) * z * d.Φ (RatU.ofGroup (d.t ^ (-k)))) =
      d.treeH z := by
  have hmem : d.Φ (RatU.ofGroup (d.t ^ k)) ∈ d.DH := d.map_mem _
  have hmem' : d.Φ (RatU.ofGroup (d.t ^ (-k))) ∈ d.DH := d.map_mem _
  refine Tree.le_antisymm (treeH_conj_le d k hz) ?_
  have hcomm : d.Φ (RatU.ofGroup (d.t ^ (-k))) * d.Φ (RatU.ofGroup (d.t ^ k)) = 1 := by
    rw [← map_mul, ← RatU.ofGroup_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      RatU.ofGroup_one, map_one]
  have h3 := treeH_conj_le d (-k) (d.DH.mul_mem (d.DH.mul_mem hmem hz) hmem')
  have h4 : d.Φ (RatU.ofGroup (d.t ^ (-k))) * (d.Φ (RatU.ofGroup (d.t ^ k)) * z *
      d.Φ (RatU.ofGroup (d.t ^ (-k)))) * d.Φ (RatU.ofGroup (d.t ^ (-(-k)))) = z := by
    simp only [neg_neg]
    calc d.Φ (RatU.ofGroup (d.t ^ (-k))) * (d.Φ (RatU.ofGroup (d.t ^ k)) * z *
        d.Φ (RatU.ofGroup (d.t ^ (-k)))) * d.Φ (RatU.ofGroup (d.t ^ k))
        = (d.Φ (RatU.ofGroup (d.t ^ (-k))) * d.Φ (RatU.ofGroup (d.t ^ k))) * z *
          (d.Φ (RatU.ofGroup (d.t ^ (-k))) * d.Φ (RatU.ofGroup (d.t ^ k))) := by
          noncomm_ring
      _ = z := by
          rw [hcomm, one_mul, mul_one]
  rw [h4] at h3
  exact h3

/-- The complexity of the `⋄`-inverse of `x` is at most the double exponential of the complexity
of `x`: the `⋄` of a realising element realises `x⋄` and has complexity `exp (exp (Tree_H x))`. -/
theorem treeH_ratOp_le (d : Prop51Data Γ P DN) {x : P} (hx : x ∈ d.DH) :
    Tree.le (d.treeH ((d.rDH.ratOp ⟨x, hx⟩ : ↥d.DH) : P))
      (Tree.exp (Tree.exp (d.treeH x))) := by
  by_cases hx0 : x = 0
  · subst hx0
    have h0 : ((d.rDH.ratOp (⟨(0 : P), hx⟩ : ↥d.DH) : ↥d.DH) : P) = 0 := by
      rw [show (⟨(0 : P), hx⟩ : ↥d.DH) = 0 from rfl, d.ratOp_zero]
      simp
    have hA : d.treeH ((d.rDH.ratOp (⟨(0 : P), hx⟩ : ↥d.DH) : ↥d.DH) : P) = 0 := by
      rw [h0]
      simpa using (d.treeH_eq_zero_iff d.DH.zero_mem).mpr rfl
    rw [hA]
    exact Tree.le_zero _
  · obtain ⟨α, hα, hαt⟩ := d.exists_realizing hx
    have hα0 : α ≠ 0 := fun h => hx0 (by rw [← hα, h, map_zero])
    have hΦ : d.Φ (RatU.rational.ratOp α) = ((d.rDH.ratOp ⟨x, hx⟩ : ↥d.DH) : P) := by
      change (((d.Φ.codRestrict d.DH d.map_mem) (RatU.rational.ratOp α) : ↥d.DH) : P) = _
      rw [d.Φ_rat.map_rat]
      rw [show d.Φ.codRestrict d.DH d.map_mem α = (⟨x, hx⟩ : ↥d.DH) from Subtype.ext hα]
    have h := (d.treeH_spec _ (d.rDH.ratOp ⟨x, hx⟩).2).2 (RatU.rational.ratOp α) hΦ
    rw [Rat.treeOfRat_rat_rational hα0, hαt] at h
    exact h

/-- The image of a monomial of `D_{N,P}((t;τ))` under `laurentEmbed`: `a t^k ↦ Φ(t^k) · a`. -/
theorem laurentEmbed_coeff_mul_T (d : Prop51Data Γ P DN) (k : ℤ) (a : ↥DN) :
    d.laurentEmbed (skewLaurentCoeff ↥DN a * ↑((skewLaurentSeriesT ↥DN) ^ k)) =
      d.coeffToP a * d.Φ (RatU.ofGroup (d.t ^ k)) := by
  rw [map_mul, d.laurentEmbed_coeff]
  congr 1
  exact (ofGroup_t_pow d k).symm

end Prop51

end Work.ORHughesFree

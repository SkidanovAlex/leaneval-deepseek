/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The image of the group `U` in `Rat(U)`, and the elements of complexity `1`

[JZLA20, Lemma 4.3(ii)] says that `Tree(α) = 1_T` if and only if `α ∈ U`, and
[JZLA20, Lemma 4.3(i)] that `Tree(α) = 0_T` if and only if `α = 0`.  These are the two facts on
which the base case of the complexity induction of [JZLA20, Proposition 5.1] and of
[JZLA20, Theorem 6.1] rests.

This file provides the image `ofGroup u = u · 1` of `u : U` in `Rat(U)` (a multiplicative map
`U →* Rat(U)` by `smul_mul`), the identification `Tree (ofGroup u) = 1`, and the *converse*
`Tree x = 1 → x = ofGroup u`.  The converse is where the axiom `smulRight_one` is used: it is
what makes `Rat(U)` behave like the model `ℕ[U ♮ X]` of [JZLA20, §4.2], in which the words of
length one are exactly the elements of `U` (so that `Tree x = 1` forces `x` to be a single
group element).

The proof of the converse is an induction on the term structure of `Rat(U)`
(`Rat/RTerm.lean`), using the two cancellation statements
`Tree (x + y) = 1 ↔ (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = 1)` and `Tree (x * y) = 1 ↔ x = 1 ∧ y = 1`
for the tree semiring.
-/
import Mathlib
import Submission.Work.ORHughesFree.Rat.ratComplexity_model
import Submission.Work.ORHughesFree.Rat.Source
import Submission.Work.ORHughesFree.Tree.mulEqOne

set_option autoImplicit false

namespace Work.ORHughesFree

namespace Tree

/-- The family of a tree is the singleton `{0}` exactly for the one-edge tree. -/
theorem fam_eq_singleton_zero_iff (x : Tree) : fam x = ({0} : Multiset Tree) ↔ x = 1 := by
  constructor
  · intro h
    have h2 : ((fam x).map Tree.exp).sum = Tree.exp 0 := by
      rw [h, Multiset.map_singleton, Multiset.sum_singleton]
    rw [Tree.sum_fam] at h2
    exact h2
  · rintro rfl
    exact Tree.fam_exp 0

/-- `exp` is injective: its family is a singleton. -/
theorem exp_injective : Function.Injective (Tree.exp : Tree → Tree) := by
  intro x y h
  have h' : fam (Tree.exp x) = fam (Tree.exp y) := by rw [h]
  rw [Tree.fam_exp, Tree.fam_exp, Multiset.singleton_inj] at h'
  exact h'

/-- `exp x` is the one-edge tree if and only if `x` is the one-vertex tree. -/
@[simp] theorem exp_eq_one_iff (x : Tree) : Tree.exp x = 1 ↔ x = 0 := by
  rw [show (1 : Tree) = Tree.exp 0 from rfl]
  exact ⟨fun h => Tree.exp_injective h, fun h => by rw [h]⟩

/-- A sum of trees is the one-edge tree only if one summand is `1` and the other is `0`. -/
theorem add_eq_one_iff (a b : Tree) : a + b = 1 ↔ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by
  constructor
  · intro h
    have hsum : fam a + fam b = ({0} : Multiset Tree) := by
      rw [← Tree.fam_add, h]
      exact Tree.fam_exp 0
    have hc : (fam a).card + (fam b).card = 1 := by
      have := congrArg Multiset.card hsum
      simpa using this
    rcases Nat.add_eq_one_iff.mp hc with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have ha' : fam a = 0 := Multiset.card_eq_zero.mp ha
      have hb' : fam b = ({0} : Multiset Tree) := by
        have h' := hsum
        rw [ha'] at h'
        simpa using h'
      exact Or.inr ⟨Tree.fam_eq_zero_iff.mp ha', (Tree.fam_eq_singleton_zero_iff b).mp hb'⟩
    · have hb' : fam b = 0 := Multiset.card_eq_zero.mp hb
      have ha' : fam a = ({0} : Multiset Tree) := by
        have h' := hsum
        rw [hb'] at h'
        simpa using h'
      exact Or.inl ⟨(Tree.fam_eq_singleton_zero_iff a).mp ha', Tree.fam_eq_zero_iff.mp hb'⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rw [add_zero]
    · rw [zero_add]

end Tree

namespace RatU

variable {U : Type} [Group U]

/-- **The image of `u : U` in `Rat(U)`**: the element `u · 1`.  By `smul_mul` this is
multiplicative in `u`. -/
noncomputable def ofGroup (u : U) : RatU U := RatU.smul u 1

theorem ofGroup_def (u : U) : ofGroup u = RatU.smul u 1 := rfl

theorem ofGroup_eq_rational (u : U) : ofGroup u = (RatU.rational (U := U)).smul u 1 := rfl

/-- The left action is left multiplication by the image of the group element. -/
theorem smul_eq_ofGroup_mul (u : U) (x : RatU U) :
    RatU.smul u x = ofGroup u * x :=
  (RatU.rational (U := U)).smul_eq_mul u x

/-- The right action is right multiplication by the image of the group element (this is the axiom
`smulRight_one`). -/
theorem smulRight_eq_mul_ofGroup (x : RatU U) (u : U) :
    RatU.smulRight x u = x * ofGroup u := by
  rw [show RatU.smulRight x u = (RatU.rational (U := U)).smulRight x u from rfl,
    (RatU.rational (U := U)).smulRight_eq_mul, (RatU.rational (U := U)).smulRight_one]
  rfl

@[simp] theorem ofGroup_one : ofGroup (1 : U) = 1 := (RatU.rational (U := U)).smul_one_one

theorem ofGroup_mul (u v : U) : ofGroup (u * v) = ofGroup u * ofGroup v := by
  rw [ofGroup_def, ofGroup_def, ofGroup_def]
  exact (RatU.rational (U := U)).smul_mul u v

/-- `ofGroup u` is a unit of `Rat(U)`, hence not a zero divisor: `ofGroup u * (w * ofGroup v) = 0`
if and only if `w = 0`. -/
theorem ofGroup_mul_eq_zero_iff (u v : U) (w : RatU U) :
    ofGroup u * (w * ofGroup v) = 0 ↔ w = 0 := by
  have hvu : ofGroup v * ofGroup v⁻¹ = 1 := by
    rw [← ofGroup_mul, mul_inv_cancel, ofGroup_one]
  have huv : ofGroup u⁻¹ * ofGroup u = 1 := by
    rw [← ofGroup_mul, inv_mul_cancel, ofGroup_one]
  constructor
  · intro h
    have h' : ofGroup u⁻¹ * ((ofGroup u * (w * ofGroup v)) * ofGroup v⁻¹) = 0 := by
      rw [h, zero_mul, mul_zero]
    rw [← mul_assoc, ← mul_assoc, huv, one_mul, mul_assoc, hvu, mul_one] at h'
    exact h'
  · rintro rfl; simp

/-- The image of `U` in `Rat(U)` as a multiplicative map. -/
noncomputable def ofGroupHom : U →* RatU U where
  toFun := ofGroup
  map_one' := ofGroup_one
  map_mul' := ofGroup_mul

@[simp] theorem ofGroupHom_apply (u : U) : ofGroupHom u = ofGroup u := rfl

theorem mk_smulL_one (u : U) : (mk (RTerm.smulL u RTerm.o) : RatU U) = ofGroup u := rfl

end RatU

namespace Rat

variable {U : Type} [Group U]

theorem treeOfRat_smul (u : U) (x : RatU U) :
    treeOfRat U (RatU.smul u x) = treeOfRat U x := by
  have h1 : RatU.lift Tree (treeRational U) ((RatU.rational (U := U)).smul u x) =
      (treeRational U).smul u (RatU.lift Tree (treeRational U) x) :=
    (RatU.lift_isHom Tree (treeRational U)).map_smul u x
  have h2 : (treeRational U).smul u (RatU.lift Tree (treeRational U) x) =
      RatU.lift Tree (treeRational U) x := rfl
  exact h1.trans h2

theorem treeOfRat_smulRight (x : RatU U) (u : U) :
    treeOfRat U (RatU.smulRight x u) = treeOfRat U x := by
  have h1 : RatU.lift Tree (treeRational U) ((RatU.rational (U := U)).smulRight x u) =
      (treeRational U).smulRight (RatU.lift Tree (treeRational U) x) u :=
    (RatU.lift_isHom Tree (treeRational U)).map_smulRight x u
  have h2 : (treeRational U).smulRight (RatU.lift Tree (treeRational U) x) u =
      RatU.lift Tree (treeRational U) x := rfl
  exact h1.trans h2

/-- [JZLA20, Lemma 4.3(ii)], forward form: the image of a group element has complexity `1`. -/
@[simp] theorem treeOfRat_ofGroup (u : U) : treeOfRat U (RatU.ofGroup u) = 1 := by
  rw [RatU.ofGroup_def, treeOfRat_smul u (1 : RatU U), treeOfRat_one]

/-- **[JZLA20, Lemma 4.3(ii)]**: an element of `Rat(U)` has complexity `1` if and only if it is
the image of a group element. -/
theorem treeOfRat_eq_one_iff (x : RatU U) : treeOfRat U x = 1 ↔ ∃ u : U, x = RatU.ofGroup u := by
  refine ⟨?_, ?_⟩
  · revert x
    refine fun x => Quotient.inductionOn x ?_
    intro t
    show Rat.treeOfRat U (RatU.mk t) = 1 → ∃ u : U, RatU.mk t = RatU.ofGroup u
    induction t with
    | z =>
        intro h
        rw [show (RatU.mk (RTerm.z : RTerm U) : RatU U) = 0 from rfl, Rat.treeOfRat_zero] at h
        exact absurd h (fun hh => Tree.one_ne_zero hh.symm)
    | o =>
        intro _
        exact ⟨1, by rw [RatU.ofGroup_one]; exact RatU.mk_one⟩
    | add a b ha hb =>
        intro h
        rw [RatU.mk_add, Rat.treeOfRat_add] at h
        rcases (Tree.add_eq_one_iff _ _).mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · obtain ⟨u, hu⟩ := ha h1
          have hb0 : RatU.mk b = 0 := (Rat.treeOfRat_eq_zero_iff U _).mp h2
          exact ⟨u, by rw [RatU.mk_add, hu, hb0, add_zero]⟩
        · obtain ⟨u, hu⟩ := hb h2
          have ha0 : RatU.mk a = 0 := (Rat.treeOfRat_eq_zero_iff U _).mp h1
          exact ⟨u, by rw [RatU.mk_add, hu, ha0, zero_add]⟩
    | mul a b ha hb =>
        intro h
        rw [RatU.mk_mul, Rat.treeOfRat_mul] at h
        obtain ⟨h1, h2⟩ := (Tree.mulEqOne _ _).mp h
        obtain ⟨u, hu⟩ := ha h1
        obtain ⟨v, hv⟩ := hb h2
        exact ⟨u * v, by rw [RatU.mk_mul, hu, hv, RatU.ofGroup_mul]⟩
    | rat a _ha =>
        intro h
        rw [RatU.mk_rat] at h
        by_cases hz : Rat.treeOfRat U (RatU.mk a) = 0
        · have hx : RatU.mk a = 0 := (Rat.treeOfRat_eq_zero_iff U _).mp hz
          rw [hx, RatU.ratOp_zero, Rat.treeOfRat_zero] at h
          exact absurd h (fun hh => Tree.one_ne_zero hh.symm)
        · have hx0 : RatU.mk a ≠ 0 := fun h0 => hz ((Rat.treeOfRat_eq_zero_iff U _).mpr h0)
          rw [Rat.treeOfRat_rat hx0] at h
          exact absurd h (fun hh => Tree.exp_ne_zero _ ((Tree.exp_eq_one_iff _).mp hh))
    | smulL u a ha =>
        intro h
        rw [RatU.mk_smulL, Rat.treeOfRat_smul] at h
        obtain ⟨v, hv⟩ := ha h
        refine ⟨u * v, ?_⟩
        rw [RatU.mk_smulL, hv, RatU.smul_eq_ofGroup_mul, RatU.ofGroup_mul]
    | smulR u a ha =>
        intro h
        rw [RatU.mk_smulR, Rat.treeOfRat_smulRight] at h
        obtain ⟨v, hv⟩ := ha h
        refine ⟨v * u, ?_⟩
        rw [RatU.mk_smulR, hv, RatU.smulRight_eq_mul_ofGroup, RatU.ofGroup_mul]
  · rintro ⟨u, rfl⟩
    exact Rat.treeOfRat_ofGroup u

end Rat

end Work.ORHughesFree

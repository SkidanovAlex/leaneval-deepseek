/-
Copyright (c) 2024. All rights reserved.

# The `𝔽₂`-vector spaces `V = C/A`, `W = A/A²`, `U = A²/A⁴` for `SZ/lemma8`

This file builds the elementary-abelian `2`-groups occurring in the proof of Higman's Lemma 8
(`Submission/Work/Higman/SZ/lemma8.lean`) as `ZMod 2`-modules: the basic instance plumbing
(commutativity of the relevant quotients, exponent-two module structures).
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.powSub_C_eq_of_cover
import Submission.Work.Higman.SZ.eigen_arg

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.Higman.SZ

open scoped commutatorElement

/-! ## Commutativity -/

/-- A subgroup every two of whose elements commute is a `CommGroup`. -/
def commGroup_subtype_of_abelian {G : Type*} [Group G] {A : Subgroup G}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : CommGroup A where
  mul_comm x y := Subtype.ext (hAab x x.2 y y.2)

/-- A quotient of a group by a normal subgroup containing the commutator subgroup is commutative. -/
def commGroup_quot_of_commutator_le {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (h : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ N) : CommGroup (G ⧸ N) where
  __ := QuotientGroup.Quotient.group N
  mul_comm x y := by
    induction x using QuotientGroup.induction_on with
    | H x =>
      induction y using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        refine QuotientGroup.eq.mpr ?_
        have hmem : ⁅y⁻¹, x⁻¹⁆ ∈ N :=
          (Subgroup.commutator_le.mp h) y⁻¹ (Subgroup.mem_top _) x⁻¹ (Subgroup.mem_top _)
        have hkey : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
          rw [commutatorElement_def]
          group
        rw [hkey]
        exact hmem

/-! ## Exponent-two module structures -/

/-- An abelian group of exponent two is a `ZMod 2`-module. -/
def module_zmod2_of_sq_one {G : Type*} [CommGroup G] (h : ∀ x : G, x * x = 1) :
    Module (ZMod 2) (Additive G) :=
  AddCommGroup.zmodModule fun x => by
    rw [show (2 : ℕ) • x = x + x from two_nsmul x]
    have hx : x + x = Additive.ofMul ((Additive.toMul x) * (Additive.toMul x)) := rfl
    rw [hx, h]
    rfl

/-! ## A by-hand `ZMod 2`-module structure -/

/-- `ZMod 2` has two elements. -/
theorem zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- An additive commutative monoid of exponent two is a `ZMod 2`-module, the scalar action being
built by hand from the two elements of `ZMod 2`.  (The generic `AddCommGroup.zmodModule` is
unusable on the quotients arising below; see `NOTES_lemma8.md`.) -/
def moduleZModTwoOfAddSelfEqZero (M : Type*) [AddCommMonoid M] (h : ∀ x : M, x + x = 0) :
    Module (ZMod 2) M where
  smul c x := c.val • x
  one_smul x := by
    show ((1 : ZMod 2).val) • x = x
    rw [show ((1 : ZMod 2).val) = 1 from rfl]
    exact one_nsmul x
  mul_smul a b x := by
    rcases zmod2_eq_zero_or_one a with rfl | rfl <;> rcases zmod2_eq_zero_or_one b with rfl | rfl
    · show (((0 : ZMod 2) * 0).val) • x = ((0 : ZMod 2).val) • (((0 : ZMod 2).val) • x)
      rw [show (0 : ZMod 2) * 0 = 0 from rfl, show ((0 : ZMod 2).val) = 0 from rfl]
      simp only [zero_nsmul]
    · show (((0 : ZMod 2) * 1).val) • x = ((0 : ZMod 2).val) • (((1 : ZMod 2).val) • x)
      rw [show (0 : ZMod 2) * 1 = 0 from rfl, show ((0 : ZMod 2).val) = 0 from rfl,
        show ((1 : ZMod 2).val) = 1 from rfl]
      simp only [zero_nsmul, one_nsmul]
    · show (((1 : ZMod 2) * 0).val) • x = ((1 : ZMod 2).val) • (((0 : ZMod 2).val) • x)
      rw [show (1 : ZMod 2) * 0 = 0 from rfl, show ((1 : ZMod 2).val) = 1 from rfl,
        show ((0 : ZMod 2).val) = 0 from rfl]
      simp only [zero_nsmul, one_nsmul]
    · show (((1 : ZMod 2) * 1).val) • x = ((1 : ZMod 2).val) • (((1 : ZMod 2).val) • x)
      rw [show (1 : ZMod 2) * 1 = 1 from rfl, show ((1 : ZMod 2).val) = 1 from rfl]
      simp only [one_nsmul]
  smul_add c x y := nsmul_add x y c.val
  smul_zero c := nsmul_zero c.val
  add_smul a b x := by
    rcases zmod2_eq_zero_or_one a with rfl | rfl <;> rcases zmod2_eq_zero_or_one b with rfl | rfl
    · show (((0 : ZMod 2) + 0).val) • x = ((0 : ZMod 2).val) • x + ((0 : ZMod 2).val) • x
      rw [show (0 : ZMod 2) + 0 = 0 from rfl, show ((0 : ZMod 2).val) = 0 from rfl]
      simp only [zero_nsmul, zero_add]
    · show (((0 : ZMod 2) + 1).val) • x = ((0 : ZMod 2).val) • x + ((1 : ZMod 2).val) • x
      rw [show (0 : ZMod 2) + 1 = 1 from rfl, show ((0 : ZMod 2).val) = 0 from rfl,
        show ((1 : ZMod 2).val) = 1 from rfl]
      simp only [zero_nsmul, one_nsmul, zero_add]
    · show (((1 : ZMod 2) + 0).val) • x = ((1 : ZMod 2).val) • x + ((0 : ZMod 2).val) • x
      rw [show (1 : ZMod 2) + 0 = 1 from rfl, show ((1 : ZMod 2).val) = 1 from rfl,
        show ((0 : ZMod 2).val) = 0 from rfl]
      simp only [zero_nsmul, one_nsmul, add_zero]
    · show (((1 : ZMod 2) + 1).val) • x = ((1 : ZMod 2).val) • x + ((1 : ZMod 2).val) • x
      rw [show (1 : ZMod 2) + 1 = 0 from by decide, show ((1 : ZMod 2).val) = 1 from rfl,
        show ((0 : ZMod 2).val) = 0 from rfl]
      simp only [zero_nsmul, one_nsmul, h x]
  zero_smul x := by
    show ((0 : ZMod 2).val) • x = 0
    rw [show ((0 : ZMod 2).val) = 0 from rfl]
    exact zero_nsmul x

end Work.Higman.SZ

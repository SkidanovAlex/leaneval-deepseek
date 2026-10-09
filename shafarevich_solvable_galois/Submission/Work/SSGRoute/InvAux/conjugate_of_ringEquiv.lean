import Mathlib
import Submission.Work.SSGRoute.InvAux
import Submission.Work.SSGRoute.InvAux.eq_of_fixes_fixSub
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Involutions of `ℚ̄` with isomorphic fixed fields are conjugate

Let `c₁, c₂` be non-trivial involutive ring automorphisms of `ℚ̄` (`c * c = 1`, `c ≠ 1`), and
suppose that their fixed fields `Fᵢ = ℚ̄^{cᵢ}` are isomorphic as rings,
`e : F₁ ≃+* F₂`.  Then `c₂ = σ c₁ σ⁻¹` for some ring automorphism `σ` of `ℚ̄`.

The proof has two halves.

* *Extension.*  An involution of a field `Ω` of characteristic zero has the property that every
  element of `Ω` satisfies an explicit quadratic equation over its fixed field, hence `Ω` is
  algebraic over `Fᵢ`.  As `Ω = ℚ̄` is algebraically closed, it is therefore an algebraic closure
  of both `F₁` and `F₂`, and Mathlib's `IsAlgClosure.equivOfEquiv` upgrades `e` to a ring
  automorphism `σ` of `ℚ̄` with `σ a = e a` for `a ∈ F₁`.

* *Uniqueness.*  `σ c₁ σ⁻¹` is again an involution `≠ 1` of `ℚ̄`, and it fixes `F₂ = σ F₁`
  pointwise.  An involution of a field of characteristic zero is determined by the fixed field of
  any *other* involution that it contains (`eq_of_fixes_fixSub`), so `σ c₁ σ⁻¹ = c₂`.

Together with the (independent) fact that the fixed fields of any two non-trivial involutions of
`ℚ̄` are isomorphic, this is the conjugacy statement used in
`Work.SSGRoute.involutions_eq_one_or_conjugate`.
-/

namespace Work.SSGRoute.InvAux

open Polynomial

section Algebraic

variable {Ω : Type*} [Field Ω]

/-- Every element of a field `Ω` of characteristic zero is algebraic over the fixed field of any
involutive automorphism `c` of `Ω`: `(x - (x + c x)/2)² = ((x - c x)/2)²` exhibits a non-zero
quadratic polynomial over `Ω^c` annihilating `x`. -/
theorem isAlgebraic_over_fixSub [CharZero Ω] {c : Ω ≃+* Ω} (hc : c * c = 1) (x : Ω) :
    IsAlgebraic ↥(fixSub c) x := by
  obtain ⟨a, ha, e, he, hq⟩ := exists_quadratic hc x
  let aF : ↥(fixSub c) := ⟨a, ha⟩
  let eF : ↥(fixSub c) := ⟨e, he⟩
  have hcoea : algebraMap ↥(fixSub c) Ω aF = a := rfl
  have hcoee : algebraMap ↥(fixSub c) Ω eF = e := rfl
  refine ⟨X ^ 2 - C (2 * aF) * X + C (aF ^ 2 - eF), ?_, ?_⟩
  · intro hzero
    have hdeg : (X ^ 2 - C (2 * aF) * X + C (aF ^ 2 - eF) :
        Polynomial ↥(fixSub c)).natDegree = 2 := by
      compute_degree!
    rw [hzero] at hdeg
    simp at hdeg
  · show (aeval x) (X ^ 2 - C (2 * aF) * X + C (aF ^ 2 - eF) :
        Polynomial ↥(fixSub c)) = 0
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_ofNat, hcoea, hcoee]
    linear_combination hq

/-- A field of characteristic zero is algebraic over the fixed field of any involution of it. -/
theorem algebra_isAlgebraic_over_fixSub [CharZero Ω] {c : Ω ≃+* Ω} (hc : c * c = 1) :
    Algebra.IsAlgebraic ↥(fixSub c) Ω :=
  Algebra.IsAlgebraic.mk fun x => isAlgebraic_over_fixSub hc x

end Algebraic

theorem conjugate_of_ringEquiv {c₁ c₂ : SSGRoute.QBar ≃+* SSGRoute.QBar}
    (hc₁ : c₁ * c₁ = 1) (hc₂ : c₂ * c₂ = 1) (hn₁ : c₁ ≠ 1) (hn₂ : c₂ ≠ 1)
    (e : ↥(Work.SSGRoute.InvAux.fixSub c₁) ≃+* ↥(Work.SSGRoute.InvAux.fixSub c₂)) :
    ∃ σ : SSGRoute.QBar ≃+* SSGRoute.QBar, σ * c₁ * σ⁻¹ = c₂ := by
  -- `ℚ̄` is an algebraic closure of the fixed field of either involution.
  have h₁ : IsAlgClosure ↥(fixSub c₁) SSGRoute.QBar :=
    ⟨inferInstance, algebra_isAlgebraic_over_fixSub hc₁⟩
  have h₂ : IsAlgClosure ↥(fixSub c₂) SSGRoute.QBar :=
    ⟨inferInstance, algebra_isAlgebraic_over_fixSub hc₂⟩
  -- Any ring automorphism of `ℚ̄` extending `e` conjugates `c₁` into `c₂`.
  have key : ∀ σ : SSGRoute.QBar ≃+* SSGRoute.QBar,
      (∀ a : ↥(fixSub c₁), σ (a : SSGRoute.QBar) = ((e a : ↥(fixSub c₂)) : SSGRoute.QBar)) →
      σ * c₁ * σ⁻¹ = c₂ := by
    intro σ hσ
    have hd : (σ * c₁ * σ⁻¹) * (σ * c₁ * σ⁻¹) = 1 := by
      rw [show (σ * c₁ * σ⁻¹) * (σ * c₁ * σ⁻¹) = σ * (c₁ * c₁) * σ⁻¹ from by group]
      rw [hc₁]
      group
    have hd1 : σ * c₁ * σ⁻¹ ≠ 1 := by
      intro h
      apply hn₁
      have h2 : (σ * c₁ * σ⁻¹) * σ = 1 * σ := by rw [h]
      rw [show (σ * c₁ * σ⁻¹) * σ = σ * c₁ from by group, one_mul] at h2
      exact mul_left_cancel h2
    have hfix : ∀ x : SSGRoute.QBar, c₂ x = x → (σ * c₁ * σ⁻¹) x = x := by
      intro x hx
      let a : ↥(fixSub c₁) := e.symm ⟨x, hx⟩
      have hσa : σ (a : SSGRoute.QBar) = x := by
        rw [hσ a]; simp [a]
      have hax : (a : SSGRoute.QBar) = σ.symm x := by
        rw [← hσa, RingEquiv.symm_apply_apply]
      have hca : c₁ (a : SSGRoute.QBar) = (a : SSGRoute.QBar) := mem_fixSub.mp a.2
      simp only [RingAut.mul_apply, RingAut.inv_apply]
      rw [← hax, hca, hσa]
    exact eq_of_fixes_fixSub hc₂ hn₂ hd hd1 hfix
  -- `e` extends to an automorphism of the algebraic closure `ℚ̄`.
  refine ⟨IsAlgClosure.equivOfEquiv SSGRoute.QBar SSGRoute.QBar e, key _ ?_⟩
  intro a
  change (IsAlgClosure.equivOfEquiv SSGRoute.QBar SSGRoute.QBar e)
      (algebraMap ↥(fixSub c₁) SSGRoute.QBar a) =
    algebraMap ↥(fixSub c₂) SSGRoute.QBar (e a)
  rw [IsAlgClosure.equivOfEquiv_algebraMap]

end Work.SSGRoute.InvAux

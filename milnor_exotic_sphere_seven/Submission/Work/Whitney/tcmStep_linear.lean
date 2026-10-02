import Mathlib
import Submission.Work.Thom.stepDefs
import Submission.Work.Thom.capRelCohIsoA
import Submission.Work.Thom.step_natural

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

/-!
# Linearity of the model-induction step

`Work.Thom.stepSph` is defined by `Classical.choose` of the *surjectivity* of the cap pullback on a
ball pair, and `Work.Thom.step` as a composite of linear maps applied to it.  Here we record the
`ℤ`-linearity of both, which is what lets the induction's algebra (`step (ε • τ) = ε • step τ`)
go through: a scalar (in particular a sign) can be pulled out of the suspension step.

The proofs use only `Work.Thom.stepSph_spec` (the characterising equation of `stepSph`), the
injectivity of the cap pullback (`Work.Thom.capRelCohIso`) and the linearity of the pullback maps.
-/

namespace Work.Whitney

open Work.Thom

noncomputable section

/-- The cap pullback in the exact form of `Work.Thom.stepSph_spec`, as a linear map. -/
theorem capPullback_eq (B : Type) [TopologicalSpace B] (n : ℕ) :
    relCohMap (capMapPairSph B n) (DiscB B n) (SphB B n)
        (CleanA.capMapPairSph_mem_mLower n) ℤ n
      = relCohMap (capMapPairSph B n) (DiscB B n) (SphB B n)
          (fun q hq => by
            have h1 : capMap n (q.2 : EuclideanSpace ℝ (Fin n)) ∈ mLower n :=
              equator_subset_mLower n (capMap_mem_equator n hq)
            simpa [capMapPairSph] using h1) ℤ n :=
  relCohMap_hcongrA _ _ _ _ _ ℤ n

/-- **Uniqueness form of `Work.Thom.stepSph`**: any class whose cap pullback is the disc transfer
of `τ` is `stepSph B n τ`. -/
theorem eq_stepSph (B : Type) [TopologicalSpace B] (n : ℕ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n))
    (w : RelCoh ℤ n (B × MSph (n + 1)) (SphB B n))
    (h : (relCohMap (capMapPairSph B n) (DiscB B n) (SphB B n)
        (CleanA.capMapPairSph_mem_mLower n) ℤ n).hom w = stepDisc B n τ) :
    w = stepSph B n τ := by
  apply (CleanA.capRelCohIso B n n).1
  rw [capPullback_eq B n, h, ← capPullback_eq B n, stepSph_spec]

/-- `Work.Thom.stepDisc` is additive. -/
theorem stepDisc_add (B : Type) [TopologicalSpace B] (n : ℕ)
    (τ₁ τ₂ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    stepDisc B n (τ₁ + τ₂) = stepDisc B n τ₁ + stepDisc B n τ₂ := by
  simp only [stepDisc]
  exact map_add _ _ _

/-- `Work.Thom.stepDisc` is `ℤ`-linear. -/
theorem stepDisc_zsmul (B : Type) [TopologicalSpace B] (n : ℕ) (c : ℤ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    stepDisc B n (c • τ) = c • stepDisc B n τ := by
  simp only [stepDisc]
  exact map_zsmul _ _ _

/-- **`Work.Thom.stepSph` is additive.** -/
theorem stepSph_add (B : Type) [TopologicalSpace B] (n : ℕ)
    (τ₁ τ₂ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    stepSph B n (τ₁ + τ₂) = stepSph B n τ₁ + stepSph B n τ₂ := by
  refine (eq_stepSph B n (τ₁ + τ₂) (stepSph B n τ₁ + stepSph B n τ₂) ?_).symm
  rw [stepDisc_add, map_add, stepSph_spec, stepSph_spec]

/-- **`Work.Thom.stepSph` is `ℤ`-linear.** -/
theorem stepSph_zsmul (B : Type) [TopologicalSpace B] (n : ℕ) (c : ℤ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    stepSph B n (c • τ) = c • stepSph B n τ := by
  refine (eq_stepSph B n (c • τ) (c • stepSph B n τ) ?_).symm
  rw [stepDisc_zsmul, map_zsmul, stepSph_spec]

/-- **`Work.Thom.step` is `ℤ`-linear in its argument.** -/
theorem step_zsmul (B : Type) [TopologicalSpace B] (n : ℕ) (c : ℤ)
    (τ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    step B n (c • τ) = c • step B n τ := by
  simp only [step]
  rw [stepSph_zsmul]
  simp only [map_zsmul]

/-- `Work.Thom.step` is additive in its argument. -/
theorem step_add (B : Type) [TopologicalSpace B] (n : ℕ)
    (τ₁ τ₂ : RelCoh ℤ n (B × EuclideanSpace ℝ (Fin n)) (Sph B n)) :
    step B n (τ₁ + τ₂) = step B n τ₁ + step B n τ₂ := by
  simp only [step]
  rw [stepSph_add]
  simp only [map_add]

end

end Work.Whitney

import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Momentum.nsqAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Momentum.nsq_norm_PsiC_le`

The mean-free localised box state `PsiC ℓ p ψ = boxFTfun ℓ p ψ − boxMeanR ℓ ψ · boxHat ℓ p`
is *uniformly bounded* when `ψ` is smooth with compact support.

The proof is a direct pointwise estimate, with no Fourier analysis and no continuity
argument.  Since `ψ` is continuous with compact support it is bounded, `‖ψ y‖ ≤ M`.  The two
box-localised shifted integrals of `PsiC` are then estimated by the elementary integral bound
`‖∫_{z ∈ acube ℓ} c z · g (x+z)‖ ≤ B · C · |acube ℓ|` of `nsqAux`:

* `‖boxFTfun ℓ p ψ x‖ ≤ M · |acube ℓ|` (the weight `e^{−i⟪p,z⟫}` has norm `1`),
* `‖boxMeanR ℓ ψ x‖ ≤ ℓ⁻³ · M · |acube ℓ|` (the weight is `ℓ⁻³`),

and `‖PsiC x‖ ≤ ‖boxFTfun x‖ + ‖boxMeanR x‖ · ‖boxHat ℓ p‖` by the triangle inequality.  For
`ℓ > 0` all the constants involved are finite and non-negative.  (The hypothesis `0 < ℓ` is
used only through `acube_lt_top` and `0 ≤ ℓ⁻³`.)
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Uniform boundedness of the mean-free box state.**  For `0 < ℓ` and `ψ` smooth with
compact support, `x ↦ ‖PsiC ℓ p ψ x‖` is bounded by an explicit constant
`M · |acube ℓ| · (1 + ℓ⁻³‖boxHat ℓ p‖)`, where `M` bounds `ψ`. -/
theorem nsq_norm_PsiC_le (ℓ : ℝ) (hℓ : 0 < ℓ) (p : EuclideanSpace ℝ (Fin 3)) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : EuclideanSpace ℝ (Fin 3), ‖Work.BoseKinLoc.Momentum.PsiC ℓ p ψ x‖ ≤ C := by
  obtain ⟨M, hM0, hM⟩ := nsq_exists_norm_le_of_contDiff_hasCompactSupport hψ hcs
  set V : ℝ := (volume (acube ℓ)).toReal with hVdef
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hℓ3 : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
  have hMV : 0 ≤ M * V := mul_nonneg hM0 hV
  -- the Fourier-transform term
  have hft : ∀ x : ℝ³, ‖boxFTfun ℓ p ψ x‖ ≤ M * V := by
    intro x
    have h := nsq_norm_shiftIntegral_le hℓ
      (fun z : ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))))
      (fun y : ℝ³ => (ψ y : ℂ)) (B := 1) (C := M) zero_le_one
      (fun z => by
        rw [show -(Complex.I * (inner ℝ p z : ℂ)) = ((-(inner ℝ p z) : ℝ) : ℂ) * Complex.I
            from by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I])
      (fun y => by simpa using hM y) x
    simpa [boxFTfun, hVdef, one_mul] using h
  -- the box-mean term
  have hI : ∀ x : ℝ³, ‖∫ z in acube ℓ, ψ (x + z)‖ ≤ M * V := by
    intro x
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := acube ℓ)
      (f := fun z : ℝ³ => ψ (x + z)) (C := M) (acube_lt_top ℓ hℓ.le)
      (fun z _ => hM (x + z))
    simpa [Measure.real, hVdef] using h
  have hmr : ∀ x : ℝ³, ‖boxMeanR ℓ ψ x‖ ≤ (ℓ ^ 3)⁻¹ * (M * V) := by
    intro x
    have hcast : boxMeanR ℓ ψ x = (ℓ ^ 3)⁻¹ * ∫ z in acube ℓ, ψ (x + z) := rfl
    have hIx := hI x
    rw [Real.norm_eq_abs] at hIx
    rw [hcast, Real.norm_eq_abs, abs_mul, abs_of_nonneg hℓ3]
    exact mul_le_mul_of_nonneg_left hIx hℓ3
  refine ⟨M * V + (ℓ ^ 3)⁻¹ * (M * V) * ‖Work.OneBodyKin.boxHat ℓ p‖, ?_, ?_⟩
  · exact add_nonneg hMV (mul_nonneg (mul_nonneg hℓ3 hMV) (norm_nonneg _))
  · intro x
    have hhat : ‖(Work.OneBodyKin.boxHat ℓ p : ℂ)‖ = ‖Work.OneBodyKin.boxHat ℓ p‖ := by
      simp [Real.norm_eq_abs]
    have hmrc : ‖(boxMeanR ℓ ψ x : ℂ)‖ = ‖boxMeanR ℓ ψ x‖ := by
      simp [Real.norm_eq_abs]
    have hnorm : ‖(boxMeanR ℓ ψ x : ℂ) * (Work.OneBodyKin.boxHat ℓ p : ℂ)‖
        ≤ (ℓ ^ 3)⁻¹ * (M * V) * ‖Work.OneBodyKin.boxHat ℓ p‖ := by
      rw [norm_mul, hmrc, hhat]
      exact mul_le_mul_of_nonneg_right (hmr x) (norm_nonneg _)
    calc ‖PsiC ℓ p ψ x‖
        = ‖boxFTfun ℓ p ψ x
            - (boxMeanR ℓ ψ x : ℂ) * (Work.OneBodyKin.boxHat ℓ p : ℂ)‖ := by rw [PsiC]
      _ ≤ ‖boxFTfun ℓ p ψ x‖
            + ‖(boxMeanR ℓ ψ x : ℂ) * (Work.OneBodyKin.boxHat ℓ p : ℂ)‖ := norm_sub_le _ _
      _ ≤ M * V + (ℓ ^ 3)⁻¹ * (M * V) * ‖Work.OneBodyKin.boxHat ℓ p‖ :=
            add_le_add (hft x) hnorm

end Work.BoseKinLoc.Momentum

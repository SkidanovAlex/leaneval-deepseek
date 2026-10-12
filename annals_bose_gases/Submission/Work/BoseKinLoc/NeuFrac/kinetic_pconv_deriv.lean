import Mathlib.Tactic.Have
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.FourierDerivEnergy
import Submission.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.NeuFrac.kinetic_pconv_deriv`

The single-direction kinetic energy identity in the `p`-convention of
`Submission.BoseGases.kinFT` (`kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy = 𝓕u((2π)⁻¹•p)`):

    ∫_x ‖∂_k F(x)‖² = (2π)⁻³ ∫_p ⟪p,e_k⟫² ‖kinFT F p‖²      (`e_k = kcStdBasis k`),

i.e. the `k`-th summand of the energy identity (`Σ_k`, cf. `Work.BSKinetic.kinFT_energy_sum`),
here for a **complex** Schwartz function `F`.

The proof combines

* the Fourier form of the kinetic energy in Mathlib's `2π`-convention
  (`Submission.BoseGases.integral_lineDeriv_sq_eq`: `∫_x‖∂_m F‖² = (2π)²∫_ξ ⟪ξ,m⟫²‖𝓕F(ξ)‖²`),
* the convention link `kinFT_eq_fourier` (`kinFT g p = 𝓕g((2π)⁻¹•p)`), and
* the scaling of the Lebesgue integral under `p ↦ (2π)•p` (`integral_scale`, a direct
  instance of `Measure.integral_comp_smul_of_nonneg`).

The weight `⟪p,e_k⟫²` picks up the factor `(2π)²`, the measure the factor `(2π)³`, and the
outer `(2π)⁻³` cancels the `(2π)³`, leaving the two sides equal.
-/

noncomputable section

open MeasureTheory
open scoped Real FourierTransform

namespace Work.BoseKinLoc.NeuFrac

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Scaling of the Lebesgue integral**: `∫_p g p = (2π)³ ∫_ξ g((2π)•ξ)`.

This is `Measure.integral_comp_smul_of_nonneg` with `R = 2π` (and `finrank ℝ ℝ³ = 3`),
solved for the unscaled integral. -/
lemma integral_scale (g : ℝ³ → ℝ) :
    (∫ p : ℝ³, g p) = (2 * Real.pi) ^ 3 * ∫ ξ : ℝ³, g ((2 * Real.pi) • ξ) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hsc := MeasureTheory.Measure.integral_comp_smul_of_nonneg
    (μ := (volume : Measure ℝ³)) g (2 * Real.pi) (hR := hpi.le)
  rw [finrank_euclideanSpace_fin, smul_eq_mul] at hsc
  rw [hsc, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 hpi.ne'), one_mul]

theorem kinetic_pconv_deriv (F : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) (k : Fin 3) :
    (∫ x : EuclideanSpace ℝ (Fin 3),
        ‖fderiv ℝ (F : EuclideanSpace ℝ (Fin 3) → ℂ) x (Submission.BoseGases.kcStdBasis k)‖ ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
          (inner ℝ p (Submission.BoseGases.kcStdBasis k)) ^ 2 *
            ‖Submission.BoseGases.kinFT (F : EuclideanSpace ℝ (Fin 3) → ℂ) p‖ ^ 2 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpne : (2 * Real.pi) ≠ 0 := hpi.ne'
  -- Step 1: the left side is the (`2π`-convention) Fourier form of the kinetic energy.
  have hA : (∫ x : ℝ³,
        ‖fderiv ℝ (F : ℝ³ → ℂ) x (Submission.BoseGases.kcStdBasis k)‖ ^ 2)
      = (2 * Real.pi) ^ 2 * ∫ ξ : ℝ³,
          (inner ℝ ξ (Submission.BoseGases.kcStdBasis k)) ^ 2
            * ‖(𝓕 F) ξ‖ ^ 2 :=
    Submission.BoseGases.integral_lineDeriv_sq_eq F (Submission.BoseGases.kcStdBasis k)
  -- Step 2: the right side, in the same Fourier form.
  have hB : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³,
          (inner ℝ p (Submission.BoseGases.kcStdBasis k)) ^ 2
            * ‖Submission.BoseGases.kinFT (F : ℝ³ → ℂ) p‖ ^ 2)
      = (2 * Real.pi) ^ 2 * ∫ ξ : ℝ³,
          (inner ℝ ξ (Submission.BoseGases.kcStdBasis k)) ^ 2
            * ‖(𝓕 F) ξ‖ ^ 2 := by
    -- (1) unwrap `kinFT` to Mathlib's `𝓕` (`kinFT g p = 𝓕g((2π)⁻¹•p)`).
    have h1 : (∫ p : ℝ³,
            (inner ℝ p (Submission.BoseGases.kcStdBasis k)) ^ 2
              * ‖Submission.BoseGases.kinFT (F : ℝ³ → ℂ) p‖ ^ 2)
        = ∫ p : ℝ³,
            (inner ℝ p (Submission.BoseGases.kcStdBasis k)) ^ 2
              * ‖(𝓕 F) ((2 * Real.pi)⁻¹ • p)‖ ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier, SchwartzMap.fourier_coe]
    rw [h1]
    -- (2) the change of variables `p = (2π) • ξ`.
    set G : ℝ³ → ℝ := fun p =>
        (inner ℝ p (Submission.BoseGases.kcStdBasis k)) ^ 2
          * ‖(𝓕 F) ((2 * Real.pi)⁻¹ • p)‖ ^ 2 with hG
    rw [integral_scale G]
    -- (3) simplify the rescaled integrand: `(2π)²` from the weight, cancellation in the arg.
    have h3 : (∫ ξ : ℝ³, G ((2 * Real.pi) • ξ))
        = (2 * Real.pi) ^ 2 * ∫ ξ : ℝ³,
            (inner ℝ ξ (Submission.BoseGases.kcStdBasis k)) ^ 2
              * ‖(𝓕 F) ξ‖ ^ 2 := by
      have hpt : ∀ ξ : ℝ³, G ((2 * Real.pi) • ξ)
          = (2 * Real.pi) ^ 2 * ((inner ℝ ξ (Submission.BoseGases.kcStdBasis k)) ^ 2
              * ‖(𝓕 F) ξ‖ ^ 2) := by
        intro ξ
        simp only [hG]
        rw [real_inner_smul_left, inv_smul_smul₀ hpne]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul]
    rw [h3]
    -- (4) arithmetic: `(2π)^{-3}·(2π)^3·(2π)² = (2π)²`.
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 hpne), one_mul]
  rw [hA, hB]

end Work.BoseKinLoc.NeuFrac

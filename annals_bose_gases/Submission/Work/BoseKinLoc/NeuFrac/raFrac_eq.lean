import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.integrable_kinFT_sq
import Submission.Work.BSKinetic.plancherel_pconv
import Submission.Work.BoseKinLoc.Residuals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.NeuFrac.raFrac_eq`

The Neumann-resolvent fraction `raFrac` (BS `eq:Neumannineq`) is the `p`-space quadratic
form of the symbol `p²/(p²+(dℓ)⁻²)`.  The pointwise algebraic split

    `p²/(p²+a²) = 1 − a²/(p²+a²)`,   `a² := (dℓ)⁻² > 0`,

together with the `p`-convention Plancherel identity
`(2π)⁻³ ∫_p ‖kinFT u p‖² = ∫_x u(x)²` (`Work.BSKinetic.plancherel_pconv`) gives

    `raFrac ℓ d ψ = ∫_x ψ(x)² − (dℓ)⁻² (2π)⁻³ ∫_p ‖ψ̂(p)‖²/(‖p‖²+(dℓ)⁻²)`.

The two analytic inputs are: the bare density `p ↦ ‖kinFT (ψ:ℂ) p‖²` is integrable
(`Work.BSKinetic.integrable_kinFT_sq`), and dividing it by the strictly positive
`‖p‖²+(dℓ)⁻²` preserves integrability (the multiplier is bounded by `(dℓ)²`).

The hypothesis on `ψ` is `⊤`-smooth (analytic), which strengthens the `C^∞` smoothness
consumed by Plancherel; `ContDiff.of_le le_top` supplies the passage.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real

namespace Work.BoseKinLoc.NeuFrac

set_option maxHeartbeats 800000
set_option autoImplicit false

/-- The elementary algebraic split `b/(b+a)·v = v − a·(v/(b+a))` (`b + a ≠ 0`). -/
lemma div_mul_eq_sub_div (a b v : ℝ) (h : b + a ≠ 0) :
    b / (b + a) * v = v - a * (v / (b + a)) := by
  field_simp
  ring

/-- Pointwise algebraic split of the Neumann symbol:
`p²/(p²+a²)·v = v − a²·(v/(p²+a²))` for `a² = (dℓ)⁻² > 0`. -/
lemma raSym_mul_eq (ℓ d : ℝ) (ha : 0 < (d * ℓ) ^ (-2 : ℤ)) (p : ℝ³) (v : ℝ) :
    raSym ℓ d p * v
      = v - (d * ℓ) ^ (-2 : ℤ) * (v / (‖p‖ ^ 2 + (d * ℓ) ^ (-2 : ℤ))) := by
  have h : ‖p‖ ^ 2 + (d * ℓ) ^ (-2 : ℤ) ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) ha)
  rw [raSym]
  exact div_mul_eq_sub_div _ _ _ h

/-- The `a²`-damped `p`-density is integrable whenever the bare one is: the multiplier
`p ↦ (‖p‖²+a²)⁻¹` is bounded by `a⁻¹`. -/
lemma integrable_div_quad {F : ℝ³ → ℝ} (c : ℝ) (hc : 0 < c) (hF : Integrable F) :
    Integrable (fun p : ℝ³ => F p / (‖p‖ ^ 2 + c)) := by
  have hle : ∀ p : ℝ³, c ≤ ‖p‖ ^ 2 + c := fun p => le_add_of_nonneg_left (sq_nonneg _)
  have hbound : ∀ᵐ p : ℝ³, ‖(fun p : ℝ³ => (‖p‖ ^ 2 + c)⁻¹) p‖ ≤ c⁻¹ :=
    Filter.Eventually.of_forall fun p => by
      have hpos : 0 < ‖p‖ ^ 2 + c := add_pos_of_nonneg_of_pos (sq_nonneg _) hc
      have h1 : (‖p‖ ^ 2 + c)⁻¹ ≤ c⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hc (hle p)
      simpa [Real.norm_eq_abs, abs_of_pos hpos] using h1
  have hcont : Continuous fun p : ℝ³ => (‖p‖ ^ 2 + c)⁻¹ := by
    apply Continuous.inv₀
    · fun_prop
    · intro p
      exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hc)
  refine (hF.bdd_mul hcont.aestronglyMeasurable hbound).congr
    (Filter.Eventually.of_forall fun p => ?_)
  simp [div_eq_mul_inv, mul_comm]

theorem raFrac_eq (ℓ d : ℝ) (hℓ : 0 < ℓ) (hd : 0 < d)
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ ⊤ ψ) (hcs : HasCompactSupport ψ) :
    Work.BoseKinLoc.raFrac ℓ d ψ =
      (∫ x : EuclideanSpace ℝ (Fin 3), (ψ x) ^ 2)
        - (d * ℓ) ^ (-2 : ℤ) * (((2 * Real.pi) ^ 3)⁻¹ *
            ∫ p : EuclideanSpace ℝ (Fin 3), ‖Work.BoseKinLoc.fhat ψ p‖ ^ 2 /
              (‖p‖ ^ 2 + (d * ℓ) ^ (-2 : ℤ))) := by
  have ha : 0 < (d * ℓ) ^ (-2 : ℤ) := by positivity
  have hψs : ContDiff ℝ ∞ ψ := hψ.of_le le_top
  have hFint : Integrable
      (fun p : ℝ³ => ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) p‖ ^ 2) :=
    Work.BSKinetic.integrable_kinFT_sq ψ hψs hcs
  have hGint : Integrable
      (fun p : ℝ³ => ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) p‖ ^ 2 /
        (‖p‖ ^ 2 + (d * ℓ) ^ (-2 : ℤ))) :=
    integrable_div_quad _ ha hFint
  unfold Work.BoseKinLoc.raFrac Work.BoseKinLoc.fhat
  have hpt : ∀ p : ℝ³,
      raSym ℓ d p * ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) p‖ ^ 2
        = ‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) p‖ ^ 2
          - (d * ℓ) ^ (-2 : ℤ) * (‖Submission.BoseGases.kinFT (fun z : ℝ³ => (ψ z : ℂ)) p‖ ^ 2
              / (‖p‖ ^ 2 + (d * ℓ) ^ (-2 : ℤ))) :=
    fun p => raSym_mul_eq ℓ d ha p _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_sub hFint (hGint.const_mul _), integral_const_mul, mul_sub,
    Work.BSKinetic.plancherel_pconv ψ hψs hcs]
  ring

end Work.BoseKinLoc.NeuFrac

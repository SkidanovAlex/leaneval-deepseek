import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.weight_algebra_fts
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.R

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-!
# Integrability of `u²·∂_z(z w²)·σ` from integrability of `u²·w²·σ`

With the radial weight `w z = (1+z)²/z²` (so that `z w² = (1+z)⁴/z³`), the differentiated
weight factors through the weight itself:

  `∂_z(z w²) = ((z-3)/(1+z))·w²`   for `z > 0`,

and the factor `(z-3)/(1+z)` is **bounded by `3` in absolute value on `z ≥ 0`**.  Hence

  `u²·∂_z(z w²)·σ = ((z-3)/(1+z))·(u²·w²·σ)`   away from the null set `{z = 0}`,

so the `∂_z(z w²)`-integrand is the given integrand `u²·w²·σ` multiplied by a measurable
function that is bounded almost everywhere; integrability is preserved by
`MeasureTheory.Integrable.mul_bdd`.

This is the `∂_z(z w²)`-slot of the sharp-hypothesis package of the `H⁶` layer: the
`z`-integration by parts there replaces `u²·w²·σ` by `u²·∂_z(z w²)·σ`, and this lemma records
that the replacement preserves integrability (so no regularity of `u` is needed, only the
integrability of the original integrand).

The hypothesis `hσ` (`σ ≥ 0` on `Iθ`) is *not* needed for the implication — the factorisation
above multiplies the *given* integrand by a bounded factor, with no positivity argument — but
it is part of the requested interface.
-/

/-- The differentiated radial weight, factored through the weight itself:
`∂_z(z·w z²) = w z² · ((z-3)/(1+z))` for `z > 0`. -/
private theorem deriv_zw2_factor {z : ℝ} (hz : 0 < z) :
    deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z
      = (Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z)) := by
  rw [Work.FTS.EllipticEst.weight_algebra_fts.2.2.2.1 z (ne_of_gt hz)]
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1z : (1 : ℝ) + z ≠ 0 := by linarith
  rw [Work.Spaces.w]
  field_simp

/-- The factor `(z-3)/(1+z)` is bounded by `3` in absolute value on `z ≥ 0`. -/
private theorem abs_ratio_le_three {z : ℝ} (hz : 0 ≤ z) : |(z - 3) / (1 + z)| ≤ 3 := by
  have h1z : (0 : ℝ) < 1 + z := by linarith
  rw [abs_div, abs_of_pos h1z, div_le_iff₀ h1z]
  have h : |z - 3| ≤ 3 + 3 * z := by
    rw [abs_le]
    constructor <;> linarith
  linarith

theorem zw2_deriv_integrable {u : ℝ → ℝ → ℝ} {σ : ℝ → ℝ}
    (hσ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ σ θ)
    (h1 : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2 * (Work.Spaces.w z) ^ 2 * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => u z θ ^ 2
        * deriv (fun z' => z' * (Work.Spaces.w z') ^ 2) z * σ θ))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  -- Work with the product of the two restricted measures on the quadrant.
  have hm : (volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.IntegrableOn, hm] at h1 ⊢
  -- The sign hypothesis is not needed; record it for the reader.
  have hfnn : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      0 ≤ u z θ ^ 2 * (Work.Spaces.w z) ^ 2 * σ θ := fun z _ θ hθ =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (hσ θ hθ)
  -- The bounded measurable factor `(z-3)/(1+z)`.
  have hg : AEStronglyMeasurable (fun p : ℝ × ℝ => (p.1 - 3) / (1 + p.1))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    have : Measurable (fun p : ℝ × ℝ => (p.1 - 3) / (1 + p.1)) := by fun_prop
    exact this.aestronglyMeasurable
  have hb : ∀ᵐ p ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)),
      ‖(p.1 - 3) / (1 + p.1)‖ ≤ (3 : ℝ) := by
    filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos] with p hp
    rw [Real.norm_eq_abs]
    exact abs_ratio_le_three hp.le
  -- Multiplying the given integrand by the bounded factor stays integrable.
  refine (h1.mul_bdd hg hb).congr ?_
  -- The product is the target integrand, a.e. (everywhere except on `{z = 0}`).
  filter_upwards [Work.FTS.CoercivityFix.Coer1.ae_prod_fst_pos] with p hp
  dsimp only [Function.uncurry]
  rw [deriv_zw2_factor hp]
  ring

end

end Work.FTS.StrongPersist.H6Aux.R

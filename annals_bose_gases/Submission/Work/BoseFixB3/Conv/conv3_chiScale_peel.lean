import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.Conv.conv3_chiScale_peel`

The box-localisation "peel" of the χ-weighted kernel `χ_ℓ(·)·f(· − z)`: for `0 < ℓ` and an
even integrable `f`,

    ∫_{y ∈ acube ℓ} χ_ℓ(y)·f(y − z) dy = (f * χ_ℓ)(z),

where `χ_ℓ = chiScale ℓ = χ((ℓ⁻¹) • ·)` and `conv3` is the Lebesgue convolution
`(f * g)(z) = ∫ w, f w · g (z − w)`.

Mathematically there is nothing to it: `χ_ℓ` is supported in the centred cube
`acube ℓ = [−ℓ/2, ℓ/2]³` (the bump `χ` vanishes outside the ball of radius `1/2`), so
restricting the integral to `acube ℓ` changes nothing; the substitution `w = z − y`
(measure preserving, and `χ_ℓ` is even) then turns the left-hand side into
`∫ w, χ_ℓ(z − w)·f(−w)`, which is `∫ w, f w·χ_ℓ(z − w)` by evenness of `f`.

## Contents

* `chiScale_eq_zero_of_not_mem_acube` — the support statement (`χ_ℓ` vanishes off `acube ℓ`);
* `integral_chiScale_mul_sub` — the substitution `∫ y, χ_ℓ(y)·f(y − z) = ∫ w, χ_ℓ(z − w)·f(w)`;
* `conv3_chiScale_peel` — the requested identity.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Work.BoseFixB3.Conv

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Support of the scaled bump.**  `χ_ℓ` vanishes off the centred cube `acube ℓ`
(for `0 < ℓ`): if `χ_ℓ y ≠ 0` then `‖y‖ ≤ ℓ/2`, hence `y ∈ acube ℓ`. -/
lemma chiScale_eq_zero_of_not_mem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {y : ℝ³}
    (hy : y ∉ Submission.BoseGases.acube ℓ) : Submission.BoseGases.chiScale ℓ y = 0 := by
  by_contra h
  exact hy (Submission.BoseGases.mem_acube_of_norm_le (le_of_lt hℓ)
    (Submission.BoseGases.chiScale_support_le hℓ h))

/-- **The substitution `y ↦ z − y`.**  Since translation and negation preserve Lebesgue
measure and `f` is even,

    `∫ y, χ_ℓ(y)·f(y − z) = ∫ w, χ_ℓ(z − w)·f(w)`. -/
lemma integral_chiScale_mul_sub {ℓ : ℝ} {f : ℝ³ → ℝ}
    (hfeven : ∀ x : ℝ³, f (-x) = f x) (z : ℝ³) :
    (∫ y : ℝ³, Submission.BoseGases.chiScale ℓ y * f (y - z))
      = ∫ w : ℝ³, Submission.BoseGases.chiScale ℓ (z - w) * f w := by
  have h1 := Submission.BoseGases.integral_comp_sub_left
    (g := fun y : ℝ³ => Submission.BoseGases.chiScale ℓ y * f (y - z)) z
  rw [← h1]
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun w => ?_))
  dsimp only
  rw [show z - w - z = -w by abel, hfeven w]

theorem conv3_chiScale_peel {ℓ : ℝ} (hℓ : 0 < ℓ) {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hf : MeasureTheory.Integrable f) (hfeven : ∀ x : EuclideanSpace ℝ (Fin 3), f (-x) = f x)
    (z : EuclideanSpace ℝ (Fin 3)) :
    (∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.chiScale ℓ y * f (y - z))
      = Submission.BoseGases.conv3 f (fun w => Submission.BoseGases.chi ((ℓ⁻¹) • w)) z := by
  -- the integrand vanishes off `acube ℓ`, so the box restriction is immaterial
  have hoff : ∀ y : ℝ³, y ∉ Submission.BoseGases.acube ℓ →
      Submission.BoseGases.chiScale ℓ y * f (y - z) = 0 := fun y hy => by
    rw [chiScale_eq_zero_of_not_mem_acube hℓ hy, zero_mul]
  have hsub := integral_chiScale_mul_sub (ℓ := ℓ) hfeven z
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hoff, hsub]
  -- unfold the convolution and commute the factors
  unfold Submission.BoseGases.conv3
  refine MeasureTheory.integral_congr_ae (Eventually.of_forall (fun w => ?_))
  dsimp only
  rw [mul_comm]
  simp only [Submission.BoseGases.chiScale]

end Work.BoseFixB3.Conv

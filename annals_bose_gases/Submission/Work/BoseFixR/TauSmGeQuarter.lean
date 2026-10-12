import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

/-- **The smoothed kinetic symbol dominates a quarter of `‖q‖²` high above its first kink.**

Unfolding `tauSm`, the first term is `(1-eT)·c²·τ̃(‖q‖/c)` with `c = (2sℓ)⁻¹`, and the
profile `τ̃ = tauProf` satisfies `(max 0 (r-2))² ≤ τ̃ r` (`exists_tauProf`).  On the region
`‖q‖ ≥ 4c` the argument `‖q‖/c` is `≥ 4`, so `τ̃(‖q‖/c) ≥ (‖q‖/c - 2)²` and hence

`(1-eT)·c²·τ̃(‖q‖/c) ≥ (1-eT)·(‖q‖ - 2c)² ≥ (1-eT)·(‖q‖/2)² = (1-eT)/4·‖q‖²`.

The `eT`-weighted second term is nonnegative and is simply discarded. -/
theorem TauSmGeQuarter {eT s d ℓ : ℝ} (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (hs : 0 < s)
    (hℓ : 0 < ℓ) (q : EuclideanSpace ℝ (Fin 3))
    (hq : 4 * (2 * s * ℓ)⁻¹ ≤ ‖q‖) :
    (1 - eT) / 4 * ‖q‖ ^ 2 ≤ Work.BoseBoxFock.tauSm eT s d ℓ q := by
  have hc : (0 : ℝ) < (2 * s * ℓ)⁻¹ := by positivity
  have h1eT : 0 ≤ 1 - eT := by linarith
  have hprof : ∀ r : ℝ, (max 0 (r - 2)) ^ 2 ≤ Work.BoseBoxFock.tauProf r :=
    fun r => Work.BoseBoxFock.tauProf_spec.2.2.1 r
  have hnn_prof : ∀ r : ℝ, 0 ≤ Work.BoseBoxFock.tauProf r :=
    fun r => le_trans (sq_nonneg _) (hprof r)
  -- the one-variable kink bound at `c = (2sℓ)⁻¹`
  have hkink : (‖q‖ - 2 * (2 * s * ℓ)⁻¹) ^ 2
      ≤ ((2 * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖q‖ / (2 * s * ℓ)⁻¹) := by
    have hr2 : 2 ≤ ‖q‖ / (2 * s * ℓ)⁻¹ := by
      rw [le_div_iff₀ hc]; linarith
    have hm : max 0 (‖q‖ / (2 * s * ℓ)⁻¹ - 2) = ‖q‖ / (2 * s * ℓ)⁻¹ - 2 :=
      max_eq_right (by linarith)
    have h1 : (‖q‖ / (2 * s * ℓ)⁻¹ - 2) ^ 2
        ≤ Work.BoseBoxFock.tauProf (‖q‖ / (2 * s * ℓ)⁻¹) := by
      have h := hprof (‖q‖ / (2 * s * ℓ)⁻¹)
      rwa [hm] at h
    have h2 : ((2 * s * ℓ)⁻¹) ^ 2 * (‖q‖ / (2 * s * ℓ)⁻¹ - 2) ^ 2
        = (‖q‖ - 2 * (2 * s * ℓ)⁻¹) ^ 2 := by
      field_simp
    calc (‖q‖ - 2 * (2 * s * ℓ)⁻¹) ^ 2
        = ((2 * s * ℓ)⁻¹) ^ 2 * (‖q‖ / (2 * s * ℓ)⁻¹ - 2) ^ 2 := h2.symm
      _ ≤ ((2 * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖q‖ / (2 * s * ℓ)⁻¹) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  -- the region hypothesis upgrades the kink to `‖q‖²/4`
  have hquarter : ‖q‖ ^ 2 / 4
      ≤ ((2 * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖q‖ / (2 * s * ℓ)⁻¹) := by
    have hge : ‖q‖ / 2 ≤ ‖q‖ - 2 * (2 * s * ℓ)⁻¹ := by linarith
    have hsq : (‖q‖ / 2) ^ 2 ≤ (‖q‖ - 2 * (2 * s * ℓ)⁻¹) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hge 2
    have heq : (‖q‖ / 2) ^ 2 = ‖q‖ ^ 2 / 4 := by ring
    linarith [hsq, heq, hkink]
  rw [Work.BoseBoxFock.tauSm]
  have hroot : (1 - eT) * (‖q‖ ^ 2 / 4)
      ≤ (1 - eT) * (((2 * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖q‖ / (2 * s * ℓ)⁻¹)) :=
    mul_le_mul_of_nonneg_left hquarter h1eT
  have hnn : 0 ≤ eT * ((2 * d * s * ℓ)⁻¹) ^ 2
      * Work.BoseBoxFock.tauProf (‖q‖ / (2 * d * s * ℓ)⁻¹) :=
    mul_nonneg (mul_nonneg heT0 (sq_nonneg _)) (hnn_prof _)
  have hassoc : (1 - eT) * (((2 * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖q‖ / (2 * s * ℓ)⁻¹))
      = (1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖q‖ / (2 * s * ℓ)⁻¹) := by
    ring
  have h4 : (1 - eT) / 4 * ‖q‖ ^ 2 = (1 - eT) * (‖q‖ ^ 2 / 4) := by ring
  linarith [hroot, hnn, hassoc, h4]

end Work.BoseFixR

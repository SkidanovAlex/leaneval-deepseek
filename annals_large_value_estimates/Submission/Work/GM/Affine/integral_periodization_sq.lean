import Mathlib
import Submission.Work.GM.Affine.periodization_tsum_finsum
import Submission.Work.GM.Affine.integral_unit_periodization

/-!
# `Work.GM.Affine.integral_periodization_sq`

The periodisation identity for the square of a continuous compactly supported function:
if `h` vanishes off `[-R, R]` and `K ≥ R + 1` is a natural number, then

`∫_{0}^{1} ∑_{ℓ ∈ [-K, K]} h (y + ℓ)^2 dy = ∫_ℝ h^2`.

The proof has two inputs, both available in this workspace:
* the periodised sum over `ℤ` collapses to the finite window `[-K, K]` on `[0, 1]`
  (because a translate `y + ℓ` with `|ℓ| ≥ K + 1` satisfies `|y + ℓ| ≥ K > R`), which is the
  same reasoning as in `periodization_tsum_finsum`;
* `integral_unit_periodization`, the classical tiling identity
  `∫_0^1 ∑'_ℓ F (ℓ + u) du = ∫_ℝ F`.
-/

namespace Work.GM.Affine

open MeasureTheory
open scoped BigOperators

theorem integral_periodization_sq {h : ℝ → ℝ} (hcont : Continuous h) {R : ℝ}
    (hRf : ∀ y : ℝ, R < |y| → h y = 0) {K : ℕ} (hK : R + 1 ≤ (K : ℝ)) :
    (∫ y in (0 : ℝ)..1, ∑ ℓ ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), (h (y + (ℓ : ℝ))) ^ 2)
      = ∫ y : ℝ, (h y) ^ 2 := by
  -- ## Compact support and integrability of `h²`
  have hsub : Function.support h ⊆ Metric.closedBall (0 : ℝ) (max R 0) := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, Real.norm_eq_abs]
    by_contra hcon
    rw [not_le] at hcon
    exact (Function.mem_support.mp hy) (hRf y (lt_of_le_of_lt (le_max_left R 0) hcon))
  have hcs : HasCompactSupport h :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 (max R 0)) hsub
  have hcs2 : HasCompactSupport (fun y : ℝ => (h y) ^ 2) := by
    refine hcs.mono ?_
    intro y hy
    simp only [Function.mem_support] at hy ⊢
    intro h0
    exact hy (by rw [h0]; norm_num)
  have hcont2 : Continuous (fun y : ℝ => (h y) ^ 2) := hcont.pow 2
  have hint : Integrable (fun y : ℝ => (h y) ^ 2) :=
    hcont2.integrable_of_hasCompactSupport hcs2
  -- ## The periodised sum is a finite sum on `[-1, 1]`
  have hpoint : ∀ u : ℝ, |u| ≤ 1 →
      (∑ ℓ ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), (h (u + (ℓ : ℝ))) ^ 2)
        = (∑' ℓ : ℤ, (h ((ℓ : ℝ) + u)) ^ 2) := by
    intro u hu
    have hzero : ∀ ℓ : ℤ, ℓ ∉ Finset.Icc (-(K : ℤ)) (K : ℤ) →
        (h ((ℓ : ℝ) + u)) ^ 2 = 0 := by
      intro ℓ hℓ
      -- `ℓ < -K` or `K < ℓ`, so in either case `|ℓ| ≥ K + 1 ≥ R + 2 > R + |u|`
      have hℓ' : ℓ < -(K : ℤ) ∨ (K : ℤ) < ℓ := by
        simpa only [Finset.mem_Icc, not_and_or, not_le] using hℓ
      have habs : (K : ℝ) + 1 ≤ |(ℓ : ℝ)| := by
        rcases hℓ' with h | h
        · have h1 : ℓ + 1 ≤ -(K : ℤ) := by omega
          have h2 : (ℓ : ℝ) + 1 ≤ -(K : ℝ) := by exact_mod_cast h1
          have h3 : (K : ℝ) + 1 ≤ -(ℓ : ℝ) := by linarith
          exact h3.trans (neg_le_abs (ℓ : ℝ))
        · have h1 : (K : ℤ) + 1 ≤ ℓ := by omega
          have h2 : (K : ℝ) + 1 ≤ (ℓ : ℝ) := by exact_mod_cast h1
          exact h2.trans (le_abs_self (ℓ : ℝ))
      have hge : R < |(ℓ : ℝ) + u| := by
        have h1 : |(ℓ : ℝ)| - |u| ≤ |(ℓ : ℝ) + u| := by
          have := abs_sub_abs_le_abs_sub (ℓ : ℝ) (-u)
          simpa [abs_neg] using this
        linarith
      rw [hRf ((ℓ : ℝ) + u) hge, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    have hidentity : (∑' ℓ : ℤ, (h ((ℓ : ℝ) + u)) ^ 2)
        = ∑ ℓ ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), (h ((ℓ : ℝ) + u)) ^ 2 :=
      tsum_eq_sum (f := fun ℓ : ℤ => (h ((ℓ : ℝ) + u)) ^ 2)
        (s := Finset.Icc (-(K : ℤ)) (K : ℤ)) hzero
    rw [hidentity]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [add_comm u (ℓ : ℝ)]
  -- ## Assemble
  have hstep : (∫ y in (0 : ℝ)..1,
        ∑ ℓ ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), (h (y + (ℓ : ℝ))) ^ 2)
      = ∫ y in (0 : ℝ)..1, (∑' ℓ : ℤ, (h ((ℓ : ℝ) + y)) ^ 2) :=
    intervalIntegral.integral_congr fun x hx => by
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      exact hpoint x (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩)
  rw [hstep]
  exact integral_unit_periodization (F := fun y : ℝ => (h y) ^ 2) hcont2
    (fun y => sq_nonneg (h y)) hint

end Work.GM.Affine

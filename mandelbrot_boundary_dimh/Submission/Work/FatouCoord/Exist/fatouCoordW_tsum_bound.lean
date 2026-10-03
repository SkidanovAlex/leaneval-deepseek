import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.coordError_bound
import Submission.Work.FatouCoord.Estimate.wMap_re_growth
import Submission.Work.FatouCoord.Estimate.summable_coordError
import Submission.Work.FatouCoord.Estimate.wMap_iterate_deriv_bound

/-!
# The remainder term of the Fatou coordinate is `O(1/w)`

The Fatou coordinate in the chart is `fatouCoordW f (1 - a) w = approxCoord (1 - a) w + R w`
with `R w = ∑' k, coordError f (1 - a) ((wMap f)^[k] w)`.  Here we show that the remainder
satisfies `‖R w‖ ≤ K / Re w` on a right half-plane `{Re w > N}`:

* `Estimate.coordError_bound` gives `‖coordError f (1 - a) v‖ ≤ B / ‖v‖ ^ 2` for `Re v > N₁`;
* `Estimate.wMap_re_growth` gives `Re ((wMap f)^[k] w) ≥ Re w + k/2` for `Re w > N₂`;
* hence `‖coordError f (1 - a) ((wMap f)^[k] w)‖ ≤ B / (Re w + k/2) ^ 2`, and the telescoping
  bound `Estimate.sum_range_inv_sq_le` (applied with `N := 2 * Re w`) shows that the majorant
  series has sum at most `B / (Re w) ^ 2 + 2 B / Re w ≤ 3 B / Re w` for `Re w ≥ 1`.

The norm of the series is then bounded by the series of norms, `‖∑' k, e_k‖ ≤ ∑' k, ‖e_k‖`.
-/

namespace Work.FatouCoord.Exist

open Work.FatouCoord

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- **The majorant series `∑ B / (s + k/2)²`.**  For `B ≥ 0` and `s ≥ 1` the series
`∑_k B / (s + k/2)²` converges with sum at most `3 B / s`.

Indeed `B / (s + k/2)² = 4B / (2s + k)²` and the telescoping estimate
`Estimate.sum_range_inv_sq_le` gives `∑_{k<n} 1/(2s+k)² ≤ 1/(2s)² + 1/(2s)`, whence the partial
sums are at most `B/s² + 2B/s ≤ 3B/s` because `s ≥ 1`. -/
private lemma summable_div_shift_sq {B s : ℝ} (hB : 0 ≤ B) (hs : 1 ≤ s) :
    Summable (fun k : ℕ => B / (s + (k : ℝ) / 2) ^ 2) ∧
      ∑' k : ℕ, B / (s + (k : ℝ) / 2) ^ 2 ≤ 3 * B / s := by
  have hspos : 0 < s := lt_of_lt_of_le one_pos hs
  have h4B : (0 : ℝ) ≤ 4 * B := by linarith
  -- rewriting `s + k/2 = (2s + k)/2`
  have hterm : ∀ k : ℕ, B / (s + (k : ℝ) / 2) ^ 2 = 4 * B / (2 * s + (k : ℝ)) ^ 2 := by
    intro k
    have h1 : (0 : ℝ) < s + (k : ℝ) / 2 := by positivity
    have h2 : (0 : ℝ) < 2 * s + (k : ℝ) := by positivity
    rw [div_eq_div_iff (pow_ne_zero 2 h1.ne') (pow_ne_zero 2 h2.ne')]
    ring
  have hpartial : ∀ n : ℕ, ∑ k ∈ Finset.range n, B / (s + (k : ℝ) / 2) ^ 2 ≤ 3 * B / s := by
    intro n
    have hcongr : ∑ k ∈ Finset.range n, B / (s + (k : ℝ) / 2) ^ 2
        = 4 * B * ∑ k ∈ Finset.range n, 1 / (2 * s + (k : ℝ)) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by rw [hterm k, mul_one_div])
    rw [hcongr]
    have h2 := Estimate.sum_range_inv_sq_le (2 * s) (by linarith) n
    have hb1 := mul_le_mul_of_nonneg_left h2 h4B
    refine le_trans hb1 ?_
    have h3 : 4 * B * (1 / (2 * s) ^ 2 + 1 / (2 * s)) = B / s ^ 2 + 2 * B / s := by
      field_simp
      ring
    rw [h3]
    have h4 : B / s ^ 2 ≤ B / s := by
      refine div_le_div_of_nonneg_left hB hspos ?_
      nlinarith
    have h5 : 3 * B / s = B / s + 2 * B / s := by ring
    linarith [h4, h5]
  exact ⟨summable_of_sum_range_le (fun k => div_nonneg hB (sq_nonneg _)) hpartial,
    Real.tsum_le_of_sum_range_le (fun k => div_nonneg hB (sq_nonneg _)) hpartial⟩

theorem fatouCoordW_tsum_bound {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A') :
    ∃ N K : ℝ, 0 < N ∧ 1 / r < N ∧ 0 ≤ K ∧
      ∀ w : ℂ, N < w.re → ‖fatouCoordW f (1 - a) w - approxCoord (1 - a) w‖ ≤ K / w.re := by
  obtain ⟨N₁, B, _hN₁pos, hBnn, hrN₁, hcErr⟩ := Estimate.coordError_bound hb
  obtain ⟨N₂, _hN₂pos, _hrN₂, hgrowth⟩ := Estimate.wMap_re_growth hb
  obtain ⟨Ns, _hNspos, _hrNs, hsumm⟩ := Estimate.summable_coordError hb
  set N : ℝ := max (max (max N₁ N₂) Ns) 1 + 1 with hNdef
  have hN₁N : N₁ < N := by
    rw [hNdef]
    have h1 : N₁ ≤ max N₁ N₂ := le_max_left _ _
    have h2 : max N₁ N₂ ≤ max (max N₁ N₂) Ns := le_max_left _ _
    have h3 : max (max N₁ N₂) Ns ≤ max (max (max N₁ N₂) Ns) 1 := le_max_left _ _
    linarith
  have hN₂N : N₂ < N := by
    rw [hNdef]
    have h1 : N₂ ≤ max N₁ N₂ := le_max_right _ _
    have h2 : max N₁ N₂ ≤ max (max N₁ N₂) Ns := le_max_left _ _
    have h3 : max (max N₁ N₂) Ns ≤ max (max (max N₁ N₂) Ns) 1 := le_max_left _ _
    linarith
  have hNsN : Ns < N := by
    rw [hNdef]
    have h2 : Ns ≤ max (max N₁ N₂) Ns := le_max_right _ _
    have h3 : max (max N₁ N₂) Ns ≤ max (max (max N₁ N₂) Ns) 1 := le_max_left _ _
    linarith
  have h1N : (1 : ℝ) ≤ N := by
    rw [hNdef]
    have h3 : (1 : ℝ) ≤ max (max (max N₁ N₂) Ns) 1 := le_max_right _ _
    linarith
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one h1N
  have hrN : 1 / r < N := lt_trans hrN₁ hN₁N
  have hKnn : (0 : ℝ) ≤ 3 * B := by linarith
  refine ⟨N, 3 * B, hNpos, hrN, hKnn, ?_⟩
  intro w hw
  have hw1 : 1 ≤ w.re := le_trans h1N hw.le
  have hwpos : 0 < w.re := lt_of_lt_of_le zero_lt_one hw1
  -- the remainder is the sum of the defects along the orbit
  have hdiff : fatouCoordW f (1 - a) w - approxCoord (1 - a) w
      = ∑' k : ℕ, coordError f (1 - a) ((wMap f)^[k] w) := by
    simp only [fatouCoordW]
    ring
  rw [hdiff]
  -- summability of the norms at `w`
  have hsumw : Summable (fun k : ℕ => ‖coordError f (1 - a) ((wMap f)^[k] w)‖) :=
    hsumm w (lt_of_lt_of_le hNsN hw.le)
  -- the pointwise majorant
  have hpoint : ∀ k : ℕ,
      ‖coordError f (1 - a) ((wMap f)^[k] w)‖ ≤ B / (w.re + (k : ℝ) / 2) ^ 2 := by
    intro k
    have hgr := hgrowth w (lt_of_lt_of_le hN₂N hw.le) k
    have hk2 : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
    have hN₁lt : N₁ < ((wMap f)^[k] w).re := by linarith [hw.le, hk2]
    have hb1 := hcErr ((wMap f)^[k] w) hN₁lt
    have hge : w.re + (k : ℝ) / 2 ≤ ‖((wMap f)^[k] w)‖ :=
      le_trans hgr (Complex.re_le_norm _)
    have hpos : 0 < w.re + (k : ℝ) / 2 := by linarith
    exact le_trans hb1 (div_le_div_of_nonneg_left hBnn (pow_pos hpos 2) (pow_le_pow_left₀ hpos.le hge 2))
  obtain ⟨hmaj_summ, hmaj_le⟩ := summable_div_shift_sq hBnn hw1
  calc ‖∑' k : ℕ, coordError f (1 - a) ((wMap f)^[k] w)‖
      ≤ ∑' k : ℕ, ‖coordError f (1 - a) ((wMap f)^[k] w)‖ := norm_tsum_le_tsum_norm hsumw
    _ ≤ ∑' k : ℕ, B / (w.re + (k : ℝ) / 2) ^ 2 :=
        Summable.tsum_le_tsum hpoint hsumw hmaj_summ
    _ ≤ 3 * B / w.re := hmaj_le

end

end Work.FatouCoord.Exist

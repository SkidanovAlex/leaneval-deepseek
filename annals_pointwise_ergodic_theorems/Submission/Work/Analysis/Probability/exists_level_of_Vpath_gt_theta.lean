import Mathlib
import Submission.Work.Analysis.Probability.exists_level_of_Vpath_gt

/-!
# A dyadic level of polynomial oscillation carried by the `r`-variation

Given a path `x : ℕ → ℝ` whose pairwise oscillations are bounded by `t > 0`
(`∀ s s', |x s' - x s| ≤ t`) and with `t < VpathR x r` (so the `r`-variation of `x` exceeds `t`,
`r > 1`), there is a dyadic level `k` at which the number of `t / 2 ^ (k+1)`-oscillations is
strictly bigger than `((1 - 2 ^ (θ-r)) / 2^r) * 2 ^ (θk)`, for any `θ > 2` with `θ < r`.

This is the polynomial-growth refinement of `exists_level_of_Vpath_gt` (which is the case
`θ = 1`), and it is the same layer-cake ("dyadic decomposition of the variation") argument: if
`d ≤ t` is a single oscillation and `m` is its unique dyadic layer
(`t / 2 ^ (m+1) < d ≤ t / 2 ^ m`), then `d ^ r ≤ t ^ r * q ^ m` with `q = 2 ^ (-r)`.  Summing over
the path and comparing with `∑ k, q^k A_k`, where `A_k` counts the oscillations exceeding the level
`t / 2 ^ (k+1)`, gives the result.  The only change with respect to the `θ = 1` case is the ratio of
the comparison geometric series: a bound `A_k ≤ ((1 - 2 ^ (θ-r)) / 2^r) * 2 ^ (θk)` gives
`∑ k, 2 ^ (-rk) A_k ≤ ((1 - 2 ^ (θ-r)) / 2^r) * ∑ k, (2 ^ (θ-r))^k = 1 / 2^r < 1`, because
`θ < r` makes the ratio `2 ^ (θ-r)` lie in `(0,1)`.  Hence if every `A_k` were so bounded, then
`∑ d^r ≤ t^r * 2^{-r} < t^r`, contradicting `t^r < ∑ d^r`.
-/

open scoped ENNReal BigOperators Topology
open Finset Filter

namespace Work.Analysis.Probability

/-- The ratio `2 ^ (θ - r)` of the `θ`-comparison geometric series is `< 1` when `θ < r`. -/
lemma two_rpow_theta_sub_r_lt_one {r θ : ℝ} (h : θ < r) : (2:ℝ)^(θ-r) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

/-- `1 - 2 ^ (θ - r) > 0` when `θ < r`. -/
lemma one_sub_two_rpow_theta_sub_r_pos {r θ : ℝ} (h : θ < r) : 0 < 1 - (2:ℝ)^(θ-r) :=
  by linarith [two_rpow_theta_sub_r_lt_one h]

/-- `dyw r * 2 ^ θ = 2 ^ (θ - r)`, i.e. `2^{-r} · 2^θ = 2^{θ-r}`. -/
lemma dyw_mul_two_rpow (r θ : ℝ) : dyw r * (2:ℝ)^θ = (2:ℝ)^(θ-r) := by
  have h2 : (0:ℝ) < 2 := by norm_num
  rw [dyw, mul_comm, ← Real.rpow_add h2 θ (-r), sub_eq_add_neg]

/-- The weight identity of the `θ`-series: `2^{-rk} · 2^{θk} = (2^{θ-r})^k`. -/
lemma dyw_pow_mul_two_rpow (r θ : ℝ) (k : ℕ) :
    (dyw r)^k * (2:ℝ)^(θ*(k:ℝ)) = ((2:ℝ)^(θ-r))^k := by
  have h2 : (0:ℝ) ≤ 2 := by norm_num
  have h1 : (2:ℝ)^(θ*(k:ℝ)) = ((2:ℝ)^θ)^k := by
    rw [← Real.rpow_natCast ((2:ℝ)^θ) k, Real.rpow_mul h2]
  rw [h1, ← mul_pow, dyw_mul_two_rpow]

/-- The comparison series bound, `θ`-version: if `A k ≤ ((1 - 2^(θ-r)) / 2^r) · 2^(θk)`, then
`∑ k, 2^{-rk} A_k ≤ 1 / 2^r`. -/
lemma tsum_weight_le_theta {r θ : ℝ} (hθr : θ < r) (An : ℕ → ℝ) (hAn0 : ∀ k, 0 ≤ An k)
    (hAn : ∀ k, An k ≤ ((1 - (2:ℝ)^(θ-r)) / 2^r) * (2:ℝ)^(θ*(k:ℝ))) :
    ∑' k : ℕ, (dyw r)^k * An k ≤ 1 / 2^r := by
  have hz0 : 0 ≤ (2:ℝ)^(θ-r) := by positivity
  have hz1 : (2:ℝ)^(θ-r) < 1 := two_rpow_theta_sub_r_lt_one hθr
  have hzpos : 0 < 1 - (2:ℝ)^(θ-r) := one_sub_two_rpow_theta_sub_r_pos hθr
  have hstep : ∀ k, (dyw r)^k * An k
      ≤ ((1 - (2:ℝ)^(θ-r)) / 2^r) * ((2:ℝ)^(θ-r))^k := by
    intro k
    calc (dyw r)^k * An k
        ≤ (dyw r)^k * (((1 - (2:ℝ)^(θ-r)) / 2^r) * (2:ℝ)^(θ*(k:ℝ))) :=
          mul_le_mul_of_nonneg_left (hAn k) (pow_nonneg (dyw_pos r).le k)
      _ = ((1 - (2:ℝ)^(θ-r)) / 2^r) * ((dyw r)^k * (2:ℝ)^(θ*(k:ℝ))) := by ring
      _ = ((1 - (2:ℝ)^(θ-r)) / 2^r) * ((2:ℝ)^(θ-r))^k := by rw [dyw_pow_mul_two_rpow]
  have hsumm1 : Summable fun k => ((1 - (2:ℝ)^(θ-r)) / 2^r) * ((2:ℝ)^(θ-r))^k :=
    Summable.mul_left _ (summable_geometric_of_lt_one hz0 hz1)
  have hsumm2 : Summable fun k => (dyw r)^k * An k :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg (dyw_pos r).le k) (hAn0 k)) hstep hsumm1
  calc ∑' k : ℕ, (dyw r)^k * An k
      ≤ ∑' k : ℕ, ((1 - (2:ℝ)^(θ-r)) / 2^r) * ((2:ℝ)^(θ-r))^k :=
        Summable.tsum_le_tsum hstep hsumm2 hsumm1
    _ = ((1 - (2:ℝ)^(θ-r)) / 2^r) * ∑' k : ℕ, ((2:ℝ)^(θ-r))^k := tsum_mul_left
    _ = ((1 - (2:ℝ)^(θ-r)) / 2^r) * (1 - (2:ℝ)^(θ-r))⁻¹ := by rw [tsum_geometric_of_lt_one hz0 hz1]
    _ = 1 / 2^r := by
        rw [div_mul_eq_mul_div, mul_inv_cancel₀ (ne_of_gt hzpos), one_div]

theorem exists_level_of_Vpath_gt_theta (x : ℕ → ℝ) {r t θ : ℝ} (hθ1 : 1 < r) (ht : 0 < t)
    (hθ2 : 2 < θ) (hθr : θ < r)
    (hrange : ∀ s s', |x s' - x s| ≤ t) (hV : ENNReal.ofReal t < Work.Analysis.Probability.VpathR x r) :
    ∃ k : ℕ, ENNReal.ofReal (((1 - (2:ℝ)^(θ-r)) / 2^r) * 2^(θ*k))
      < Work.Analysis.Probability.Kpath x (t / 2^(k+1)) := by
  classical
  rw [VpathR] at hV
  obtain ⟨u, hu⟩ := exists_lt_iSup hV
  obtain ⟨J, hJ⟩ := exists_lt_iSup hu
  set d : ℕ → ℝ := fun j => |x (u.1 (j+1)) - x (u.1 j)| with hd
  have hd0 : ∀ j, 0 ≤ d j := fun j => abs_nonneg _
  have hdt : ∀ j, d j ≤ t := fun j => hrange _ _
  have hS0 : 0 ≤ ∑ j ∈ Finset.range J, d j ^ r :=
    Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (hd0 j) r)
  have hJ' : t < (∑ j ∈ Finset.range J, d j ^ r) ^ (1/r) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.le).mp hJ
  have hS1 : 0 < (∑ j ∈ Finset.range J, d j ^ r) ^ (1/r) := lt_of_lt_of_le ht hJ'.le
  have htr : t ^ r < ∑ j ∈ Finset.range J, d j ^ r := by
    have h := (Real.rpow_lt_rpow_iff ht.le hS1.le (by linarith : (0:ℝ) < r)).mpr hJ'
    rwa [← Real.rpow_mul hS0 (1/r) r, div_mul_cancel₀ (1:ℝ) (by linarith : (0:ℝ) < r).ne', Real.rpow_one] at h
  by_contra hcon
  push Not at hcon
  set An : ℕ → ℝ := fun k => ((Finset.filter (fun j => t / 2^(k+1) < d j) (Finset.range J)).card : ℝ)
    with hAn
  have hKpath : ∀ k, ENNReal.ofReal (An k) ≤ Kpath x (t / 2^(k+1)) := by
    intro k
    rw [hAn, ENNReal.ofReal_natCast, Kpath]
    exact le_iSup_of_le u (le_iSup_of_le J le_rfl)
  have hcpos : ∀ k, 0 < ((1 - (2:ℝ)^(θ-r)) / 2^r) * 2^(θ*k) := by
    intro k
    exact mul_pos (div_pos (one_sub_two_rpow_theta_sub_r_pos hθr) (by positivity)) (by positivity)
  have hAn_le : ∀ k, An k ≤ ((1 - (2:ℝ)^(θ-r)) / 2^r) * 2^(θ*k) := by
    intro k
    exact (ENNReal.ofReal_le_ofReal_iff (hcpos k).le).mp (le_trans (hKpath k) (hcon k))
  have hAn0 : ∀ k, 0 ≤ An k := fun k => Nat.cast_nonneg _
  have hmain : ∑ j ∈ Finset.range J, d j ^ r ≤ t ^ r * ∑' k : ℕ, (dyw r)^k * An k := by
    simpa only [hAn] using sum_le_tsum_agg hθ1 ht J d hd0 hdt
  have hbound : ∑' k : ℕ, (dyw r)^k * An k ≤ 1 / 2^r := tsum_weight_le_theta hθr An hAn0 hAn_le
  have hL1 : ∑' k : ℕ, (dyw r)^k * An k < 1 := by
    refine lt_of_le_of_lt hbound ?_
    rw [one_div_two_rpow]
    exact dyw_lt_one (by linarith : (0:ℝ) < r)
  have hfin : ∑ j ∈ Finset.range J, d j ^ r < t ^ r :=
    lt_of_le_of_lt hmain (by
      have h := mul_lt_mul_of_pos_left hL1 (Real.rpow_pos_of_pos ht r)
      rwa [mul_one] at h)
  linarith [htr, hfin]

end Work.Analysis.Probability

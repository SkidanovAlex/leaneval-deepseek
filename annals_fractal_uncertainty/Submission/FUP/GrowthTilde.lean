import Submission.FUP.Step8
import Submission.Commons.MeasureTheory.Integral.integrable_tsum_of_nonneg
import Submission.FUP.GrowthSum
import Submission.Commons.MeasureTheory.Integral.integral_Ioi_inv_sq
import Submission.Commons.Measure.Real.intervalIntegral_abs_le_sq_mul_integral_inv_sq
import Submission.Commons.Measure.Real.integral_Ioi_indicator_one_add_sq_inv_le
import Submission.Commons.Measure.Real.setIntegral_Ioc_mul_inv_one_add_sq_le
import Submission.Commons.Measure.Real.integral_Ioc_indicator_mul_inv_one_add_sq_le

open MeasureTheory Metric Filter Set
open scoped Real BigOperators Topology ContDiff

set_option autoImplicit false
set_option maxHeartbeats 3200000
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

namespace Submission.FUP

/-!
# The growth condition of the modified weight

The last missing ingredient of §4 is that the modified weight `ω̃ = ∑_k ω̃_k` (and each of its
truncations `T_n = ∑_{k<n} ω̃_k`) satisfies the Beurling–Malliavin growth condition

  `∫_0^∞ G*(r)/(1+r²) dr < ∞`,   `G*(r) = sup_{‖x‖=r} ∫_{1/2}^2 |ω(sx)| ds`.

Since `π ω̃_k ≡ q_k` is constant on the sphere, the size of `ω̃_k` at scale `2^k` is `≍ |q_k|`, and
we prove the pointwise bounds (for `k ≥ 2`)

  `∫_{1/2}^2 |ω̃_k(t x)| dt ≤ 4 ‖x‖ |q_k| · 1_{2^{k-2} < ‖x‖ < 2^{k+2}}`

(the indicator is what makes the sum over `k` converge after integration against `1/(1+r²)`), and
`∫_{1/2}^2 |ω̃_1(tx)| dt ≤ 4 C_reg C_p(d)` for the first piece.  Summing,

  `G*(r) ≤ 4 C_reg C_p(d) 1_{r > 1/2} + 4 r^{-1} 1_{r > 1} ∑_k |q_k|`,

whose integral against `1/(1+r²)` is at most `8 C_reg C_p(d) + 2 ∑_k |q_k| ≤ 8 C_reg C_p(d) + 2^8 C_gr`.
-/

/-! ## The segment integral of a single piece -/

/-- **The segment integral of a modified piece.**  For `k ≥ 2`, the integral of `|ω̃_k|` over the
segment `{t • x : t ∈ [1/2,2]}` is bounded by `4‖x‖|q_k|` when `‖x‖` lies in the dyadic window of
`k`, and vanishes otherwise. -/
theorem intervalIntegral_abs_omegaTildePiece_le_window (hd : 1 ≤ d) (k : ℕ) (hk2 : 2 ≤ k)
    {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w) (hwk : ∀ x : ℝᵈ, omegaTildePiece (d := d) k w x ≤ 0)
    (x : ℝᵈ) :
    (∫ t in (1 / 2 : ℝ)..2, |omegaTildePiece (d := d) k w (t • x)|)
      ≤ 4 * ‖x‖ * |qk k w|
        * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) ‖x‖ := by
  have hk1 : 1 ≤ k := by omega
  by_cases hwin : ‖x‖ ∈ Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))
  · rw [Set.indicator_of_mem hwin]
    have hr : 0 < ‖x‖ := lt_trans (by positivity : (0 : ℝ) < (2 : ℝ) ^ (k - 2)) hwin.1
    set u : ℝᵈ := (‖x‖)⁻¹ • x with hu
    have hu1 : ‖u‖ = 1 := by
      rw [hu, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
        inv_mul_cancel₀ (ne_of_gt hr)]
    have hxr : ‖x‖ • u = x := by
      rw [hu, smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
    have hsub : (∫ t in (1 / 2 : ℝ)..2, |omegaTildePiece (d := d) k w (t • x)|)
        = (‖x‖)⁻¹ * ∫ s in (2 : ℝ)⁻¹ * ‖x‖..2 * ‖x‖,
            |omegaTildePiece (d := d) k w (s • u)| := by
      have h := intervalIntegral.integral_comp_mul_right
        (fun s : ℝ => |omegaTildePiece (d := d) k w (s • u)|) (a := (1 / 2 : ℝ)) (b := 2)
        (c := ‖x‖) (ne_of_gt hr)
      rw [smul_eq_mul] at h
      have hlhs : (fun t : ℝ => |omegaTildePiece (d := d) k w (t • x)|)
          = fun t : ℝ => |omegaTildePiece (d := d) k w ((t * ‖x‖) • u)| := by
        funext t
        have h1 : (t * ‖x‖) • u = t • x := by
          rw [mul_smul, hxr]
        rw [h1]
      rw [hlhs, h]
      norm_num
    rw [hsub]
    have hseg : (∫ s in (2 : ℝ)⁻¹ * ‖x‖..2 * ‖x‖, |omegaTildePiece (d := d) k w (s • u)|)
        ≤ 4 * ‖x‖ ^ 2 * |qk k w| := by
      have hc : 0 < (2 : ℝ)⁻¹ * ‖x‖ := by positivity
      have hcd : (2 : ℝ)⁻¹ * ‖x‖ ≤ 2 * ‖x‖ := by linarith [norm_nonneg x]
      have hcont : Continuous (fun s : ℝ => omegaTildePiece (d := d) k w (s • u)) :=
        (contDiff_omegaTildePiece k hw hk1).continuous.comp (by fun_prop)
      have hcs : HasCompactSupport (fun s : ℝ => omegaTildePiece (d := d) k w (s • u)) :=
        hasCompactSupport_omegaTildePiece_ray k w u hu1
      have hz : ∀ s : ℝ, |s| ≤ 1 → omegaTildePiece (d := d) k w (s • u) = 0 := fun s hs =>
        omegaTildePiece_ray_eq_zero_small k hk2 w u hu1 hs
      have h := Commons.Measure.Real.intervalIntegral_abs_le_sq_mul_integral_inv_sq hcont hcs hz hc hcd
      have hq : (∫ s in Set.Ioi (0 : ℝ),
          |omegaTildePiece (d := d) k w (s • u)| * (s ^ 2)⁻¹) = |qk k w| := by
        rw [← setIntegral_Ioi_abs_omegaTildePiece_div_sq k hk2 hw hwk u hu1]
        refine setIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
        rw [div_eq_mul_inv]
      rw [hq] at h
      calc (∫ s in (2 : ℝ)⁻¹ * ‖x‖..2 * ‖x‖, |omegaTildePiece (d := d) k w (s • u)|)
          ≤ (2 * ‖x‖) ^ 2 * |qk k w| := h
        _ = 4 * ‖x‖ ^ 2 * |qk k w| := by ring
    refine le_trans (mul_le_mul_of_nonneg_left hseg (by positivity)) ?_
    have hq : 0 ≤ |qk k w| := abs_nonneg _
    rw [inv_mul_le_iff₀ hr]
    nlinarith
  · rw [Set.indicator_of_notMem hwin]
    have hzero : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 2,
        |omegaTildePiece (d := d) k w (t • x)| = 0 := by
      intro t ht
      rw [abs_eq_zero]
      rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hwin
      rcases hwin with h | h
      · refine omegaTildePiece_eq_zero_of_norm_le_pred k hk1 w ?_
        have hnorm : ‖t • x‖ = t * ‖x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1]), mul_comm]
        rw [hnorm]
        have h2 : (2 : ℝ) * ‖x‖ ≤ 2 * (2 : ℝ) ^ (k - 2) := by linarith
        nlinarith [ht.2, norm_nonneg x, h2,
          show (2:ℝ) ^ (k - 1) = 2 * (2:ℝ) ^ (k - 2) from by
            rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]; ring]
      · refine omegaTildePiece_eq_zero_of_norm_ge k w ?_
        have hnorm : ‖t • x‖ = t * ‖x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1]), mul_comm]
        rw [hnorm]
        have h1 : (2 : ℝ) ^ (k + 2) = 2 * (2 : ℝ) ^ (k + 1) := by
          rw [pow2_add k 2, pow2_add k 1]; ring
        nlinarith [ht.1, h, pow_pos (by norm_num : (0:ℝ) < 2) (k+1)]
    have hEqOn : EqOn (fun t : ℝ => |omegaTildePiece (d := d) k w (t • x)|) (fun _ => (0:ℝ))
        (uIcc (1 / 2 : ℝ) 2) := by
      intro t ht
      rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at ht
      exact hzero t ht
    rw [intervalIntegral.integral_congr hEqOn, intervalIntegral.integral_zero, mul_zero]

/-- **The `k = 1` piece.**  Its segment integral is bounded by `4 C_reg C_p(d)` for `‖x‖ > 1/2`
and vanishes for `‖x‖ ≤ 1/2` (where `ω̃_1` is supported away from the segment). -/
theorem intervalIntegral_abs_omegaTildePiece_one_le (hd : 1 ≤ d) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0) {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (x : ℝᵈ) :
    (∫ t in (1 / 2 : ℝ)..2, |omegaTildePiece (d := d) 1 w (t • x)|)
      ≤ 4 * (Creg * pieceConst d) * (Set.Ioi (1 / 2 : ℝ)).indicator (fun _ => (1 : ℝ)) ‖x‖ := by
  by_cases hx : ‖x‖ ∈ Set.Ioi (1 / 2 : ℝ)
  · rw [Set.indicator_of_mem hx]
    have hle : ∀ t : ℝ, |omegaTildePiece (d := d) 1 w (t • x)| ≤ 2 * (Creg * pieceConst d) := by
      intro t
      have h := omegaPiece_iteratedFDeriv_le 1 0 (by norm_num) hCreg hw hwzero hwbound (t • x)
      rw [show omegaTildePiece (d := d) 1 w = omegaPiece 1 w from
        funext fun z => omegaTildePiece_of_lt 1 w (by norm_num) z]
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
      refine le_trans h (le_of_eq ?_)
      rw [show (((1 : ℕ) : ℝ) * (1 - ((0 : ℕ) : ℝ))) = 1 by norm_num, Real.rpow_one]
      ring
    have hcont : Continuous (fun t : ℝ => |omegaTildePiece (d := d) 1 w (t • x)|) :=
      ((contDiff_omegaTildePiece 1 hw le_rfl).continuous.comp
        (continuous_id.smul continuous_const)).abs
    have hInt := intervalIntegral.integral_mono (f := fun t : ℝ =>
        |omegaTildePiece (d := d) 1 w (t • x)|) (g := fun _ : ℝ => 2 * (Creg * pieceConst d))
      (a := (1 / 2 : ℝ)) (b := 2) (by norm_num) (hcont.intervalIntegrable _ _)
      (show IntervalIntegrable (fun _ : ℝ => 2 * (Creg * pieceConst d)) volume (1 / 2) 2 from
        intervalIntegrable_const) hle
    refine le_trans hInt ?_
    rw [intervalIntegral.integral_const, smul_eq_mul]
    have hCT : 0 < Creg * pieceConst d := mul_pos hCreg (pieceConst_pos d)
    have h3 : (2 - 1 / 2 : ℝ) * (2 * (Creg * pieceConst d)) = 3 * (Creg * pieceConst d) := by ring
    rw [h3]
    nlinarith [hCT]
  · rw [Set.indicator_of_notMem hx]
    have hzero : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 2,
        |omegaTildePiece (d := d) 1 w (t • x)| = 0 := by
      intro t ht
      rw [abs_eq_zero]
      refine omegaTildePiece_eq_zero_of_norm_le_pred 1 le_rfl w ?_
      have hnorm : ‖t • x‖ = t * ‖x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1]), mul_comm]
      rw [hnorm]
      have hxle : ‖x‖ ≤ 1 / 2 := le_of_not_gt fun h => hx h
      have h2 : t * ‖x‖ ≤ 2 * (1 / 2) := by nlinarith [ht.1, ht.2, hxle, norm_nonneg x]
      have h3 : (2 : ℝ) ^ (1 - 1) = 1 := by norm_num
      linarith
    have hEqOn : EqOn (fun t : ℝ => |omegaTildePiece (d := d) 1 w (t • x)|) (fun _ => (0 : ℝ))
        (uIcc (1 / 2 : ℝ) 2) := by
      intro t ht
      rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at ht
      exact hzero t ht
    rw [intervalIntegral.integral_congr hEqOn, intervalIntegral.integral_zero, mul_zero]

/-- **The segment integral of the truncation.**  Summing the per-piece bounds. -/
theorem intervalIntegral_abs_truncSum_le (hd : 1 ≤ d) (N : ℕ) {w : ℝᵈ → ℝ}
    (hw : ContDiff ℝ 3 w) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0) {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0) (x : ℝᵈ) :
    (∫ t in (1 / 2 : ℝ)..2, |truncSum (d := d) N w (t • x)|)
      ≤ 4 * (Creg * pieceConst d) * (Set.Ioi (1 / 2 : ℝ)).indicator (fun _ => (1 : ℝ)) ‖x‖
        + ∑ k ∈ Finset.Icc 2 N, 4 * ‖x‖ * |qk k w|
            * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) ‖x‖ := by
  set g : ℕ → ℝ := fun k => ∫ t in (1 / 2 : ℝ)..2, |omegaTildePiece (d := d) k w (t • x)| with hg
  have hcont : ∀ k : ℕ, Continuous (fun t : ℝ => |omegaTildePiece (d := d) k w (t • x)|) := by
    intro k
    rcases Nat.eq_zero_or_pos k with h0 | h1
    · subst h0
      have hz : (fun t : ℝ => |omegaTildePiece (d := d) 0 w (t • x)|) = fun _ => (0 : ℝ) := by
        funext t
        rw [funext (omegaTildePiece_zero_eq_zero w hwzero), abs_zero]
      rw [hz]; exact continuous_const
    · exact ((contDiff_omegaTildePiece k hw h1).continuous.comp
        (continuous_id.smul continuous_const)).abs
  -- dominate the integral of the truncation by the sum of the integrals of the pieces
  have hpoint : ∀ t : ℝ, |truncSum (d := d) N w (t • x)|
      ≤ ∑ k ∈ Finset.range N, |omegaTildePiece (d := d) k w (t • x)| := by
    intro t
    rw [truncSum_apply]
    exact Finset.abs_sum_le_sum_abs _ _
  have hstep1 : (∫ t in (1 / 2 : ℝ)..2, |truncSum (d := d) N w (t • x)|)
      ≤ ∑ k ∈ Finset.range N, g k := by
    refine le_trans (intervalIntegral.integral_mono (f := fun t : ℝ =>
        |truncSum (d := d) N w (t • x)|)
      (g := fun t : ℝ => ∑ k ∈ Finset.range N, |omegaTildePiece (d := d) k w (t • x)|)
      (by norm_num)
      (show IntervalIntegrable (fun t : ℝ => |truncSum (d := d) N w (t • x)|) volume (1 / 2) 2 from
        (((truncSum_contDiff N hw).continuous.comp
          (continuous_id.smul continuous_const)).abs).intervalIntegrable _ _)
      (show IntervalIntegrable (fun t : ℝ => ∑ k ∈ Finset.range N,
          |omegaTildePiece (d := d) k w (t • x)|) volume (1 / 2) 2 from
        (continuous_finset_sum _ fun k _ => hcont k).intervalIntegrable _ _) hpoint) ?_
    rw [intervalIntegral.integral_finsetSum (μ := volume) (a := (1 / 2 : ℝ)) (b := 2)
      (fun k _ => (hcont k).intervalIntegrable _ _)]
  refine le_trans hstep1 ?_
  -- bound the terms
  have hcover : Finset.range N ⊆ ({0, 1} : Finset ℕ) ∪ Finset.Icc 2 N := by
    intro k hk
    rw [Finset.mem_range] at hk
    rcases lt_or_ge k 2 with h | h
    · interval_cases k <;> simp
    · exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨h, by omega⟩)
  have hdisj : Disjoint ({0, 1} : Finset ℕ) (Finset.Icc 2 N) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_Icc] at hb
    fin_cases ha <;> omega
  have hnonneg : ∀ k, 0 ≤ g k := fun k =>
    intervalIntegral.integral_nonneg (by norm_num) (fun u _ => abs_nonneg _)
  have hsum_le : (∑ k ∈ Finset.range N, g k)
      ≤ ∑ k ∈ ({0, 1} : Finset ℕ) ∪ Finset.Icc 2 N, g k :=
    Finset.sum_le_sum_of_subset_of_nonneg hcover (fun k _ _ => hnonneg k)
  rw [Finset.sum_union hdisj, Finset.sum_pair (by norm_num : (0:ℕ) ≠ 1)] at hsum_le
  refine le_trans hsum_le ?_
  -- the `k = 0` term vanishes and the `k = 1` term is bounded
  have hg0 : g 0 = 0 := by
    change (∫ t in (1 / 2 : ℝ)..2, |omegaTildePiece (d := d) 0 w (t • x)|) = 0
    have hz : (fun t : ℝ => |omegaTildePiece (d := d) 0 w (t • x)|) = fun _ => (0 : ℝ) := by
      funext t
      rw [funext (omegaTildePiece_zero_eq_zero w hwzero), abs_zero]
    rw [hz, intervalIntegral.integral_zero]
  have hg1 : g 1 ≤ 4 * (Creg * pieceConst d) * (Set.Ioi (1 / 2 : ℝ)).indicator (fun _ => (1 : ℝ)) ‖x‖ := by
    change (∫ t in (1 / 2 : ℝ)..2, |omegaTildePiece (d := d) 1 w (t • x)|)
      ≤ 4 * (Creg * pieceConst d) * (Set.Ioi (1 / 2 : ℝ)).indicator (fun _ => (1 : ℝ)) ‖x‖
    exact intervalIntegral_abs_omegaTildePiece_one_le hd hw hwzero hCreg hwbound x
  have htail : (∑ k ∈ Finset.Icc 2 N, g k) ≤ ∑ k ∈ Finset.Icc 2 N, 4 * ‖x‖ * |qk k w|
      * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) ‖x‖ := by
    refine Finset.sum_le_sum fun k hk => ?_
    change (∫ t in (1 / 2 : ℝ)..2, |omegaTildePiece (d := d) k w (t • x)|)
      ≤ 4 * ‖x‖ * |qk k w|
        * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) ‖x‖
    exact intervalIntegral_abs_omegaTildePiece_le_window hd k (Finset.mem_Icc.mp hk).1 hw (hwk k) x
  linarith

/-- **The growth function of the truncation.**  Taking the sup over the sphere of the segment
bound of `intervalIntegral_abs_truncSum_le`. -/
theorem Gstar_truncSum_le (hd : 1 ≤ d) (N : ℕ) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0) {Creg : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0)
    {r : ℝ} (hr : 0 < r) :
    Gstar (truncSum (d := d) N w) r
      ≤ 4 * (Creg * pieceConst d) * (Set.Ioi (1 / 2 : ℝ)).indicator (fun _ => (1 : ℝ)) r
        + ∑ k ∈ Finset.Icc 2 N, 4 * r * |qk k w|
            * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) r := by
  haveI : Nonempty {x : ℝᵈ // ‖x‖ = r} := nonempty_sphere (d := d) hr hd
  rw [Gstar]
  refine ciSup_le fun x => ?_
  have h := intervalIntegral_abs_truncSum_le hd N hw hwzero hCreg hwbound hwk (x : ℝᵈ)
  simpa [x.2] using h

/-- The first majorant term `A · 1_{r>1/2}/(1+r²)` of the growth estimate is integrable. -/
lemma integrable_indicator_Ioi_half_div (A : ℝ) :
    Integrable (fun r : ℝ => A * (Set.Ioi (1 / 2 : ℝ)).indicator (fun _ => (1 : ℝ)) r
      / (1 + r ^ 2)) := by
  have hpt : ∀ r : ℝ, A * (Set.Ioi (1 / 2 : ℝ)).indicator (fun _ => (1 : ℝ)) r
      / (1 + r ^ 2) = (Set.Ioi (1 / 2 : ℝ)).indicator (fun r : ℝ => A / (1 + r ^ 2)) r := by
    intro r
    by_cases hc : r ∈ Set.Ioi (1 / 2 : ℝ)
    · rw [Set.indicator_of_mem hc (fun _ => (1 : ℝ)), mul_one,
        Set.indicator_of_mem hc (fun r : ℝ => A / (1 + r ^ 2))]
    · rw [Set.indicator_of_notMem hc (fun _ => (1 : ℝ)), mul_zero, zero_div,
        Set.indicator_of_notMem hc (fun r : ℝ => A / (1 + r ^ 2))]
  have hmaj : Integrable ((Set.Ioi (1 / 2 : ℝ)).indicator (fun r : ℝ => A / (1 + r ^ 2))) := by
    refine (integrable_indicator_iff measurableSet_Ioi).mpr ?_
    have h : Integrable (fun r : ℝ => A / (1 + r ^ 2)) := by
      simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul A
    exact h.integrableOn
  exact hmaj.congr (Eventually.of_forall fun r => (hpt r).symm)

/-- Partial sums of `|q_k|` (from `k = 2`) are bounded by `128 C_gr`. -/
theorem sum_abs_qk_Icc_le (hd : 1 ≤ d) (N : ℕ) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwnonpos : ∀ x, w x ≤ 0) {Creg : ℝ} (hCreg : 0 < Creg)
    (hreg : ∀ x : ℝᵈ, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))
    {Cgr : ℝ} (hint : IntegrableOn (fun r => Gstar w r / (1 + r ^ 2)) (Set.Ioi 0))
    (hgrle : (∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) ≤ Cgr) :
    ∑ k ∈ Finset.Icc 2 N, |qk k w| ≤ 128 * Cgr := by
  have h1 := sum_abs_qk_le_growth (d := d) hd hw.continuous hwnonpos hCreg.le hreg hint
    (K := max N 1)
  have hsub : Finset.Icc 2 N ⊆ Finset.Icc 1 (max N 1) := by
    intro k hk
    obtain ⟨h2, hN⟩ := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => abs_nonneg (qk k w))
  linarith

/-- A reindexing lemma for sums over `Icc 2 (m+1)`. -/
lemma sum_range_shift_eq_sum_Icc (F : ℕ → ℝ) (m : ℕ) :
    ∑ j ∈ Finset.range m, F (j + 2) = ∑ k ∈ Finset.Icc 2 (m + 1), F k := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    rw [show Finset.Icc 2 (m + 1 + 1) = insert (m + 2) (Finset.Icc 2 (m + 1)) from by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega]
    rw [Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    ring

/-- The shifted series `∑_j |q_{j+2}|` is summable. -/
theorem summable_abs_qk_shift (hd : 1 ≤ d) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwnonpos : ∀ x, w x ≤ 0) {Creg : ℝ} (hCreg : 0 < Creg)
    (hreg : ∀ x : ℝᵈ, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))
    {Cgr : ℝ} (hint : IntegrableOn (fun r => Gstar w r / (1 + r ^ 2)) (Set.Ioi 0))
    (hgrle : (∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) ≤ Cgr) :
    Summable (fun j : ℕ => |qk (j + 2) w|) := by
  refine summable_of_sum_range_le (c := 128 * Cgr) (fun n => abs_nonneg _) fun n => ?_
  rw [sum_range_shift_eq_sum_Icc (fun k => |qk k w|) n]
  exact sum_abs_qk_Icc_le (d := d) hd (n + 1) hw hwnonpos hCreg hreg hint hgrle

/-- The shifted series `∑_j |q_{j+2}|` is at most `128 C_gr`. -/
theorem tsum_abs_qk_shift_le (hd : 1 ≤ d) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwnonpos : ∀ x, w x ≤ 0) {Creg : ℝ} (hCreg : 0 < Creg)
    (hreg : ∀ x : ℝᵈ, ‖w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 : ℝ) / 2))
    {Cgr : ℝ} (hint : IntegrableOn (fun r => Gstar w r / (1 + r ^ 2)) (Set.Ioi 0))
    (hgrle : (∫ r in Set.Ioi (0 : ℝ), Gstar w r / (1 + r ^ 2)) ≤ Cgr) :
    (∑' j : ℕ, |qk (j + 2) w|) ≤ 128 * Cgr := by
  have hS : ∀ n : ℕ, ∑ k ∈ Finset.range n, |qk (k + 2) w| ≤ 128 * Cgr := fun n => by
    rw [sum_range_shift_eq_sum_Icc (fun k => |qk k w|) n]
    exact sum_abs_qk_Icc_le (d := d) hd (n + 1) hw hwnonpos hCreg hreg hint hgrle
  have hsumm := summable_abs_qk_shift (d := d) hd hw hwnonpos hCreg hreg hint hgrle
  exact le_of_tendsto_of_tendsto' hsumm.hasSum.tendsto_sum_nat tendsto_const_nhds hS

/-- A dyadic power above a given real number. -/
lemma exists_two_pow_gt (a : ℝ) : ∃ m : ℕ, a < (2 : ℝ) ^ m :=
  ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually_gt_atTop a).exists

/-- On the segment of radius `r`, the modified weight agrees with a truncation. -/
lemma Gstar_omegaTildeSum_eq_truncSum (hd : 1 ≤ d) {w : ℝᵈ → ℝ} {r : ℝ} (hr : 0 < r)
    {m : ℕ} (hm : 2 * r < (2 : ℝ) ^ m) :
    Gstar (omegaTildeSum (d := d) w) r = Gstar (truncSum (d := d) (m + 1) w) r := by
  have hpt : ∀ x : {x : ℝᵈ // ‖x‖ = r},
      (∫ t in (1 / 2 : ℝ)..2, |omegaTildeSum (d := d) w (t • (x : ℝᵈ))|)
        = ∫ t in (1 / 2 : ℝ)..2, |truncSum (d := d) (m + 1) w (t • (x : ℝᵈ))| := by
    intro x
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht0 : (0 : ℝ) ≤ t := le_trans (by norm_num) ht.1
    have hnorm : ‖t • (x : ℝᵈ)‖ = t * r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0, x.2]
    have hlt : ‖t • (x : ℝᵈ)‖ < (2 : ℝ) ^ m := by
      rw [hnorm]
      have ht2 : t ≤ 2 := by
        have h := ht.2
        rwa [max_eq_right (by norm_num : (1 / 2 : ℝ) ≤ 2)] at h
      have hmul : t * r ≤ 2 * r := mul_le_mul_of_nonneg_right ht2 hr.le
      linarith
    rw [omegaTildeSum_eq_sum_range m w hlt, truncSum_apply]
  rw [Gstar, Gstar]
  congr 1
  funext x
  exact hpt x

/-- **The growth condition for the truncations.**  The growth functional of `T_N = ∑_{k<N} ω̃_k` is
bounded by `8 C_reg C_p(d) + 2^13 C_gr`, uniformly in `N`. -/
theorem hasFiniteGrowth_truncSum (hd : 1 ≤ d) (N : ℕ) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwnonpos : ∀ x, w x ≤ 0) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg Cgr : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (hgrowth : HasFiniteGrowth w Cgr)
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0) :
    HasFiniteGrowth (truncSum (d := d) N w)
      (8 * (Creg * pieceConst d) + 8192 * Cgr + 1) := by
  obtain ⟨hint, hgrle⟩ := hgrowth
  rw [growthFunctional_eq_Gstar] at hgrle
  have hreg : ∀ z : ℝᵈ, ‖w z‖ ≤ Creg * (1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    intro z
    have h := hwbound 0 (by norm_num) z
    simpa [norm_iteratedFDeriv_zero] using h
  set S : ℝ := ∑ k ∈ Finset.Icc 2 N, |qk k w| with hS
  have hSnn : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun k _ => abs_nonneg _
  have hSle : S ≤ 128 * Cgr := by
    rw [hS]
    have h1 := sum_abs_qk_le_growth (d := d) hd hw.continuous hwnonpos hCreg.le hreg hint
      (K := max N 1)
    have hsub : Finset.Icc 2 N ⊆ Finset.Icc 1 (max N 1) := by
      intro k hk
      obtain ⟨h2, hN⟩ := Finset.mem_Icc.mp hk
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => abs_nonneg (qk k w))
    linarith
  set A : ℝ := 4 * (Creg * pieceConst d) with hA
  have hAnn : 0 ≤ A := by rw [hA]; have := pieceConst_pos d; positivity
  -- the dominating function
  set K : ℝ → ℝ := fun r =>
      A * (Set.Ioi (1 / 2 : ℝ)).indicator (fun _ => (1 : ℝ)) r / (1 + r ^ 2)
      + ∑ k ∈ Finset.Icc 2 N, (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹)
          * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) r
    with hK
  -- ## Step 1: pointwise domination
  have hle : ∀ r ∈ Set.Ioi (0 : ℝ),
      Gstar (truncSum (d := d) N w) r / (1 + r ^ 2) ≤ K r := by
    intro r hr
    have hrpos : 0 < r := hr
    have hone : (0 : ℝ) < 1 + r ^ 2 := by positivity
    have hG := Gstar_truncSum_le (d := d) hd N hw hwzero hCreg hwbound hwk hr
    rw [← hA] at hG
    have hperk : ∀ k ∈ Finset.Icc 2 N,
        4 * r * |qk k w|
            * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) r
            / (1 + r ^ 2)
          ≤ (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹)
              * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) r := by
      intro k hk
      obtain ⟨hk2, hkN⟩ := Finset.mem_Icc.mp hk
      by_cases hc : r ∈ Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))
      · rw [Set.indicator_of_mem hc (fun _ => (1 : ℝ)), mul_one, mul_one]
        have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
        have hq : (0 : ℝ) ≤ |qk k w| := abs_nonneg _
        have hlow : (2 : ℝ) ^ (k - 2) < r := hc.1
        have h4 : (2 : ℝ) ^ k < 4 * r := by
          have h := mul_lt_mul_of_pos_right hlow (by norm_num : (0 : ℝ) < 4)
          rw [show (2 : ℝ) ^ (k - 2) * 4 = (2 : ℝ) ^ k by
            rw [show (2 : ℝ) ^ (k - 2) * 4 = (2 : ℝ) ^ (k - 2) * (2 : ℝ) ^ 2 by norm_num,
              ← pow_add]
            congr 1
            omega] at h
          linarith
        have h1 : 1 < 4 * ((2 : ℝ) ^ k)⁻¹ * r := by
          have h := mul_lt_mul_of_pos_left h4 (inv_pos.mpr h2k)
          rw [inv_mul_cancel₀ (ne_of_gt h2k)] at h
          linarith
        have hkey : 4 * r ≤ 16 * ((2 : ℝ) ^ k)⁻¹ * (1 + r ^ 2) := by
          have h2 : 4 * r < 16 * ((2 : ℝ) ^ k)⁻¹ * r ^ 2 := by
            have h3 : 4 * r < 4 * r * (4 * ((2 : ℝ) ^ k)⁻¹ * r) := by
              nlinarith [h1, hrpos]
            nlinarith [h3]
          have h5 : 16 * ((2 : ℝ) ^ k)⁻¹ * r ^ 2 ≤ 16 * ((2 : ℝ) ^ k)⁻¹ * (1 + r ^ 2) := by
            nlinarith [sq_nonneg r, inv_nonneg.mpr h2k.le]
          linarith
        rw [div_le_iff₀ hone]
        nlinarith [mul_le_mul_of_nonneg_right hkey hq]
      · rw [Set.indicator_of_notMem hc (fun _ => (1 : ℝ))]
        simp
    have hsum : (∑ k ∈ Finset.Icc 2 N, 4 * r * |qk k w|
          * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) r)
          / (1 + r ^ 2)
        ≤ ∑ k ∈ Finset.Icc 2 N, (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹)
            * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) r := by
      rw [Finset.sum_div]
      exact Finset.sum_le_sum hperk
    rw [hK]
    refine le_trans (div_le_div_of_nonneg_right hG hone.le) ?_
    rw [add_div]
    exact add_le_add le_rfl hsum
  -- ## Step 2: `K` is integrable
  have hwin_sub : ∀ k : ℕ, 2 ≤ k →
      Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2)) ⊆ Set.Ioi (0 : ℝ) := by
    intro k hk r hr
    exact lt_trans (by positivity : (0 : ℝ) < (2 : ℝ) ^ (k - 2)) hr.1
  have hf1_int : Integrable (fun r : ℝ => A * (Set.Ioi (1 / 2 : ℝ)).indicator (fun _ => (1 : ℝ)) r
      / (1 + r ^ 2)) := integrable_indicator_Ioi_half_div A
  have hfk_int : ∀ k : ℕ, Integrable (fun r : ℝ => (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹)
      * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) r) := by
    intro k
    rw [show (fun r : ℝ => (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹)
        * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) r)
        = (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator
            (fun _ => (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹)) from by
      funext r
      by_cases hc : r ∈ Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))
      · rw [Set.indicator_of_mem hc (fun _ => (1 : ℝ)), mul_one,
          Set.indicator_of_mem hc (fun _ => (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹ : ℝ))]
      · rw [Set.indicator_of_notMem hc (fun _ => (1 : ℝ)), mul_zero,
          Set.indicator_of_notMem hc (fun _ => (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹ : ℝ))]]
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const (C := 16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹) measure_Ioc_lt_top.ne
  have hf2_int : Integrable (fun r : ℝ => ∑ k ∈ Finset.Icc 2 N,
      (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹)
        * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) r) :=
    integrable_finset_sum _ fun k _ => hfk_int k
  have hK_int : Integrable K := by
    rw [hK]
    exact hf1_int.add hf2_int
  -- ## Step 3: the integral of `K`
  have hK_le : (∫ r in Set.Ioi (0 : ℝ), K r) ≤ 2 * A + 60 * S := by
    rw [hK, integral_add hf1_int.integrableOn hf2_int.integrableOn]
    have h1 : (∫ r in Set.Ioi (0 : ℝ),
        A * (Set.Ioi (1 / 2 : ℝ)).indicator (fun _ => (1 : ℝ)) r / (1 + r ^ 2)) ≤ 2 * A := by
      have h := Commons.Measure.Real.integral_Ioi_indicator_one_add_sq_inv_le
        (A := A) (c := (1 / 2 : ℝ)) hAnn (by norm_num)
      rw [show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num, mul_comm] at h
      exact h
    have hper : ∀ k ∈ Finset.Icc 2 N,
        (∫ r in Set.Ioi (0 : ℝ), (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹)
          * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) r)
          = 60 * |qk k w| := by
      intro k hk
      obtain ⟨hk2, _⟩ := Finset.mem_Icc.mp hk
      have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      rw [show (fun r : ℝ => (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹)
          * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) r)
          = (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator
              (fun _ => (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹ : ℝ)) from by
        funext r
        by_cases hc : r ∈ Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))
        · rw [Set.indicator_of_mem hc (fun _ => (1 : ℝ)), mul_one,
            Set.indicator_of_mem hc (fun _ => (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹ : ℝ))]
        · rw [Set.indicator_of_notMem hc (fun _ => (1 : ℝ)), mul_zero,
            Set.indicator_of_notMem hc (fun _ => (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹ : ℝ))]]
      rw [setIntegral_indicator measurableSet_Ioc,
        Set.inter_eq_right.mpr (hwin_sub k hk2), setIntegral_const, Measure.real,
        Real.volume_Ioc, ENNReal.toReal_ofReal (by
          have ha : (0 : ℝ) < (2 : ℝ) ^ (k - 2) := by positivity
          have hb : (2 : ℝ) ^ (k - 2) ≤ (2 : ℝ) ^ (k + 2) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          linarith), smul_eq_mul]
      have hb : (2 : ℝ) ^ (k + 2) = 4 * (2 : ℝ) ^ k := by
        rw [pow_add]; norm_num; ring
      have ha : (2 : ℝ) ^ (k - 2) = (2 : ℝ) ^ k * 4⁻¹ := by
        have h4 : (2 : ℝ) ^ (k - 2) * 4 = (2 : ℝ) ^ k := by
          rw [show (2 : ℝ) ^ (k - 2) * 4 = (2 : ℝ) ^ (k - 2) * (2 : ℝ) ^ 2 by norm_num,
            ← pow_add]
          congr 1
          omega
        rw [← h4]
        ring
      rw [hb, ha]
      rw [show (4 * (2 : ℝ) ^ k - (2 : ℝ) ^ k * 4⁻¹) * (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹)
          = 60 * |qk k w| by
        rw [show (4 * (2 : ℝ) ^ k - (2 : ℝ) ^ k * 4⁻¹)
            = 15 * 4⁻¹ * (2 : ℝ) ^ k by ring]
        rw [show (15 * 4⁻¹ * (2 : ℝ) ^ k) * (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹)
            = (15 * 4⁻¹ * 16) * (((2 : ℝ) ^ k) * ((2 : ℝ) ^ k)⁻¹) * |qk k w| by ring]
        rw [mul_inv_cancel₀ (ne_of_gt h2k), mul_one]
        norm_num]
    have h2 : (∫ r in Set.Ioi (0 : ℝ), ∑ k ∈ Finset.Icc 2 N,
        (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹)
          * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) r)
        ≤ 60 * S := by
      rw [show (∫ r in Set.Ioi (0 : ℝ), ∑ k ∈ Finset.Icc 2 N,
          (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹)
            * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) r)
          = ∑ k ∈ Finset.Icc 2 N, ∫ r in Set.Ioi (0 : ℝ),
              (16 * |qk k w| * ((2 : ℝ) ^ k)⁻¹)
                * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) r
          from integral_finset_sum (Finset.Icc 2 N) (fun k _ => (hfk_int k).integrableOn)]
      rw [hS, Finset.mul_sum]
      exact Finset.sum_le_sum fun k hk => le_of_eq (hper k hk)
    linarith
  -- ## Step 4: conclusion
  have hden : Continuous fun r : ℝ => (1 : ℝ) + r ^ 2 :=
    continuous_const.add (continuous_id.pow 2)
  have hmeas : AEStronglyMeasurable
      (fun r : ℝ => Gstar (truncSum (d := d) N w) r / (1 + r ^ 2))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (AEMeasurable.div
      (aestronglyMeasurable_Gstar (d := d) hd (truncSum_contDiff N hw).continuous).aemeasurable
      hden.measurable.aemeasurable).aestronglyMeasurable
  have hOn : IntegrableOn (fun r : ℝ => Gstar (truncSum (d := d) N w) r / (1 + r ^ 2))
      (Set.Ioi (0 : ℝ)) := by
    refine Integrable.mono' hK_int.integrableOn hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Gstar_nonneg _ r) (by positivity))]
    exact hle r hr
  refine ⟨hOn, ?_⟩
  rw [growthFunctional_eq_Gstar]
  refine le_trans (integral_mono_ae hOn hK_int.integrableOn ?_) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact hle r hr
  · linarith [hK_le, hSle, hA]

/-- **The modified weight is `C³`.**  The sum `∑_k ω̃_k` is locally finite: for each `x` there is
`n` with `‖x‖ < 2^n`, and on a neighbourhood of `x` only the pieces `k ≤ n` are nonzero. -/
theorem contDiff_omegaTildeSum (hd : 1 ≤ d) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w) :
    ContDiff ℝ 3 (omegaTildeSum (d := d) w) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨n, hn⟩ := exists_pow_gt_norm x
  have hmem : Metric.ball x ((2 : ℝ) ^ n - ‖x‖) ∈ 𝓝 x :=
    Metric.ball_mem_nhds x (sub_pos.mpr hn)
  have hev : omegaTildeSum (d := d) w =ᶠ[𝓝 x] truncSum (d := d) (n + 1) w := by
    filter_upwards [hmem] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have hy' : ‖y‖ < (2 : ℝ) ^ n := by
      have h1 : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
        calc ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
          _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      linarith [h1, hy]
    rw [omegaTildeSum_eq_sum_range n w hy', truncSum_apply]
  exact (truncSum_contDiff (n + 1) hw).contDiffAt.congr_of_eventuallyEq hev

/-- **The growth condition for the modified weight `ω̃ = ∑_k ω̃_k` itself.** -/
theorem hasFiniteGrowth_omegaTildeSum (hd : 1 ≤ d) {w : ℝᵈ → ℝ} (hw : ContDiff ℝ 3 w)
    (hwnonpos : ∀ x, w x ≤ 0) (hwzero : ∀ x, ‖x‖ ≤ 2 → w x = 0)
    {Creg Cgr : ℝ} (hCreg : 0 < Creg)
    (hwbound : ∀ b : ℕ, b ≤ 3 → ∀ x : ℝᵈ,
      ‖iteratedFDeriv ℝ b w x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (b : ℝ)) / 2))
    (hgrowth : HasFiniteGrowth w Cgr)
    (hwk : ∀ (k : ℕ) (x : ℝᵈ), omegaTildePiece (d := d) k w x ≤ 0) :
    HasFiniteGrowth (omegaTildeSum (d := d) w)
      (8 * (Creg * pieceConst d) + 8192 * Cgr + 1) := by
  obtain ⟨hint, hgrle⟩ := hgrowth
  rw [growthFunctional_eq_Gstar] at hgrle
  have hreg : ∀ z : ℝᵈ, ‖w z‖ ≤ Creg * (1 + ‖z‖ ^ 2) ^ ((1 : ℝ) / 2) := by
    intro z
    have h := hwbound 0 (by norm_num) z
    simpa [norm_iteratedFDeriv_zero] using h
  have hCgr : 0 ≤ Cgr := le_trans (integral_nonneg fun r => div_nonneg (Gstar_nonneg w r) (by positivity)) hgrle
  have hsumm_q := summable_abs_qk_shift (d := d) hd hw hwnonpos hCreg hreg hint hgrle
  have htsum_q := tsum_abs_qk_shift_le (d := d) hd hw hwnonpos hCreg hreg hint hgrle
  set A : ℝ := 4 * (Creg * pieceConst d) with hA
  have hAnn : 0 ≤ A := by rw [hA]; have := pieceConst_pos d; positivity
  set c : ℕ → ℝ := fun j => 16 * |qk (j + 2) w| * ((2 : ℝ) ^ (j + 2))⁻¹ with hc
  set Win : ℕ → Set ℝ := fun j => Set.Ioc ((2 : ℝ) ^ ((j + 2) - 2)) ((2 : ℝ) ^ ((j + 2) + 2)) with hWin
  have hWin_meas : ∀ j : ℕ, MeasurableSet (Win j) := by
    intro j
    rw [hWin]
    exact measurableSet_Ioc
  have hWin_sub : ∀ j : ℕ, Win j ⊆ Set.Ioi (0 : ℝ) := by
    intro j r hr
    exact lt_trans (by positivity : (0 : ℝ) < (2 : ℝ) ^ ((j + 2) - 2)) hr.1
  have hc_nn : ∀ j : ℕ, 0 ≤ c j := by
    intro j
    simp only [hc]
    positivity
  set KInf : ℝ → ℝ := fun r =>
      A * (Set.Ioi (1 / 2 : ℝ)).indicator (fun _ => (1 : ℝ)) r / (1 + r ^ 2)
      + ∑' j, c j * (Win j).indicator (fun _ => (1 : ℝ)) r with hKInf
  -- the pointwise domination
  have hle : ∀ r ∈ Set.Ioi (0 : ℝ), Gstar (omegaTildeSum (d := d) w) r / (1 + r ^ 2) ≤ KInf r := by
    intro r hr
    have hrpos : 0 < r := hr
    have hone : (0 : ℝ) < 1 + r ^ 2 := by positivity
    obtain ⟨m, hm⟩ := exists_two_pow_gt (2 * r)
    have hGeq := Gstar_omegaTildeSum_eq_truncSum (d := d) (w := w) hd hrpos hm
    have h1 := Gstar_truncSum_le (d := d) hd (m + 1) hw hwzero hCreg hwbound hwk hr
    rw [← hA] at h1
    have hsumm_G : Summable (fun j : ℕ => c j * (Win j).indicator (fun _ => (1 : ℝ)) r) := by
      refine Summable.of_norm_bounded (hsumm_q.mul_left 4) fun j => ?_
      have hjc : 0 ≤ c j := hc_nn j
      have hind : |(Win j).indicator (fun _ => (1 : ℝ)) r| ≤ 1 := by
        by_cases hc' : r ∈ Win j
        · rw [Set.indicator_of_mem hc' (fun _ => (1 : ℝ)), abs_one]
        · rw [Set.indicator_of_notMem hc' (fun _ => (1 : ℝ)), abs_zero]
          norm_num
      have hp : (4 : ℝ) ≤ (2 : ℝ) ^ (j + 2) := by
        calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          _ ≤ (2 : ℝ) ^ (j + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hkey : 16 * ((2 : ℝ) ^ (j + 2))⁻¹ ≤ 4 := by
        have h1 : ((2 : ℝ) ^ (j + 2))⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp
        nlinarith
      have hcle : c j ≤ 4 * |qk (j + 2) w| := by
        simp only [hc]
        rw [show (16 : ℝ) * |qk (j + 2) w| * ((2 : ℝ) ^ (j + 2))⁻¹
            = 16 * ((2 : ℝ) ^ (j + 2))⁻¹ * |qk (j + 2) w| by ring]
        exact mul_le_mul_of_nonneg_right hkey (abs_nonneg _)
      calc ‖c j * (Win j).indicator (fun _ => (1 : ℝ)) r‖
          = c j * |(Win j).indicator (fun _ => (1 : ℝ)) r| := by
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hjc]
        _ ≤ c j * 1 := mul_le_mul_of_nonneg_left hind hjc
        _ = c j := mul_one _
        _ ≤ 4 * |qk (j + 2) w| := hcle
    have hper : ∀ j : ℕ,
        4 * r * |qk (j + 2) w| * (Win j).indicator (fun _ => (1 : ℝ)) r / (1 + r ^ 2)
          ≤ c j * (Win j).indicator (fun _ => (1 : ℝ)) r := by
      intro j
      by_cases hc' : r ∈ Win j
      · rw [Set.indicator_of_mem hc' (fun _ => (1 : ℝ)), mul_one, mul_one]
        have hq : (0 : ℝ) ≤ |qk (j + 2) w| := abs_nonneg _
        have h2j : ((2 : ℝ) ^ ((j + 2) - 2)) < r := hc'.1
        have hidx : (2 : ℝ) ^ ((j + 2) - 2) = (2 : ℝ) ^ j := by
          rw [show (j + 2) - 2 = j by omega]
        have hlow : (2 : ℝ) ^ j < r := by rwa [hidx] at h2j
        have hpow : (2 : ℝ) ^ (j + 2) = 4 * (2 : ℝ) ^ j := by
          rw [pow_add]
          norm_num
          ring
        have hpow : (2 : ℝ) ^ (j + 2) = 4 * (2 : ℝ) ^ j := by
          rw [pow_add]
          norm_num
          ring
        have hkey : 4 * r * (1 + r ^ 2)⁻¹ ≤ 16 * ((2 : ℝ) ^ (j + 2))⁻¹ := by
          have h1 : 4 * r * (1 + r ^ 2)⁻¹ ≤ 4 * r * (r ^ 2)⁻¹ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact inv_anti₀ (by positivity) (by nlinarith [sq_nonneg r])
          have h2 : 4 * r * (r ^ 2)⁻¹ = 4 * r⁻¹ := by
            field_simp
          have h4 : (16 : ℝ) * ((2 : ℝ) ^ (j + 2))⁻¹ = 4 * ((2 : ℝ) ^ j)⁻¹ := by
            rw [hpow]
            field_simp
            ring
          calc 4 * r * (1 + r ^ 2)⁻¹ ≤ 4 * r * (r ^ 2)⁻¹ := h1
            _ = 4 * r⁻¹ := h2
            _ ≤ 4 * ((2 : ℝ) ^ j)⁻¹ :=
                mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ j) hlow.le)
                  (by norm_num)
            _ = 16 * ((2 : ℝ) ^ (j + 2))⁻¹ := h4.symm
        have hfin : 4 * r * |qk (j + 2) w| * (1 + r ^ 2)⁻¹ ≤ c j := by
          simp only [hc]
          rw [show (16 : ℝ) * |qk (j + 2) w| * ((2 : ℝ) ^ (j + 2))⁻¹
              = 16 * ((2 : ℝ) ^ (j + 2))⁻¹ * |qk (j + 2) w| by ring]
          calc 4 * r * |qk (j + 2) w| * (1 + r ^ 2)⁻¹
              = |qk (j + 2) w| * (4 * r * (1 + r ^ 2)⁻¹) := by ring
            _ ≤ |qk (j + 2) w| * (16 * ((2 : ℝ) ^ (j + 2))⁻¹) := mul_le_mul_of_nonneg_left hkey hq
            _ = 16 * ((2 : ℝ) ^ (j + 2))⁻¹ * |qk (j + 2) w| := by ring
        exact hfin
      · rw [Set.indicator_of_notMem hc' (fun _ => (1 : ℝ))]
        simp
    have h2 : (∑ k ∈ Finset.Icc 2 (m + 1), 4 * r * |qk k w|
          * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) r)
          / (1 + r ^ 2)
        ≤ ∑ j ∈ Finset.range m, c j * (Win j).indicator (fun _ => (1 : ℝ)) r := by
      rw [Finset.sum_div,
        ← sum_range_shift_eq_sum_Icc (fun k => 4 * r * |qk k w|
          * (Set.Ioc ((2 : ℝ) ^ (k - 2)) ((2 : ℝ) ^ (k + 2))).indicator (fun _ => (1 : ℝ)) r
          / (1 + r ^ 2)) m]
      exact Finset.sum_le_sum fun j _ => hper j
    have h3 : (∑ j ∈ Finset.range m, c j * (Win j).indicator (fun _ => (1 : ℝ)) r)
        ≤ ∑' j, c j * (Win j).indicator (fun _ => (1 : ℝ)) r :=
      Summable.sum_le_tsum _ (fun j _ => mul_nonneg (hc_nn j)
        (Set.indicator_nonneg (fun _ _ => zero_le_one) r)) hsumm_G
    rw [hKInf, hGeq]
    refine le_trans (div_le_div_of_nonneg_right h1 hone.le) ?_
    rw [add_div]
    exact add_le_add le_rfl (le_trans h2 h3)
  -- per-term integral of the majorant
  have hint_term : ∀ j : ℕ,
      (∫ r in Set.Ioi (0 : ℝ), c j * (Win j).indicator (fun _ => (1 : ℝ)) r)
        = 60 * |qk (j + 2) w| := by
    intro j
    rw [show (fun r : ℝ => c j * (Win j).indicator (fun _ => (1 : ℝ)) r)
        = (Win j).indicator (fun _ => c j) from by
      funext r
      by_cases hc' : r ∈ Win j
      · rw [Set.indicator_of_mem hc' (fun _ => (1 : ℝ)), mul_one,
          Set.indicator_of_mem hc' (fun _ => c j)]
      · rw [Set.indicator_of_notMem hc' (fun _ => (1 : ℝ)), mul_zero,
          Set.indicator_of_notMem hc' (fun _ => c j)]]
    rw [setIntegral_indicator (hWin_meas j), Set.inter_eq_right.mpr (hWin_sub j)]
    beta_reduce
    rw [setIntegral_const, Measure.real, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by
        have hb : (2 : ℝ) ^ ((j + 2) - 2) ≤ (2 : ℝ) ^ ((j + 2) + 2) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        linarith), smul_eq_mul]
    rw [show (j + 2) + 2 = j + 4 by omega, show (j + 2) - 2 = j by omega]
    simp only [hc]
    rw [show (2 : ℝ) ^ (j + 4) = 16 * (2 : ℝ) ^ j by
      rw [pow_add]
      norm_num
      ring]
    rw [show (16 * (2 : ℝ) ^ j - (2 : ℝ) ^ j)
          * (16 * |qk (j + 2) w| * ((2 : ℝ) ^ (j + 2))⁻¹) = 60 * |qk (j + 2) w| by
      rw [show 16 * (2 : ℝ) ^ j - (2 : ℝ) ^ j = 15 * (2 : ℝ) ^ j by ring]
      rw [show 15 * (2 : ℝ) ^ j * (16 * |qk (j + 2) w| * ((2 : ℝ) ^ (j + 2))⁻¹)
          = (15 * 16) * ((2 : ℝ) ^ j * ((2 : ℝ) ^ (j + 2))⁻¹) * |qk (j + 2) w| by ring]
      rw [show (2 : ℝ) ^ j * ((2 : ℝ) ^ (j + 2))⁻¹ = 4⁻¹ by
        rw [show (2 : ℝ) ^ (j + 2) = 4 * (2 : ℝ) ^ j by
          rw [pow_add]
          norm_num
          ring, mul_inv_rev]
        field_simp]
      norm_num]
  have hfj_eq : ∀ j : ℕ, (fun r : ℝ => c j * (Win j).indicator (fun _ => (1 : ℝ)) r)
      = (Win j).indicator (fun _ => c j) := by
    intro j
    funext r
    by_cases hc' : r ∈ Win j
    · rw [Set.indicator_of_mem hc' (fun _ => (1 : ℝ)), mul_one,
        Set.indicator_of_mem hc' (fun _ => c j)]
    · rw [Set.indicator_of_notMem hc' (fun _ => (1 : ℝ)), mul_zero,
        Set.indicator_of_notMem hc' (fun _ => c j)]
  have hfj_int : ∀ j : ℕ,
      Integrable (fun r : ℝ => c j * (Win j).indicator (fun _ => (1 : ℝ)) r) volume := by
    intro j
    rw [hfj_eq j]
    refine (integrable_indicator_iff (hWin_meas j)).mpr ?_
    exact integrableOn_const (C := c j) measure_Ioc_lt_top.ne
  have hsumm60 : Summable (fun j : ℕ => ∫ r in Set.Ioi (0 : ℝ),
      c j * (Win j).indicator (fun _ => (1 : ℝ)) r) :=
    (hsumm_q.mul_left 60).congr fun j => (hint_term j).symm
  have hlin : (∑' j, ∫⁻ r, ENNReal.ofReal (c j * (Win j).indicator (fun _ => (1 : ℝ)) r)
      ∂(volume.restrict (Set.Ioi 0))) ≠ ⊤ := by
    have h1 : ∀ j : ℕ, (∫⁻ r, ENNReal.ofReal (c j * (Win j).indicator (fun _ => (1 : ℝ)) r)
        ∂(volume.restrict (Set.Ioi 0)))
        = ENNReal.ofReal (∫ r in Set.Ioi (0 : ℝ),
            c j * (Win j).indicator (fun _ => (1 : ℝ)) r) := fun j =>
      (ofReal_integral_eq_lintegral_ofReal ((hfj_int j).integrableOn)
        (Eventually.of_forall fun r => mul_nonneg (hc_nn j)
          (Set.indicator_nonneg (fun _ _ => zero_le_one) r))).symm
    rw [tsum_congr h1]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => integral_nonneg fun r => mul_nonneg (hc_nn j)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) r)) hsumm60]
    exact ENNReal.ofReal_ne_top
  obtain ⟨hK2_int, hK2_eq⟩ :=
    Commons.MeasureTheory.Integral.integrable_tsum_of_nonneg
      (μ := volume.restrict (Set.Ioi (0 : ℝ)))
      (f := fun j r => c j * (Win j).indicator (fun _ => (1 : ℝ)) r)
      (fun j => (measurable_const.mul (measurable_const.indicator (hWin_meas j))).aestronglyMeasurable)
      (fun j r => mul_nonneg (hc_nn j) (Set.indicator_nonneg (fun _ _ => zero_le_one) r))
      hlin
  have hK2_val : (∫ r in Set.Ioi (0 : ℝ), ∑' j, c j * (Win j).indicator (fun _ => (1 : ℝ)) r)
      ≤ 7680 * Cgr := by
    rw [hK2_eq, tsum_congr hint_term, tsum_mul_left]
    have h := mul_le_mul_of_nonneg_left htsum_q (by norm_num : (0 : ℝ) ≤ 60)
    linarith
  have hKInf_int : IntegrableOn KInf (Set.Ioi (0 : ℝ)) := by
    simp only [hKInf]
    exact ((integrable_indicator_Ioi_half_div A).integrableOn).add hK2_int
  have hKInf_val : (∫ r in Set.Ioi (0 : ℝ), KInf r) ≤ 2 * A + 7680 * Cgr := by
    rw [hKInf, integral_add (integrable_indicator_Ioi_half_div A).integrableOn hK2_int]
    have h1 : (∫ r in Set.Ioi (0 : ℝ),
        A * (Set.Ioi (1 / 2 : ℝ)).indicator (fun _ => (1 : ℝ)) r / (1 + r ^ 2)) ≤ 2 * A := by
      have h := Commons.Measure.Real.integral_Ioi_indicator_one_add_sq_inv_le
        (A := A) (c := (1 / 2 : ℝ)) hAnn (by norm_num)
      rw [show ((1 : ℝ) / 2)⁻¹ = 2 by norm_num, mul_comm] at h
      exact h
    linarith
  have hden : Continuous fun r : ℝ => (1 : ℝ) + r ^ 2 :=
    continuous_const.add (continuous_id.pow 2)
  have hmeas : AEStronglyMeasurable
      (fun r : ℝ => Gstar (omegaTildeSum (d := d) w) r / (1 + r ^ 2))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (AEMeasurable.div
      (aestronglyMeasurable_Gstar (d := d) hd (contDiff_omegaTildeSum (d := d) hd hw).continuous).aemeasurable
      hden.measurable.aemeasurable).aestronglyMeasurable
  have hOn : IntegrableOn (fun r : ℝ => Gstar (omegaTildeSum (d := d) w) r / (1 + r ^ 2))
      (Set.Ioi (0 : ℝ)) := by
    refine Integrable.mono' hKInf_int hmeas ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Gstar_nonneg _ r) (by positivity))]
    exact hle r hr
  refine ⟨hOn, ?_⟩
  rw [growthFunctional_eq_Gstar]
  refine le_trans (integral_mono_ae hOn hKInf_int ?_) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact hle r hr
  · linarith [hKInf_val, hA, hCgr]


end Submission.FUP




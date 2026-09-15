import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_strip_growth
import Submission.Commons.NumberTheory.Zeta.zeta_strip_smallIm_bound
import Submission.Commons.Analysis.ExpLog.log_le_two_sqrt

open Complex Filter Set
open scoped Real Topology BigOperators

noncomputable section

namespace Commons.NumberTheory.Zeta

/-- **Sharp `1/2`-power bound for `ζ(1+z+z')` on the classical zero-free curve.**  If `z, z'` lie
on/behind the left boundary `Γ₀ = {Re = -β/log(|Im|+2)}` of the shifted zero-free region and not
left of its extreme point `-β/log 2`, i.e. `-β/log 2 ≤ Re z ≤ -β/log(|z.im|+2)` (and likewise for
`z'`), then `Re(1+z+z') ∈ [1 - 2β/log 2, 1)` is bounded away from the pole and
`|1+z+z'-1| ≥ β/log(|z.im|+2) + β/log(|z'.im|+2) ≫ 1/log base`, so the pole term is `≪ √base/β`;
with the exponent-`2/5` strip bound far from the real axis
(`Commons.NumberTheory.Zeta.zeta_strip_growth`, `δ = 1/10`) and
`Commons.NumberTheory.Zeta.zeta_strip_smallIm_bound` near it one gets `‖ζ(1+z+z')‖ ≪ √base`.

This is the CORRECT form of Green–Tao's estimate (troublesome) in the proof of Lemma A.3/10.4
(`|ζ(1+z+z')| ≪ (1+|z|+|z'|)^{1/4}` for `z,z' ∈ Γ₀`): the hypothesis on `z.re` is an UPPER bound
(so that `(z+z').re ≤ -β/log(|z.im|+2) - β/log(|z'.im|+2) < 0` controls the pole at `1+z+z' = 1`).
Do NOT reverse it: the variant with `-β/log(|z.im|+2) ≤ z.re ≤ 0` is FALSE (take `z = z' = -ε`;
then `1+z+z' = 1-2ε`, where `‖ζ(1-2ε)‖ ≈ 1/(2ε) → ∞`, while `base = 3`). -/
theorem zeta_one_add_add_bound_curve_sqrt_left_curve {β : ℝ} (hβ : 0 < β) (hβ10 : β ≤ 1 / 10) :
    ∃ C : ℝ, 0 < C ∧ ∀ z z' : ℂ,
      -(β / Real.log 2) ≤ z.re → z.re ≤ -(β / Real.log (|z.im| + 2)) →
      -(β / Real.log 2) ≤ z'.re → z'.re ≤ -(β / Real.log (|z'.im| + 2)) →
      ‖riemannZeta (1 + z + z')‖ ≤ C * (|z.im| + |z'.im| + 3) ^ ((1:ℝ) / 2) := by
  obtain ⟨C1, hC1pos, hC1⟩ := zeta_strip_growth
  obtain ⟨C2, hC2pos, hC2⟩ := zeta_strip_smallIm_bound
  refine ⟨11 * (C1 + C2) * (1 + 4 / β) + ‖riemannZeta 1‖ + 1, by positivity, ?_⟩
  intro z z' hzlo hzhi hzlo' hzhi'
  set base : ℝ := |z.im| + |z'.im| + 3 with hbasedef
  have hbase_ge_one : (1 : ℝ) ≤ base := by
    rw [hbasedef]
    have h1 := abs_nonneg z.im
    have h2 := abs_nonneg z'.im
    linarith
  have hbase_pos : (0 : ℝ) < base := lt_of_lt_of_le zero_lt_one hbase_ge_one
  have hbase_nonneg : (0 : ℝ) ≤ base := le_of_lt hbase_pos
  have hsqrt_eq : Real.sqrt base = base ^ ((1:ℝ) / 2) := Real.sqrt_eq_rpow base
  have hsqrt_ge_one : (1 : ℝ) ≤ Real.sqrt base := by
    rw [hsqrt_eq]
    exact Real.one_le_rpow hbase_ge_one (by norm_num)
  have hlog2_pos : (0:ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2_ge : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  set A : ℝ := Real.log (|z.im| + 2) with hAdef
  set B : ℝ := Real.log (|z'.im| + 2) with hBdef
  have hApos : 0 < A := by rw [hAdef]; exact Real.log_pos (by linarith [abs_nonneg z.im])
  have hBpos : 0 < B := by rw [hBdef]; exact Real.log_pos (by linarith [abs_nonneg z'.im])
  have hzA : z.re ≤ -(β / A) := by rw [hAdef]; exact hzhi
  have hzB : z'.re ≤ -(β / B) := by rw [hBdef]; exact hzhi'
  set s : ℂ := 1 + z + z' with hsdef
  have hre : s.re = 1 + z.re + z'.re := by simp [hsdef]
  have him : s.im = z.im + z'.im := by simp [hsdef]
  have hre_lt_one : s.re < 1 := by
    rw [hre]
    have h1 : z.re < 0 := by
      have : 0 < β / A := div_pos hβ hApos
      linarith
    have h2 : z'.re < 0 := by
      have : 0 < β / B := div_pos hβ hBpos
      linarith
    linarith
  have hre_ge : 1 - 2 * β / Real.log 2 ≤ s.re := by
    rw [hre]
    have hX : 1 + (-(β / Real.log 2) + -(β / Real.log 2)) ≤ 1 + z.re + z'.re := by
      linarith
    have e : 1 - 2 * β / Real.log 2 = 1 + (-(β / Real.log 2) + -(β / Real.log 2)) := by
      ring
    rw [e]
    exact hX
  have hre_six : (1:ℝ) / 2 + 1 / 10 ≤ s.re := by
    have hb : 2 * β / Real.log 2 ≤ 2 / 5 := by
      rw [div_le_iff₀ hlog2_pos]
      nlinarith [hlog2_ge, hβ10, hβ]
    linarith
  have hre_two : s.re ≤ 2 := by linarith
  have hsne : s ≠ 1 := by
    intro h
    have : s.re = 1 := by rw [h]; simp
    linarith
  have hsw : ((s.re : ℂ) + Complex.I * (s.im : ℂ)) = s := by
    rw [mul_comm]
    exact Complex.re_add_im s
  have hδ : (1:ℝ) + 1 / (1/10) = 11 := by norm_num
  have hexp : (1:ℝ) / 2 - (1/10) / 2 = 9/20 := by norm_num
  by_cases ht : 1 ≤ |s.im|
  · -- far from the real axis: exponent-`2/5` strip bound
    have hb := hC1 (1/10) s.re s.im (by norm_num) (by norm_num) hre_six hre_two ht
    rw [hsw, hδ, hexp] at hb
    have ht_base : |s.im| + 3 ≤ base := by
      rw [hbasedef, him]
      linarith [abs_add_le z.im z'.im]
    have hpow : (|s.im| + 3) ^ ((9:ℝ)/20) ≤ base ^ ((1:ℝ)/2) := by
      have h0 : (0:ℝ) ≤ |s.im| + 3 := by positivity
      calc (|s.im| + 3) ^ ((9:ℝ)/20) ≤ base ^ ((9:ℝ)/20) :=
            Real.rpow_le_rpow h0 ht_base (by norm_num)
        _ ≤ base ^ ((1:ℝ)/2) := Real.rpow_le_rpow_of_exponent_le hbase_ge_one (by norm_num)
    calc ‖riemannZeta s‖ ≤ C1 * 11 * (|s.im| + 3) ^ ((9:ℝ)/20) := hb
      _ ≤ C1 * 11 * base ^ ((1:ℝ)/2) := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ (11 * (C1 + C2) * (1 + 4 / β) + ‖riemannZeta 1‖ + 1) * base ^ ((1:ℝ)/2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hbase_nonneg _)
          have h4 : (1:ℝ) ≤ 1 + 4 / β := by
            have : (0:ℝ) < 4 / β := by positivity
            linarith
          have h5 : (0:ℝ) ≤ 11 * (C1 + C2) := by positivity
          have hle : 11 * C1 ≤ 11 * (C1 + C2) * (1 + 4 / β) := by
            calc 11 * C1 ≤ 11 * (C1 + C2) := by linarith
              _ = 11 * (C1 + C2) * 1 := by ring
              _ ≤ 11 * (C1 + C2) * (1 + 4 / β) := mul_le_mul_of_nonneg_left h4 h5
          have h6 : (0:ℝ) ≤ ‖riemannZeta 1‖ + 1 := by positivity
          linarith
  · -- near the real axis
    have ht1 : |s.im| < 1 := not_le.mp ht
    have ht2 : |s.im| ≤ 2 := by linarith
    have hb := hC2 (1/10) s.re s.im (by norm_num) (by norm_num) hre_six hre_two
      ht2 (by rw [hsw]; exact hsne)
    rw [hsw, hδ] at hb
    -- lower bound on ‖s - 1‖, hence control of the pole term
    have hsm1_re : (s - 1).re = z.re + z'.re := by
      rw [hsdef]; simp; ring
    have hgap : β / A + β / B ≤ -(s - 1).re := by
      rw [hsm1_re]
      have h1 : β / A ≤ -z.re := by linarith
      have h2 : β / B ≤ -z'.re := by linarith
      linarith
    have hgap_pos : 0 < β / A + β / B := by positivity
    have hnorm_ge : β / A + β / B ≤ ‖s - 1‖ := by
      have h1 : |(s - 1).re| ≤ ‖s - 1‖ := abs_re_le_norm (s - 1)
      have h2 : |(s - 1).re| = -(s - 1).re := by
        rw [abs_of_neg (by linarith [hgap, hgap_pos])]
      linarith
    have hinv : ‖s - 1‖⁻¹ ≤ (A + B) / β := by
      have h1 : ‖s - 1‖⁻¹ ≤ (β / A + β / B)⁻¹ :=
        (inv_le_inv₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hsne)) hgap_pos).mpr hnorm_ge
      have hDA : β / A ≤ β / A + β / B := by
        have : 0 < β / B := div_pos hβ hBpos
        linarith
      have h2 : (β / A + β / B)⁻¹ ≤ (β / A)⁻¹ :=
        (inv_le_inv₀ hgap_pos (div_pos hβ hApos)).mpr hDA
      have h3 : (β / A)⁻¹ = A / β := by rw [inv_div]
      have h4 : A / β ≤ (A + B) / β := by
        apply div_le_div_of_nonneg_right _ hβ.le
        linarith
      linarith
    -- `A` and `B` are `O(√base)` by `log x ≤ 2√x`
    have hAsqrt : A ≤ 2 * Real.sqrt base := by
      rw [hAdef]
      have h1 : Real.log (|z.im| + 2) ≤ 2 * Real.sqrt (|z.im| + 2) :=
        Commons.Analysis.ExpLog.log_le_two_sqrt (by positivity)
      have h2 : Real.sqrt (|z.im| + 2) ≤ Real.sqrt base := by
        apply Real.sqrt_le_sqrt
        rw [hbasedef]; linarith [abs_nonneg z'.im]
      linarith
    have hBsqrt : B ≤ 2 * Real.sqrt base := by
      rw [hBdef]
      have h1 : Real.log (|z'.im| + 2) ≤ 2 * Real.sqrt (|z'.im| + 2) :=
        Commons.Analysis.ExpLog.log_le_two_sqrt (by positivity)
      have h2 : Real.sqrt (|z'.im| + 2) ≤ Real.sqrt base := by
        apply Real.sqrt_le_sqrt
        rw [hbasedef]; linarith [abs_nonneg z.im]
      linarith
    have hAB : A + B ≤ 4 * Real.sqrt base := by linarith
    have hinv2 : 1 / ‖s - 1‖ ≤ 4 * Real.sqrt base / β := by
      have h1 : 1 / ‖s - 1‖ = ‖s - 1‖⁻¹ := one_div _
      have h2 : (A + B) / β ≤ 4 * Real.sqrt base / β :=
        div_le_div_of_nonneg_right hAB hβ.le
      rw [h1]; exact le_trans hinv h2
    have h12 : 1 + 1 / ‖s - 1‖ ≤ (1 + 4 / β) * Real.sqrt base := by
      have hstep : 1 + 1 / ‖s - 1‖ ≤ 1 + 4 * Real.sqrt base / β := by linarith [hinv2]
      have hstep2 : 1 + 4 * Real.sqrt base / β ≤ (1 + 4 / β) * Real.sqrt base := by
        have e1 : 4 * Real.sqrt base / β = (4 / β) * Real.sqrt base := by ring
        have e2 : (1 + 4 / β) * Real.sqrt base
            = Real.sqrt base + (4 / β) * Real.sqrt base := by ring
        rw [e1, e2]
        linarith [hsqrt_ge_one]
      exact le_trans hstep hstep2
    have hfinal : C2 * 11 * ((1 + 4 / β) * Real.sqrt base) ≤
        (11 * (C1 + C2) * (1 + 4 / β) + ‖riemannZeta 1‖ + 1) * Real.sqrt base := by
      have hX : (0:ℝ) ≤ Real.sqrt base := Real.sqrt_nonneg base
      have h4 : (0:ℝ) ≤ 1 + 4 / β := by positivity
      have hle : 11 * C2 * (1 + 4 / β) ≤ 11 * (C1 + C2) * (1 + 4 / β) := by
        apply mul_le_mul_of_nonneg_right _ h4
        linarith
      calc C2 * 11 * ((1 + 4 / β) * Real.sqrt base)
          = (11 * C2 * (1 + 4 / β)) * Real.sqrt base := by ring
        _ ≤ (11 * (C1 + C2) * (1 + 4 / β)) * Real.sqrt base :=
            mul_le_mul_of_nonneg_right hle hX
        _ ≤ (11 * (C1 + C2) * (1 + 4 / β) + ‖riemannZeta 1‖ + 1) * Real.sqrt base := by
            apply mul_le_mul_of_nonneg_right _ hX
            have h6 : (0:ℝ) ≤ ‖riemannZeta 1‖ + 1 := by positivity
            linarith
    calc ‖riemannZeta s‖ ≤ C2 * 11 * (1 + 1 / ‖s - 1‖) := hb
      _ ≤ C2 * 11 * ((1 + 4 / β) * Real.sqrt base) :=
          mul_le_mul_of_nonneg_left h12 (by positivity)
      _ ≤ (11 * (C1 + C2) * (1 + 4 / β) + ‖riemannZeta 1‖ + 1) * Real.sqrt base := hfinal
      _ = (11 * (C1 + C2) * (1 + 4 / β) + ‖riemannZeta 1‖ + 1) * base ^ ((1:ℝ)/2) := by
          rw [hsqrt_eq]

end Commons.NumberTheory.Zeta

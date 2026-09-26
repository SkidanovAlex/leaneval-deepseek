import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.E_jdiff_large
import Submission.Work.Asymptotics.ExpTwoPiLatticeLower

set_option maxHeartbeats 1000000

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

noncomputable section

/-! ## 1. `Δ` dominates `q` in the whole strip `Im ≥ 1`

This is `Work.Asymptotics.DeltaFun_funnel_lower_sharp` (valid for `Im τ ≥ 2`) with the
hypothesis relaxed to `Im τ ≥ 1`; the only numerical input of that proof is
`‖q τ‖ = e^{-2π Im τ} ≤ e^{-2π} ≤ 1/96`, which already holds for `Im τ ≥ 1`. -/

private theorem deltaFun_lower_im_one (τ : UpperHalfPlane) (hτ : 1 ≤ τ.im) :
    (1 / 2 : ℝ) * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖ := by
  have hq_lt : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos (by rw [UpperHalfPlane.coe_im]; exact τ.im_pos)
  have hmul : Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n (τ : ℂ)) :=
    ModularForm.multipliable_one_sub_pow hq_lt
  set r : ℝ := ‖Function.Periodic.qParam 1 (τ : ℂ)‖ with hrdef
  have hnormq : r = Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [hrdef, Function.Periodic.norm_qParam, UpperHalfPlane.coe_im]; congr 1; ring
  have hr0 : 0 ≤ r := by rw [hrdef]; exact norm_nonneg _
  have hr_le : r ≤ 1 / 96 := by
    rw [hnormq]
    have h96 : (96 : ℝ) ≤ Real.exp (2 * Real.pi) := by
      have h1 : (96 : ℝ) ≤ Real.exp 6 := by
        have h2 : (2.7182818283 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_d9
        have h3 : Real.exp 6 = (Real.exp 1) ^ 6 := by
          rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
        rw [h3]
        calc (96 : ℝ) ≤ (2.7182818283 : ℝ) ^ 6 := by norm_num
          _ ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) h2 6
      have h4 : Real.exp 6 ≤ Real.exp (2 * Real.pi) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
      linarith
    have hle : -(2 * Real.pi * τ.im) ≤ -(2 * Real.pi) := by nlinarith [Real.pi_pos, hτ]
    calc Real.exp (-(2 * Real.pi * τ.im)) ≤ Real.exp (-(2 * Real.pi)) := Real.exp_le_exp.mpr hle
      _ = 1 / Real.exp (2 * Real.pi) := by rw [Real.exp_neg, inv_eq_one_div]
      _ ≤ 1 / 96 := one_div_le_one_div_of_le (by norm_num) h96
  have hr1 : r < 1 := by linarith
  have hr_half : r ≤ 1 / 2 := by linarith
  have hprod : 1 - 2 * r ≤ ‖∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ))‖ := by
    have hlim := hmul.tendsto_prod_tprod_nat
    refine ge_of_tendsto hlim.norm ?_
    filter_upwards with N
    have hfac : ∀ n : ℕ, 1 - r ^ (n + 1) ≤ ‖(1 - ModularForm.eta_q n (τ : ℂ))‖ := by
      intro n
      have hnorm : ‖ModularForm.eta_q n (τ : ℂ)‖ = r ^ (n + 1) := by
        simp [ModularForm.eta_q, hrdef, norm_pow]
      have h := norm_add_le (1 - ModularForm.eta_q n (τ : ℂ)) (ModularForm.eta_q n (τ : ℂ))
      rw [sub_add_cancel, norm_one] at h
      rw [hnorm] at h
      linarith
    have hsumm : Summable (fun n : ℕ => r ^ (n + 1)) :=
      (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hr0 hr1)
    have hgeom : ∑ n ∈ Finset.range N, r ^ (n + 1) ≤ 2 * r := by
      have h1 : ∑ n ∈ Finset.range N, r ^ (n + 1) ≤ ∑' n : ℕ, r ^ (n + 1) :=
        hsumm.sum_le_tsum (Finset.range N) (fun i _ => pow_nonneg hr0 _)
      have htsum : ∑' n : ℕ, r ^ (n + 1) = r / (1 - r) := by
        have heq : (fun n : ℕ => r ^ (n + 1)) = fun n : ℕ => r * r ^ n := by
          funext n; rw [pow_succ]; ring
        rw [heq, tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
        ring
      have h2 : r / (1 - r) ≤ 2 * r := by
        rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - r)]
        nlinarith [hr0, hr_half]
      calc ∑ n ∈ Finset.range N, r ^ (n + 1) ≤ ∑' n : ℕ, r ^ (n + 1) := h1
        _ = r / (1 - r) := htsum
        _ ≤ 2 * r := h2
    have h2 : 1 - ∑ n ∈ Finset.range N, r ^ (n + 1) ≤ ∏ n ∈ Finset.range N, (1 - r ^ (n + 1)) :=
      one_sub_sum_le_prod_one_sub (Finset.range N) (fun n => r ^ (n + 1))
        (fun n _ => pow_nonneg hr0 _) (fun n _ => pow_le_one₀ hr0 (le_of_lt hr1))
    have h1 : ∏ n ∈ Finset.range N, (1 - r ^ (n + 1))
        ≤ ∏ n ∈ Finset.range N, ‖(1 - ModularForm.eta_q n (τ : ℂ))‖ :=
      Finset.prod_le_prod₀ (fun n _ => by
        have : r ^ (n+1) ≤ 1 := pow_le_one₀ hr0 (le_of_lt hr1)
        linarith) (fun n _ => hfac n)
    rw [norm_prod]
    linarith
  have hDelta : ‖Work.Kernels.DeltaFun τ‖
      = Real.exp (-(2*Real.pi*τ.im)) * ‖∏' n : ℕ, (1 - ModularForm.eta_q n (τ:ℂ))‖ ^ 24 := by
    rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant,
        ModularForm.discriminant_eq_q_prod, norm_mul, hmul.tprod_pow, norm_pow, ← hrdef, hnormq]
  have hbase : (1:ℝ)/2 ≤ (1 - 2*r)^24 := by
    have hb : (1:ℝ) - 48 * r ≤ (1 - 2*r)^24 := by
      have h1 : (1:ℝ) + (24:ℝ) * (-(2*r)) = 1 - 48*r := by ring
      have h2 : (1:ℝ) + -(2*r) = 1 - 2*r := by ring
      rw [← h1, ← h2]
      exact one_add_mul_le_pow (a := -(2*r)) (by linarith [hr0] : (-2:ℝ) ≤ -(2*r)) (24:ℕ)
    have h48 : 48 * r ≤ 1/2 := by linarith [hr_le]
    linarith
  have hnonneg : 0 ≤ 1 - 2*r := by linarith [hr_half]
  have h24 : (1:ℝ)/2 ≤ ‖∏' n : ℕ, (1 - ModularForm.eta_q n (τ:ℂ))‖ ^ 24 :=
    le_trans hbase (pow_le_pow_left₀ hnonneg hprod 24)
  have hqn : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2*Real.pi*τ.im)) :=
    Work.Asymptotics.norm_qParamFun τ
  rw [hqn]
  calc (1:ℝ)/2 * Real.exp (-(2*Real.pi*τ.im))
      = Real.exp (-(2*Real.pi*τ.im)) * (1/2) := by ring
    _ ≤ Real.exp (-(2*Real.pi*τ.im)) * ‖∏' n : ℕ, (1 - ModularForm.eta_q n (τ:ℂ))‖ ^ 24 :=
        mul_le_mul_of_nonneg_left h24 (Real.exp_nonneg _)
    _ = ‖Work.Kernels.DeltaFun τ‖ := hDelta.symm

/-- **The CKMRV divisor on the funnel, lower bound.**  For `τ ∈ 𝒟` with `Im τ ≥ 2` and `0 < t ≤ 1`, the divisor
`Δ(i/t)·(j(τ) - j(i/t))` is bounded below by a constant times the minimum of `1` and the distances from `τ` to the three
coincidence points `i/t`, `1 + i/t`, `-1 + i/t`, times `1 + exp(2π(Im τ - 1/t))`.

Proof strategy: `Δ(i/t)j(τ) = Δ(i/t)E₄(τ)³/Δ(τ)` and `Δ(i/t)j(i/t) = E₄(i/t)³`, so
`divisor = Δ(i/t)E₄(τ)³/Δ(τ) - E₄(i/t)³`; with `q = qParamFun`, `v = q(i/t)/q(τ)` one has
`divisor = (v - 1) + O(q(τ) + |q(τ)|²/|q(i/t)|)`, and `‖exp(2π(ε-ix)) - 1‖` with `ε = Im τ - 1/t`, `x = Re τ`
is bounded below by `c·min(1, ‖ε-ix‖, ‖(ε,x) - (0,±1)‖)`.  Available inputs: `E4Fun_two_term`, `DeltaFun_two_term`,
`DeltaFun_upper` (`Submission/Work/Asymptotics/KPlusXiDefs.lean`), `‖Δ‖ ≥ c·‖q‖` for `Im ≥ 1`,
`divisor_factor_lower_aux` (`Submission/Work/Asymptotics/Compact/flat_aux.lean`), and
`Work.FunnelNumerics.Delta_funnel_bounds`, `Work.FunnelNumerics.E4_funnel_bounds` on the funnel. -/
theorem DivisorFunnelBound : ∃ c : ℝ, 0 < c ∧ ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
    τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → t ≤ 1 →
    c * (min 1 (min ‖(τ : ℂ) - (t⁻¹ : ℂ) * Complex.I‖
      (min ‖(τ : ℂ) - ((1 : ℂ) + (t⁻¹ : ℂ) * Complex.I)‖
        ‖(τ : ℂ) - ((-1 : ℂ) + (t⁻¹ : ℂ) * Complex.I)‖))
      * (1 + Real.exp (2 * Real.pi * (τ.im - t⁻¹))))
    ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) *
       (Work.Kernels.jInvariantFun τ -
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)))‖ := by
  obtain ⟨cL, hcL, hL⟩ := E_jdiff_large
  obtain ⟨cA, hcA, hA⟩ := ExpTwoPiLatticeLower
  refine ⟨cL * cA / 2, by positivity, ?_⟩
  intro τ t ht hτD h2 ht1
  have htinv : 0 < t⁻¹ := inv_pos.mpr ht
  have htle : (1 : ℝ) ≤ t⁻¹ := (one_le_inv₀ ht).mpr ht1
  set z : UpperHalfPlane := Work.Kernels.imagAxis t⁻¹ htinv with hzdef
  have hzcoe : ((z : UpperHalfPlane) : ℂ) = ((t⁻¹ : ℝ) : ℂ) * Complex.I := rfl
  have hzim : z.im = t⁻¹ := by rw [hzdef]; simp [Work.Kernels.imagAxis]
  have hz1 : 1 ≤ z.im := by rw [hzim]; exact htle
  -- the `S`-translate of `τ` lies in `E`, and `j` is `S`-invariant
  have hmem : ModularGroup.S • τ ∈ KEpsilon := S_smul_mem_KEpsilon hτD h2
  have hE1 := hL (ModularGroup.S • τ) t⁻¹ htinv hmem htle
  rw [S_smul_S_smul] at hE1
  rw [Work.Kernels.KernelFacts.jInvariantFun_S_smul] at hE1
  rw [← hzdef] at hE1
  rw [← hzcoe] at hE1
  -- the `q`-parameters and `v = q z / q τ`
  set qz : ℂ := Work.Kernels.qParamFun z with hqz
  set qt : ℂ := Work.Kernels.qParamFun τ with hqt
  set v : ℂ := qz / qt with hv
  have hqz0 : qz ≠ 0 := Complex.exp_ne_zero _
  have hqt0 : qt ≠ 0 := Complex.exp_ne_zero _
  have hv0 : v ≠ 0 := by rw [hv]; exact div_ne_zero hqz0 hqt0
  have hqz_exp : qz = Complex.exp (2 * Real.pi * Complex.I * (z : ℂ)) := rfl
  have hqt_exp : qt = Complex.exp (2 * Real.pi * Complex.I * (τ : ℂ)) := rfl
  have hv_exp : v = Complex.exp (2 * Real.pi * Complex.I * ((z : ℂ) - (τ : ℂ))) := by
    rw [hv, hqz_exp, hqt_exp, ← Complex.exp_sub]
    congr 1; ring
  have hEun : Complex.exp (2 * Real.pi * Complex.I * ((τ : ℂ) - (z : ℂ))) * v = 1 := by
    rw [hv_exp, ← Complex.exp_add]
    rw [show 2 * Real.pi * Complex.I * ((τ : ℂ) - (z : ℂ))
        + 2 * Real.pi * Complex.I * ((z : ℂ) - (τ : ℂ)) = 0 by ring, Complex.exp_zero]
  have hEun_inv : Complex.exp (2 * Real.pi * Complex.I * ((τ : ℂ) - (z : ℂ))) = v⁻¹ :=
    eq_inv_of_mul_eq_one_left hEun
  have h1ven : ‖1 - Complex.exp (2 * Real.pi * Complex.I * ((τ : ℂ) - (z : ℂ)))‖
      = ‖v - 1‖ / ‖v‖ := by
    rw [hEun_inv]
    have h : 1 - v⁻¹ = (v - 1) / v := by field_simp
    rw [h, norm_div]
  have hqzez : ‖qz‖ * Real.exp (2 * Real.pi * τ.im) = ‖v‖ := by
    have hrenorm : (2 * Real.pi * Complex.I * (τ : ℂ)).re = -(2 * Real.pi * τ.im) := by
      simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, UpperHalfPlane.coe_im]
    have hqtinv : Real.exp (2 * Real.pi * τ.im) = ‖qt‖⁻¹ := by
      have hneg := Real.exp_neg (2 * Real.pi * τ.im)
      rw [hqt_exp, Complex.norm_exp, hrenorm, hneg, inv_inv]
    rw [hqtinv, hv, norm_div, div_eq_mul_inv]
  have hvpos : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hv0
  -- multiply the `E_jdiff_small` bound by `‖q z‖`
  have hE2 : cL * ‖v - 1‖ ≤ ‖qz‖ * ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := by
    have hstep := mul_le_mul_of_nonneg_left hE1 (norm_nonneg qz)
    calc cL * ‖v - 1‖
        = cL * ‖v‖ * (‖v - 1‖ / ‖v‖) := by field_simp
      _ = cL * (‖qz‖ * Real.exp (2 * Real.pi * τ.im)) * (‖v - 1‖ / ‖v‖) := by rw [hqzez]
      _ = ‖qz‖ * (cL * Real.exp (2 * Real.pi * τ.im) * (‖v - 1‖ / ‖v‖)) := by ring
      _ = ‖qz‖ * (cL * Real.exp (2 * Real.pi * τ.im)
            * ‖1 - Complex.exp (2 * Real.pi * Complex.I * ((τ : ℂ) - (z : ℂ)))‖) := by
          rw [h1ven]
      _ ≤ ‖qz‖ * ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := hstep
  -- the `Δ`-factor
  have hΔ : (1 / 2 : ℝ) * ‖qz‖ ≤ ‖Work.Kernels.DeltaFun z‖ := deltaFun_lower_im_one z hz1
  have hD : (cL / 2) * ‖v - 1‖
      ≤ ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ
          - Work.Kernels.jInvariantFun z)‖ := by
    rw [norm_mul]
    calc (cL / 2) * ‖v - 1‖ = (1 / 2 : ℝ) * (cL * ‖v - 1‖) := by ring
      _ ≤ (1 / 2 : ℝ) * (‖qz‖ * ‖Work.Kernels.jInvariantFun τ
            - Work.Kernels.jInvariantFun z‖) := by linarith [hE2]
      _ = ((1 / 2 : ℝ) * ‖qz‖) * ‖Work.Kernels.jInvariantFun τ
            - Work.Kernels.jInvariantFun z‖ := by ring
      _ ≤ ‖Work.Kernels.DeltaFun z‖ * ‖Work.Kernels.jInvariantFun τ
            - Work.Kernels.jInvariantFun z‖ :=
          mul_le_mul_of_nonneg_right hΔ (norm_nonneg _)
  -- the elementary exponential estimate
  have hx1 : |τ.re| ≤ 1 := by
    have h1 := hτD.1
    have h2 := hτD.2.1
    rw [abs_le]; exact ⟨by linarith, by linarith⟩
  have hExp := hA τ.re (τ.im - t⁻¹) hx1
  have hτcoe : (τ : ℂ) = (τ.re : ℂ) + (τ.im : ℂ) * Complex.I := by
    rw [← UpperHalfPlane.coe_re, ← UpperHalfPlane.coe_im]
    exact (Complex.re_add_im (τ : ℂ)).symm
  have hv_eq : v = Complex.exp (2 * Real.pi * (((τ.im - t⁻¹ : ℝ) : ℂ)
      - (τ.re : ℂ) * Complex.I)) := by
    rw [hv_exp]
    congr 1
    rw [hτcoe, hzcoe]
    apply Complex.ext <;>
      simp [← Complex.ofReal_inv, Complex.mul_re, Complex.mul_im] <;> ring
  have hω0 : (τ : ℂ) - (t⁻¹ : ℂ) * Complex.I
      = (τ.re : ℂ) + ((τ.im - t⁻¹ : ℝ) : ℂ) * Complex.I := by
    rw [hτcoe]
    apply Complex.ext <;>
      simp [← Complex.ofReal_inv, Complex.mul_re, Complex.mul_im] <;> ring
  have hω1 : (τ : ℂ) - ((1 : ℂ) + (t⁻¹ : ℂ) * Complex.I)
      = ((τ.re : ℂ) + ((τ.im - t⁻¹ : ℝ) : ℂ) * Complex.I) - 1 := by
    rw [hτcoe]
    apply Complex.ext <;>
      simp [← Complex.ofReal_inv, Complex.mul_re, Complex.mul_im] <;> ring
  have hω2 : (τ : ℂ) - ((-1 : ℂ) + (t⁻¹ : ℂ) * Complex.I)
      = ((τ.re : ℂ) + ((τ.im - t⁻¹ : ℝ) : ℂ) * Complex.I) + 1 := by
    rw [hτcoe]
    apply Complex.ext <;>
      simp [← Complex.ofReal_inv, Complex.mul_re, Complex.mul_im] <;> ring
  have hExp' : cA * ((min 1 (min ‖(τ : ℂ) - (t⁻¹ : ℂ) * Complex.I‖
        (min ‖(τ : ℂ) - ((1 : ℂ) + (t⁻¹ : ℂ) * Complex.I)‖
          ‖(τ : ℂ) - ((-1 : ℂ) + (t⁻¹ : ℂ) * Complex.I)‖)))
      * (1 + Real.exp (2 * Real.pi * (τ.im - t⁻¹)))) ≤ ‖v - 1‖ := by
    rw [hv_eq, ← mul_assoc]
    simpa only [hω0, hω1, hω2] using hExp
  -- assemble
  have key : (cL * cA / 2) * ((min 1 (min ‖(τ : ℂ) - (t⁻¹ : ℂ) * Complex.I‖
        (min ‖(τ : ℂ) - ((1 : ℂ) + (t⁻¹ : ℂ) * Complex.I)‖
          ‖(τ : ℂ) - ((-1 : ℂ) + (t⁻¹ : ℂ) * Complex.I)‖)))
      * (1 + Real.exp (2 * Real.pi * (τ.im - t⁻¹))))
      ≤ ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ
          - Work.Kernels.jInvariantFun z)‖ := by
    calc (cL * cA / 2) * ((min 1 (min ‖(τ : ℂ) - (t⁻¹ : ℂ) * Complex.I‖
        (min ‖(τ : ℂ) - ((1 : ℂ) + (t⁻¹ : ℂ) * Complex.I)‖
          ‖(τ : ℂ) - ((-1 : ℂ) + (t⁻¹ : ℂ) * Complex.I)‖)))
          * (1 + Real.exp (2 * Real.pi * (τ.im - t⁻¹))))
        = (cL / 2) * (cA * ((min 1 (min ‖(τ : ℂ) - (t⁻¹ : ℂ) * Complex.I‖
        (min ‖(τ : ℂ) - ((1 : ℂ) + (t⁻¹ : ℂ) * Complex.I)‖
          ‖(τ : ℂ) - ((-1 : ℂ) + (t⁻¹ : ℂ) * Complex.I)‖)))
          * (1 + Real.exp (2 * Real.pi * (τ.im - t⁻¹))))) := by ring
      _ ≤ (cL / 2) * ‖v - 1‖ := mul_le_mul_of_nonneg_left hExp' (by positivity)
      _ ≤ ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ
          - Work.Kernels.jInvariantFun z)‖ := hD
  exact key


end

end Work.Asymptotics

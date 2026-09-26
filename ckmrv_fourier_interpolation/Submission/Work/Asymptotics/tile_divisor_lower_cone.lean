/-
# Divisor lower bound on the cusp-`±1` tile cone

`Work.Asymptotics.tile_divisor_lower_cone` bounds the *divisor* of the CKMRV kernel,
`Δ(z)(j(n + w) - j(z))`, from below on the cone `{z ∈ ℍ : 1 ≤ Im z}` away from the pole `S w`
by the exponential `1 + e^{2π(A - Im z)}` with `A := Im (S w) ≥ 2`.

## Route

Put `τ := S • w` (so `A := τ.im ≥ 2`), `d := (z : ℂ) - (τ : ℂ)`, `β := d.im = z.im - τ.im`,
`ρ := e^{-2πβ} = e^{2π(A - z.im)}`.  With `e := qParamFun z / qParamFun τ = exp (2π i d)` and
`u := (Δ z / q z)·(q τ · j τ)`, the defining relation `Δ·j = E₄³` gives

  `Δ(z)(j(w) - j(z)) = Δ(z) j(w) - E₄(z)³ = e·u - E₄(z)³`,

and the two elementary bounds `‖u - 1‖ ≤ 1/8`, `‖E₄(z)³ - 1‖ ≤ κ` turn this into

  `‖Δ(z)(j w - j z)‖ ≥ max ((7/8)ρ - (1+κ), ‖e - 1‖ - ρ/8 - κ)`

(`Work.Asymptotics.cone_arith`).  The separation hypothesis is used only through `‖e - 1‖`
(`Work.Asymptotics.phase_mid_bound` in the middle range), together with the numbers
`‖Δ/q - 1‖ ≤ 1/20` (`Work.Asymptotics.DeltaFun_div_qParamFun_sub_one_le`) and the `q`-expansion
bound `‖E₄ - 1‖ ≤ 480 ‖q‖` (valid for `‖q‖ ≤ 1/32`, hence for `Im ≥ 1`).
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.FunnelNumerics.Delta_funnel_bounds
import Submission.Work.FunnelNumerics.E4_funnel_bounds

namespace Work.Asymptotics

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane

noncomputable section

/-! ## Elementary product, power and exponential estimates -/

private lemma cone_norm_prod_one_add_le {ι : Type*} (s : Finset ι) (g : ι → ℂ) :
    ‖∏ i ∈ s, (1 + g i)‖ ≤ ∏ i ∈ s, (1 + ‖g i‖) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, norm_mul]
      have h1 : ‖1 + g a‖ ≤ 1 + ‖g a‖ := by
        have := norm_add_le (1 : ℂ) (g a)
        rwa [norm_one] at this
      exact mul_le_mul h1 ih (norm_nonneg _) (by positivity)

private lemma cone_norm_prod_one_add_sub_one_le {ι : Type*} (s : Finset ι) (g : ι → ℂ) :
    ‖(∏ i ∈ s, (1 + g i)) - 1‖ ≤ (∏ i ∈ s, (1 + ‖g i‖)) - 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hrew : (1 + g a) * (∏ i ∈ s, (1 + g i)) - 1
          = g a * (∏ i ∈ s, (1 + g i)) + ((∏ i ∈ s, (1 + g i)) - 1) := by ring
      rw [hrew]
      have hnorm := cone_norm_prod_one_add_le s g
      have h1 : ‖g a * (∏ i ∈ s, (1 + g i))‖ ≤ ‖g a‖ * (∏ i ∈ s, (1 + ‖g i‖)) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      calc ‖g a * (∏ i ∈ s, (1 + g i)) + ((∏ i ∈ s, (1 + g i)) - 1)‖
          ≤ ‖g a * (∏ i ∈ s, (1 + g i))‖ + ‖(∏ i ∈ s, (1 + g i)) - 1‖ := norm_add_le _ _
        _ ≤ ‖g a‖ * (∏ i ∈ s, (1 + ‖g i‖)) + ((∏ i ∈ s, (1 + ‖g i‖)) - 1) := by
            linarith [h1, ih]
        _ = (1 + ‖g a‖) * (∏ i ∈ s, (1 + ‖g i‖)) - 1 := by ring

private lemma cone_prod_one_add_le_exp_sum {ι : Type*} (s : Finset ι) (t : ι → ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i) :
    ∏ i ∈ s, (1 + t i) ≤ Real.exp (∑ i ∈ s, t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have h1 : (1 + t a) * ∏ i ∈ s, (1 + t i)
          ≤ Real.exp (t a) * Real.exp (∑ i ∈ s, t i) := by
        refine mul_le_mul ?_ (ih fun i hi => ht i (Finset.mem_insert_of_mem hi)) ?_ ?_
        · linarith [Real.add_one_le_exp (t a)]
        · exact Finset.prod_nonneg fun i hi => by
            linarith [ht i (Finset.mem_insert_of_mem hi)]
        · exact Real.exp_nonneg _
      rwa [← Real.exp_add] at h1

/-- The infinite product of a multipliable family is within `exp (∑ ‖f n - 1‖) - 1` of `1`. -/
private lemma cone_norm_tprod_sub_one_le {f : ℕ → ℂ} (hM : Multipliable f)
    (hS : Summable fun n : ℕ => ‖f n - 1‖) {S : ℝ} (hSS : ∑' n, ‖f n - 1‖ ≤ S) :
    ‖(∏' n, f n) - 1‖ ≤ Real.exp S - 1 := by
  have htend : Filter.Tendsto (fun N : ℕ => ‖(∏ n ∈ Finset.range N, f n) - 1‖) Filter.atTop
      (nhds ‖(∏' n, f n) - 1‖) := (hM.tendsto_prod_tprod_nat.sub_const 1).norm
  refine le_of_tendsto htend ?_
  rw [Filter.eventually_atTop]
  refine ⟨0, fun N _ => ?_⟩
  have h1 := cone_norm_prod_one_add_sub_one_le (Finset.range N) (fun n => f n - 1)
  have hprod : (∏ n ∈ Finset.range N, (1 + (f n - 1))) = ∏ n ∈ Finset.range N, f n := by
    exact Finset.prod_congr rfl fun n _ => by ring
  rw [hprod] at h1
  have h2 := cone_prod_one_add_le_exp_sum (Finset.range N) (fun n => ‖f n - 1‖)
    (fun n _ => norm_nonneg _)
  have h3 : ∑ n ∈ Finset.range N, ‖f n - 1‖ ≤ S :=
    le_trans (hS.sum_le_tsum _ fun i _ => norm_nonneg _) hSS
  calc ‖(∏ n ∈ Finset.range N, f n) - 1‖
      ≤ (∏ n ∈ Finset.range N, (1 + ‖f n - 1‖)) - 1 := h1
    _ ≤ Real.exp (∑ n ∈ Finset.range N, ‖f n - 1‖) - 1 := by linarith
    _ ≤ Real.exp S - 1 := by
        have := Real.exp_le_exp.mpr h3
        linarith

/-- `‖z ^ n - 1‖ ≤ n ‖z - 1‖ (1 + ‖z - 1‖) ^ (n - 1)`. -/
private lemma cone_norm_pow_sub_one_le (z : ℂ) (n : ℕ) :
    ‖z ^ n - 1‖ ≤ n * ‖z - 1‖ * (1 + ‖z - 1‖) ^ (n - 1) := by
  have hgeom : z ^ n - 1 = (z - 1) * ∑ i ∈ Finset.range n, z ^ i := (mul_geom_sum z n).symm
  have hc1 : 1 ≤ 1 + ‖z - 1‖ := by have := norm_nonneg (z - 1); linarith
  have hz : ‖z‖ ≤ 1 + ‖z - 1‖ := by
    have := norm_sub_norm_le z 1
    rw [norm_one] at this
    linarith
  have h2 : ∀ i ∈ Finset.range n, ‖z ^ i‖ ≤ (1 + ‖z - 1‖) ^ (n - 1) := by
    intro i hi
    have hi' : i ≤ n - 1 := by
      have := Finset.mem_range.mp hi
      omega
    calc ‖z ^ i‖ = ‖z‖ ^ i := norm_pow _ _
      _ ≤ (1 + ‖z - 1‖) ^ i := pow_le_pow_left₀ (norm_nonneg _) hz i
      _ ≤ (1 + ‖z - 1‖) ^ (n - 1) := pow_le_pow_right₀ hc1 hi'
  have h1 : ‖∑ i ∈ Finset.range n, z ^ i‖ ≤ n * (1 + ‖z - 1‖) ^ (n - 1) := by
    calc ‖∑ i ∈ Finset.range n, z ^ i‖ ≤ ∑ i ∈ Finset.range n, ‖z ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range n, (1 + ‖z - 1‖) ^ (n - 1) := Finset.sum_le_sum h2
      _ = n * (1 + ‖z - 1‖) ^ (n - 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hgeom, norm_mul]
  calc ‖z - 1‖ * ‖∑ i ∈ Finset.range n, z ^ i‖
      ≤ ‖z - 1‖ * (n * (1 + ‖z - 1‖) ^ (n - 1)) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = n * ‖z - 1‖ * (1 + ‖z - 1‖) ^ (n - 1) := by ring

/-- `exp t - 1 ≤ t/(1 - t)` for `t < 1`. -/
private lemma cone_exp_sub_one_le {t : ℝ} (ht : t < 1) :
    Real.exp t - 1 ≤ t / (1 - t) := by
  have h1 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  have h2 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have h3 : 0 < 1 - t := by linarith
  have h4 : Real.exp t * (1 - t) ≤ 1 := by
    calc Real.exp t * (1 - t) ≤ Real.exp t * Real.exp (-t) :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos t).le
      _ = 1 := h2
  have h5 : (1 : ℝ) / (1 - t) - 1 = t / (1 - t) := by field_simp; ring
  have h6 : Real.exp t ≤ 1 / (1 - t) := (le_div_iff₀ h3).mpr h4
  linarith [h5, h6]

/-! ## Numerical bounds for the `q`-parameter -/

private lemma exp_nat_ge {n : ℕ} {B : ℝ} (hB : B ≤ (2.7182818283 : ℝ) ^ n) :
    B ≤ Real.exp (n : ℝ) := by
  have h6 : (2.7182818283 : ℝ) ^ n ≤ (Real.exp 1) ^ n :=
    pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le n
  have h6' : Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
    rw [show (n : ℝ) = ((n : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  rw [h6']
  linarith

private lemma exp_neg_le_inv {c B : ℝ} (h : B ≤ Real.exp c) (hB : 0 < B) :
    Real.exp (-c) ≤ 1 / B := by
  rw [Real.exp_neg, one_div, inv_le_inv₀ (Real.exp_pos c) hB]
  exact h

private lemma exp_two_pi_ge_512 : (512 : ℝ) ≤ Real.exp (2 * Real.pi) := by
  have hsplit : Real.exp (2 * Real.pi) = Real.exp 6 * Real.exp (2 * Real.pi - 6) := by
    rw [← Real.exp_add]; ring_nf
  have h6 : (2.7182818283 : ℝ) ^ 6 ≤ Real.exp 6 := by
    have h := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 6
    have h' : Real.exp (6 : ℝ) = (Real.exp 1) ^ 6 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h']; exact h
  have hexp0 : (1 + 7 / 25 : ℝ) ≤ Real.exp (2 * Real.pi - 6) := by
    have h2 : (7 / 25 : ℝ) ≤ 2 * Real.pi - 6 := by nlinarith [Real.pi_gt_d2]
    linarith [Real.add_one_le_exp (2 * Real.pi - 6)]
  rw [hsplit]
  calc (512 : ℝ) ≤ (2.7182818283 : ℝ) ^ 6 * (1 + 7 / 25) := by norm_num
    _ ≤ Real.exp 6 * (1 + 7 / 25) := by linarith [h6, Real.exp_pos 6]
    _ ≤ Real.exp 6 * Real.exp (2 * Real.pi - 6) :=
        mul_le_mul_of_nonneg_left hexp0 (Real.exp_pos 6).le
    _ = Real.exp 6 * Real.exp (2 * Real.pi - 6) := rfl

private lemma exp_neg_half_le : Real.exp (-(1 / 2 : ℝ)) ≤ 2 / 3 := by
  have h3 : (3 : ℝ) / 2 ≤ Real.exp (1 / 2) := by
    have := Real.add_one_le_exp (1 / 2 : ℝ); linarith
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 2 / 3)]
  linarith

private lemma exp_half_ge : (3 : ℝ) / 2 ≤ Real.exp (1 / 2) := by
  have := Real.add_one_le_exp (1 / 2 : ℝ); linarith

private lemma exp_three_ge_twenty : (20 : ℝ) ≤ Real.exp 3 := by
  have h : Real.exp (3 : ℝ) = (Real.exp 1) ^ 3 := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  rw [h]
  have hge : (2.7182818283 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283) hge 3
  norm_num at h3
  linarith

private lemma exp_pi_div_six_le : Real.exp (Real.pi / 6) ≤ 211 / 100 := by
  have h : Real.pi / 6 ≤ 21 / 40 := by nlinarith [Real.pi_lt_d2]
  refine (Real.exp_le_exp.mpr h).trans ?_
  have h1 := cone_exp_sub_one_le (t := (21 / 40 : ℝ)) (by norm_num)
  have h2 : (21 / 40 : ℝ) / (1 - 21 / 40) = 21 / 19 := by norm_num
  rw [h2] at h1
  linarith

private lemma norm_qParam_le_of_im {τ : ℍ} {c B : ℝ}
    (hc : -(2 * Real.pi * τ.im) ≤ c) (hB : Real.exp c ≤ B) :
    ‖Work.Kernels.qParamFun τ‖ ≤ B := by
  rw [Work.Asymptotics.norm_qParamFun]
  exact (Real.exp_le_exp.mpr hc).trans hB

private lemma norm_qParam_le_512 (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.qParamFun τ‖ ≤ 1 / 512 := by
  rw [Work.Asymptotics.norm_qParamFun]
  exact (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hτ])).trans
    (exp_neg_le_inv (c := 2 * Real.pi) exp_two_pi_ge_512 (by norm_num))

private lemma norm_qParam_le_8000 (τ : ℍ) (hτ : 3 / 2 ≤ τ.im) :
    ‖Work.Kernels.qParamFun τ‖ ≤ 1 / 8000 := by
  rw [Work.Asymptotics.norm_qParamFun]
  exact (Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three, hτ])).trans
    (exp_neg_le_inv (c := 9) (exp_nat_ge (n := 9) (by norm_num)) (by norm_num))

private lemma norm_qParam_le_22000 (τ : ℍ) (hτ : 5 / 3 ≤ τ.im) :
    ‖Work.Kernels.qParamFun τ‖ ≤ 1 / 22000 := by
  rw [Work.Asymptotics.norm_qParamFun]
  exact (Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three, hτ])).trans
    (exp_neg_le_inv (c := 10) (exp_nat_ge (n := 10) (by norm_num)) (by norm_num))

private lemma norm_qParam_le_162000 (τ : ℍ) (hτ : 2 ≤ τ.im) :
    ‖Work.Kernels.qParamFun τ‖ ≤ 1 / 162000 := by
  rw [Work.Asymptotics.norm_qParamFun]
  exact (Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three, hτ])).trans
    (exp_neg_le_inv (c := 12) (exp_nat_ge (n := 12) (by norm_num)) (by norm_num))

/-! ## The `q`-expansion bound for `E₄` -/

private lemma summable_succ_pow_four_mul_shift' (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1 / 32) :
    Summable (fun m : ℕ => ((m : ℝ) + 1) ^ 4 * x ^ (m + 1)) := by
  have h16 : ‖(16 * x : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  refine Summable.of_nonneg_of_le (fun m => by positivity)
    (fun m => Work.FunnelNumerics.succ_pow_four_mul_shift_le_majorant x hx m) ?_
  exact (summable_geometric_of_norm_lt_one h16).mul_left x

private lemma tsum_succ_pow_four_mul_shift_le' (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1 / 32) :
    ∑' m : ℕ, ((m : ℝ) + 1) ^ 4 * x ^ (m + 1) ≤ 2 * x := by
  have h16 : ‖(16 * x : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hmaj : Summable (fun m : ℕ => x * (16 * x) ^ m) :=
    (summable_geometric_of_norm_lt_one h16).mul_left x
  calc ∑' m : ℕ, ((m : ℝ) + 1) ^ 4 * x ^ (m + 1)
      ≤ ∑' m : ℕ, x * (16 * x) ^ m :=
        Summable.tsum_le_tsum
          (fun m => Work.FunnelNumerics.succ_pow_four_mul_shift_le_majorant x hx m)
          (summable_succ_pow_four_mul_shift' x hx hx1) hmaj
    _ = x * ∑' m : ℕ, (16 * x) ^ m := tsum_mul_left
    _ = x * (1 - 16 * x)⁻¹ := by rw [tsum_geometric_of_norm_lt_one h16]
    _ ≤ 2 * x := by
        have h1 : 0 < 1 - 16 * x := by linarith
        have h2 : (1 : ℝ) / 2 ≤ 1 - 16 * x := by linarith
        have hinv : (1 - 16 * x)⁻¹ ≤ 2 := by
          have hh := (inv_le_inv₀ h1 (by norm_num : (0 : ℝ) < 1 / 2)).mpr h2
          simpa using hh
        nlinarith [hx, hinv, h1.le]

/-- `‖E₄ τ - 1‖ ≤ 480 ‖q τ‖` whenever `‖q τ‖ ≤ 1/512` (in particular for `Im τ ≥ 1`). -/
private lemma E4_sub_one_le_480 (τ : ℍ) (hq : ‖Work.Kernels.qParamFun τ‖ ≤ 1 / 512) :
    ‖Work.Kernels.E4Fun τ - 1‖ ≤ 480 * ‖Work.Kernels.qParamFun τ‖ := by
  have hx : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ≤ 1 / 512 := by
    rw [← Work.Asymptotics.qParamFun_eq_qParam]; exact hq
  have hxnn : 0 ≤ ‖Function.Periodic.qParam 1 (τ : ℂ)‖ := norm_nonneg _
  rw [← (Work.FunnelNumerics.E4_hasSum_shift τ).tsum_eq]
  have hterm : ∀ m : ℕ, ‖(PowerSeries.coeff (m + 1)) (UpperHalfPlane.qExpansion 1 Work.Modular.E4)
      * Function.Periodic.qParam 1 (τ : ℂ) ^ (m + 1)‖
      ≤ 240 * (((m : ℝ) + 1) ^ 4 * ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (m + 1)) := by
    intro m
    rw [norm_mul, norm_pow]
    have hc := Work.FunnelNumerics.E4_coeff_succ_le m
    have hxn : (0 : ℝ) ≤ ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (m + 1) := by positivity
    calc ‖(PowerSeries.coeff (m + 1)) (UpperHalfPlane.qExpansion 1 Work.Modular.E4)‖
          * ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (m + 1)
        ≤ (240 * ((m : ℝ) + 1) ^ 4) * ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (m + 1) :=
          mul_le_mul_of_nonneg_right hc hxn
      _ = 240 * (((m : ℝ) + 1) ^ 4 * ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (m + 1)) := by ring
  have hmaj : Summable (fun m : ℕ => 240 * (((m : ℝ) + 1) ^ 4 *
      ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (m + 1))) :=
    (summable_succ_pow_four_mul_shift' _ hxnn (hx.trans (by norm_num))).mul_left 240
  have hsm : Summable (fun m : ℕ => ‖(PowerSeries.coeff (m + 1))
      (UpperHalfPlane.qExpansion 1 Work.Modular.E4)
      * Function.Periodic.qParam 1 (τ : ℂ) ^ (m + 1)‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hterm hmaj
  calc ‖∑' m : ℕ, (PowerSeries.coeff (m + 1)) (UpperHalfPlane.qExpansion 1 Work.Modular.E4)
        * Function.Periodic.qParam 1 (τ : ℂ) ^ (m + 1)‖
      ≤ ∑' m : ℕ, ‖(PowerSeries.coeff (m + 1)) (UpperHalfPlane.qExpansion 1 Work.Modular.E4)
        * Function.Periodic.qParam 1 (τ : ℂ) ^ (m + 1)‖ := norm_tsum_le_tsum_norm hsm
    _ ≤ ∑' m : ℕ, 240 * (((m : ℝ) + 1) ^ 4 *
        ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (m + 1)) :=
        Summable.tsum_le_tsum hterm hsm hmaj
    _ = 240 * ∑' m : ℕ, ((m : ℝ) + 1) ^ 4 *
        ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (m + 1) := tsum_mul_left
    _ ≤ 240 * (2 * ‖Function.Periodic.qParam 1 (τ : ℂ)‖) := by
        have hb := tsum_succ_pow_four_mul_shift_le' ‖Function.Periodic.qParam 1 (τ : ℂ)‖
          hxnn (hx.trans (by norm_num))
        linarith
    _ = 480 * ‖Work.Kernels.qParamFun τ‖ := by
        rw [Work.Asymptotics.qParamFun_eq_qParam]; ring

/-- If `‖w - 1‖ ≤ c` then `‖w ^ 3 - 1‖ ≤ (1 + c) ^ 3 - 1`. -/
private lemma cone_norm_cube_sub_one_le {w : ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : ‖w - 1‖ ≤ c) : ‖w ^ 3 - 1‖ ≤ (1 + c) ^ 3 - 1 := by
  have hw : ‖w‖ ≤ 1 + c := by
    have hh := norm_sub_norm_le w 1
    rw [norm_one] at hh
    linarith
  have h2 : ‖w ^ 2 + w + 1‖ ≤ (1 + c) ^ 2 + (1 + c) + 1 := by
    have h3 : ‖w ^ 2 + w + 1‖ ≤ ‖w ^ 2 + w‖ + 1 := by
      have hh := norm_add_le (w ^ 2 + w) (1 : ℂ)
      rwa [norm_one] at hh
    have h4 : ‖w ^ 2 + w‖ ≤ ‖w ^ 2‖ + ‖w‖ := norm_add_le _ _
    rw [norm_pow] at h4
    nlinarith [h3, h4, hw, norm_nonneg w]
  have h1 : w ^ 3 - 1 = (w - 1) * (w ^ 2 + w + 1) := by ring
  rw [h1, norm_mul]
  calc ‖w - 1‖ * ‖w ^ 2 + w + 1‖ ≤ c * ((1 + c) ^ 2 + (1 + c) + 1) :=
        mul_le_mul h h2 (norm_nonneg _) hc
    _ = (1 + c) ^ 3 - 1 := by ring

/-- `‖E₄ τ ^ 3 - 1‖ ≤ κ` from `‖q τ‖ ≤ B` and the numeric comparison. -/
private lemma E4_cube_close_of (τ : ℍ) {B κ : ℝ} (hB : ‖Work.Kernels.qParamFun τ‖ ≤ B)
    (hB512 : B ≤ 1 / 512) (hB0 : 0 ≤ B) (hκ : (1 + 480 * B) ^ 3 - 1 ≤ κ) :
    ‖Work.Kernels.E4Fun τ ^ 3 - 1‖ ≤ κ := by
  have h480 := E4_sub_one_le_480 τ (hB.trans hB512)
  have h1 : ‖Work.Kernels.E4Fun τ - 1‖ ≤ 480 * B := by
    calc ‖Work.Kernels.E4Fun τ - 1‖ ≤ 480 * ‖Work.Kernels.qParamFun τ‖ := h480
      _ ≤ 480 * B := by linarith
  have h2 := cone_norm_cube_sub_one_le (by positivity) h1
  linarith [h2, hκ]

/-! ## The `eta`-product ratio `Δ/q` is close to `1` above height `1` -/

/-- `‖Δ τ / q(τ) - 1‖ ≤ 1/20` for `Im τ ≥ 1`.  Indeed `Δ/q = ∏' n (1 - q^{n+1})^24`, the eta
product deviates from `1` by at most `1/510` (its deviations `‖q‖^{n+1}` sum to `≤ 1/511`), and
raising to the 24-th power costs at most a factor `24 (1 + 1/510)^23`. -/
theorem DeltaFun_div_qParamFun_sub_one_le (τ : UpperHalfPlane) (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.DeltaFun τ / Work.Kernels.qParamFun τ - 1‖ ≤ 1 / 20 := by
  have hq_lt : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos (by rw [UpperHalfPlane.coe_im]; exact τ.im_pos)
  have hq512 : ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ≤ 1 / 512 := by
    rw [← Work.Asymptotics.qParamFun_eq_qParam]
    exact norm_qParam_le_512 τ hτ
  have hq0 : 0 ≤ ‖Function.Periodic.qParam 1 (τ : ℂ)‖ := norm_nonneg _
  have hmul : Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n (τ : ℂ)) :=
    ModularForm.multipliable_one_sub_pow hq_lt
  have hdev : ∀ n : ℕ, ‖(1 - ModularForm.eta_q n (τ : ℂ)) - 1‖
      = ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (n + 1) := by
    intro n
    have hval : (1 - ModularForm.eta_q n (τ : ℂ)) - 1
        = -(Function.Periodic.qParam 1 (τ : ℂ)) ^ (n + 1) := by
      rw [ModularForm.eta_q]; ring
    rw [hval, norm_neg, norm_pow]
  have hSsum : Summable (fun n : ℕ => ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one hq0 hq_lt)
  have hS : Summable (fun n : ℕ => ‖(1 - ModularForm.eta_q n (τ : ℂ)) - 1‖) := by
    simpa only [hdev] using hSsum
  have htsum : ∑' n : ℕ, ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (n + 1)
      = ‖Function.Periodic.qParam 1 (τ : ℂ)‖ * (1 - ‖Function.Periodic.qParam 1 (τ : ℂ)‖)⁻¹ := by
    have h1 : ∑' n : ℕ, ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ (n + 1)
        = ‖Function.Periodic.qParam 1 (τ : ℂ)‖ *
            ∑' n : ℕ, ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ n := by
      rw [← tsum_mul_left]
      exact tsum_congr fun n => by rw [pow_succ']
    have hgeo : ∑' n : ℕ, ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ n
        = (1 - ‖Function.Periodic.qParam 1 (τ : ℂ)‖)⁻¹ := by
      refine tsum_geometric_of_norm_lt_one ?_
      rwa [Real.norm_eq_abs, abs_of_nonneg hq0]
    rw [h1, hgeo]
  have hbound : ∑' n, ‖(1 - ModularForm.eta_q n (τ : ℂ)) - 1‖ ≤ 1 / 511 := by
    rw [tsum_congr hdev, htsum]
    rw [mul_inv_le_iff₀ (by linarith : (0 : ℝ) < 1 - ‖Function.Periodic.qParam 1 (τ : ℂ)‖)]
    have h512 := hq512
    nlinarith [h512, hq0]
  have hclose : ‖(∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ))) - 1‖ ≤ 1 / 510 := by
    have hmain := cone_norm_tprod_sub_one_le hmul hS (S := 1 / 511) hbound
    have hexp : Real.exp (1 / 511 : ℝ) - 1 ≤ 1 / 510 := by
      have h := cone_exp_sub_one_le (t := (1 / 511 : ℝ)) (by norm_num)
      have hval : (1 / 511 : ℝ) / (1 - 1 / 511) = 1 / 510 := by norm_num
      rw [hval] at h
      exact h
    linarith
  have hD : Work.Kernels.DeltaFun τ
      = Work.Kernels.qParamFun τ * (∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ))) ^ 24 := by
    rw [Work.Kernels.DeltaFun, CuspForm.coe_discriminant, ModularForm.discriminant_eq_q_prod]
    congr 1
    · rw [Work.Asymptotics.qParamFun_eq_qParam]
    · rw [hmul.tprod_pow]
  have hΔq : Work.Kernels.DeltaFun τ / Work.Kernels.qParamFun τ
      = (∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ))) ^ 24 := by
    rw [hD]
    field_simp
  rw [hΔq]
  have h24 := cone_norm_pow_sub_one_le (∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ))) 24
  have hgc : (1 + ‖(∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ))) - 1‖) ^ (24 - 1)
      ≤ (1 + 1 / 510) ^ 23 := by
    have h0 : (0 : ℝ) ≤ 1 + ‖(∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ))) - 1‖ :=
      add_nonneg zero_le_one (norm_nonneg _)
    have h1 : 1 + ‖(∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ))) - 1‖ ≤ 1 + 1 / 510 := by
      linarith
    exact pow_le_pow_left₀ h0 h1 23
  refine h24.trans ?_
  have hstep : 24 * ‖(∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ))) - 1‖
      * (1 + ‖(∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ))) - 1‖) ^ (24 - 1)
      ≤ 24 * (1 / 510) * (1 + 1 / 510) ^ 23 := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hclose (by norm_num)
    · exact hgc
    · exact pow_nonneg (add_nonneg zero_le_one (norm_nonneg _)) 23
    · norm_num
  linarith [hstep, show (24 : ℝ) * (1 / 510) * (1 + 1 / 510) ^ 23 ≤ 1 / 20 by norm_num]

/-! ## The middle-range phase bound -/

/-- `‖exp z - 1‖² = (e^{Re z} - cos (Im z))² + sin² (Im z)`. -/
private lemma cone_norm_exp_sq_cos (z : ℂ) :
    ‖Complex.exp z - 1‖ ^ 2 = (Real.exp z.re - Real.cos z.im) ^ 2 + (Real.sin z.im) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.exp_re,
    Complex.exp_im, Complex.one_re, Complex.one_im]
  have hcs := Real.cos_sq_add_sin_sq z.im
  have he : Real.exp z.re * Real.exp z.re = Real.exp (2 * z.re) := by
    rw [← Real.exp_add]; ring_nf
  nlinarith [hcs, he]

/-- `‖exp z - 1‖² = e^{2 Re z} - 2 e^{Re z} cos (Im z) + 1`. -/
private lemma cone_norm_exp_sq_lin (z : ℂ) :
    ‖Complex.exp z - 1‖ ^ 2 = Real.exp (2 * z.re) - 2 * Real.exp z.re * Real.cos z.im + 1 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.exp_re,
    Complex.exp_im, Complex.one_re, Complex.one_im]
  have hcs := Real.cos_sq_add_sin_sq z.im
  have he : Real.exp z.re * Real.exp z.re = Real.exp (2 * z.re) := by
    rw [← Real.exp_add]; ring_nf
  nlinarith [hcs, he]

/-- **Middle-range phase bound.**  If `d` avoids all integers by `1/8` and `|Im d| ≤ 1/12` then
`‖exp (2π i d) - 1‖ ≥ 1/2`. -/
theorem phase_mid_bound (d : ℂ) (h : ∀ k : ℤ, (1 / 8 : ℝ) ≤ ‖d - ((k : ℤ) : ℂ)‖)
    (him : |d.im| ≤ 1 / 12) :
    (1 / 2 : ℝ) ≤ ‖Complex.exp (2 * Real.pi * Complex.I * d) - 1‖ := by
  set k : ℤ := Int.floor (d.re + 1 / 2) with hk
  have hk1 : ((k : ℤ) : ℝ) ≤ d.re + 1 / 2 := Int.floor_le _
  have hk2 : d.re + 1 / 2 < ((k : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  set w : ℂ := d - ((k : ℤ) : ℂ) with hwdef
  have hwre : w.re = d.re - ((k : ℤ) : ℝ) := by
    rw [hwdef]
    simp only [Complex.sub_re, Complex.intCast_re]
  have hwim : w.im = d.im := by
    rw [hwdef]
    simp only [Complex.sub_im, Complex.intCast_im, sub_zero]
  have hkabs : |w.re| ≤ 1 / 2 := by
    rw [hwre, abs_le]
    constructor <;> linarith
  have hsep := h k
  have hspsq : (1 / 8 : ℝ) ^ 2 ≤ w.re ^ 2 + w.im ^ 2 := by
    have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [← hsq]
    exact pow_le_pow_left₀ (by norm_num) hsep 2
  have hβsq : w.im ^ 2 ≤ (1 / 12 : ℝ) ^ 2 := by
    have hb := abs_le.mp him
    rw [hwim]
    nlinarith [hb.1, hb.2]
  have hw2 : (1 / 12 : ℝ) ^ 2 ≤ w.re ^ 2 := by nlinarith [hspsq, hβsq]
  have hwabs : (1 / 12 : ℝ) ≤ |w.re| := by
    have h1 : (1 / 12 : ℝ) ^ 2 ≤ |w.re| ^ 2 := by rw [sq_abs]; exact hw2
    nlinarith [h1, abs_nonneg w.re]
  have hexp : Complex.exp (2 * Real.pi * Complex.I * d)
      = Complex.exp (2 * Real.pi * Complex.I * w) := by
    have hshift : 2 * Real.pi * Complex.I * d
        = ((k : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) + 2 * Real.pi * Complex.I * w := by
      have hd : d = ((k : ℤ) : ℂ) + w := by rw [hwdef]; ring
      rw [hd, mul_add]
      ring
    rw [hshift, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]
  set z : ℂ := 2 * Real.pi * Complex.I * w with hz
  have hzre : z.re = -(2 * Real.pi * w.im) := by
    rw [hz]
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hzim : z.im = 2 * Real.pi * w.re := by
    rw [hz]
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have habs : ∀ t : ℝ, |2 * Real.pi * t| = 2 * Real.pi * |t| := by
    intro t
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
  rcases le_or_gt (1 / 4 : ℝ) |w.re| with hcase | hcase
  · -- `|Re w| ≥ 1/4`: the cosine term dominates
    have hθle : 2 * Real.pi * |w.re| ≤ Real.pi := by nlinarith [Real.pi_pos, hkabs]
    have hθge : Real.pi / 2 ≤ 2 * Real.pi * |w.re| := by nlinarith [Real.pi_pos, hcase]
    have hcos : Real.cos z.im ≤ 0 := by
      rw [← Real.cos_abs, hzim, habs]
      exact Real.cos_nonpos_of_pi_div_two_le_of_le hθge (by linarith [Real.pi_pos])
    have h1 : (1 : ℝ) ≤ ‖Complex.exp z - 1‖ := by
      have hsq := cone_norm_exp_sq_lin z
      have hb : (1 : ℝ) ≤ ‖Complex.exp z - 1‖ ^ 2 := by
        rw [hsq]
        have hp : (0 : ℝ) ≤ Real.exp z.re := Real.exp_nonneg _
        have hp2 : (0 : ℝ) ≤ Real.exp (2 * z.re) := Real.exp_nonneg _
        nlinarith [hp, hp2, hcos, mul_nonneg hp (neg_nonneg.mpr hcos)]
      nlinarith [hb, norm_nonneg (Complex.exp z - 1)]
    rw [hexp]
    linarith
  · -- `1/12 ≤ |Re w| ≤ 1/4`: the sine term dominates
    have hθle : |z.im| ≤ Real.pi / 2 := by rw [hzim, habs]; nlinarith [Real.pi_pos, hcase]
    have hθge : Real.pi / 6 ≤ |z.im| := by rw [hzim, habs]; nlinarith [Real.pi_pos, hwabs]
    have hsin : (1 / 2 : ℝ) ≤ |Real.sin z.im| := by
      rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (by linarith [hθle, Real.pi_pos])]
      calc (1 / 2 : ℝ) = Real.sin (Real.pi / 6) := Real.sin_pi_div_six.symm
        _ ≤ Real.sin |z.im| :=
            Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hθle hθge
    have h1 : (1 / 2 : ℝ) ≤ ‖Complex.exp z - 1‖ := by
      have hsq := cone_norm_exp_sq_cos z
      have hb : (1 / 2 : ℝ) ^ 2 ≤ ‖Complex.exp z - 1‖ ^ 2 := by
        rw [hsq]
        have h2 : (1 / 2 : ℝ) ^ 2 ≤ (Real.sin z.im) ^ 2 := by
          have hs := sq_abs (Real.sin z.im)
          nlinarith [hsin, hs, abs_nonneg (Real.sin z.im)]
        nlinarith [h2, sq_nonneg (Real.exp z.re - Real.cos z.im)]
      nlinarith [hb, norm_nonneg (Complex.exp z - 1)]
    rw [hexp]
    exact h1

/-! ## Integer translations of `j` -/

private lemma jInvariantFun_nat_vadd : ∀ (m : ℕ) (τ : ℍ),
    Work.Kernels.jInvariantFun ((m : ℝ) +ᵥ τ) = Work.Kernels.jInvariantFun τ := by
  intro m
  induction m with
  | zero => intro τ; simp
  | succ k ih =>
      intro τ
      have h1 : (((k + 1 : ℕ) : ℝ) +ᵥ τ) = (1 : ℝ) +ᵥ (((k : ℕ) : ℝ) +ᵥ τ) := by
        rw [← add_vadd]; push_cast; ring_nf
      rw [h1, Work.Kernels.KernelFacts.jInvariantFun_vadd_one, ih]

private lemma jInvariantFun_int_vadd (k : ℤ) (τ : ℍ) :
    Work.Kernels.jInvariantFun ((k : ℝ) +ᵥ τ) = Work.Kernels.jInvariantFun τ := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · rw [hm]; push_cast; exact jInvariantFun_nat_vadd m τ
  · rw [hm]
    have h1 : (((m : ℕ) : ℝ) +ᵥ ((-((m : ℕ) : ℝ)) +ᵥ τ)) = τ := by rw [← add_vadd]; simp
    have h2 := jInvariantFun_nat_vadd m ((-((m : ℕ) : ℝ)) +ᵥ τ)
    rw [h1] at h2
    push_cast
    exact h2.symm

/-! ## The two-branch arithmetic of the divisor bound -/

/-- If `‖e‖ = ρ`, `g ≤ ‖e - 1‖`, `‖u - 1‖ ≤ δ` and `‖F - 1‖ ≤ κ` then `‖eu - F‖` is at least
both `(1-δ)ρ - (1+κ)` and `g - δρ - κ`. -/
theorem cone_arith (e u F : ℂ) (ρ g δ κ : ℝ)
    (hρ : ‖e‖ = ρ) (hg : g ≤ ‖e - 1‖) (hu : ‖u - 1‖ ≤ δ) (hF : ‖F - 1‖ ≤ κ) :
    max ((1 - δ) * ρ - (1 + κ)) (g - δ * ρ - κ) ≤ ‖e * u - F‖ := by
  have hρ0 : 0 ≤ ρ := by rw [← hρ]; exact norm_nonneg e
  refine max_le ?_ ?_
  · have hu' : (1 - δ) ≤ ‖u‖ := by
      have hh := norm_sub_norm_le (1 : ℂ) u
      rw [norm_one, norm_sub_rev] at hh
      linarith
    have hF' : ‖F‖ ≤ 1 + κ := by
      have hh := norm_sub_norm_le F 1
      rw [norm_one] at hh
      linarith
    have h1 : (1 - δ) * ρ ≤ ‖e * u‖ := by
      rw [norm_mul, hρ]
      nlinarith [hu', hρ0, norm_nonneg e, norm_nonneg u]
    have h2 : ‖e * u‖ - ‖F‖ ≤ ‖e * u - F‖ := norm_sub_norm_le _ _
    linarith
  · have h1 : e * u - F = (e - 1) + e * (u - 1) - (F - 1) := by ring
    have h3 : ‖(e - 1) + e * (u - 1) - (F - 1)‖
        ≥ ‖(e - 1) + e * (u - 1)‖ - ‖F - 1‖ := norm_sub_norm_le _ _
    have h4 : ‖(e - 1) + e * (u - 1)‖ ≥ ‖e - 1‖ - ‖e * (u - 1)‖ := by
      have hh := norm_sub_norm_le (e - 1) (-(e * (u - 1)))
      rw [norm_neg, sub_neg_eq_add] at hh
      exact hh
    have h5 : ‖e * (u - 1)‖ ≤ δ * ρ := by
      rw [norm_mul, hρ]
      calc ρ * ‖u - 1‖ = ‖u - 1‖ * ρ := by ring
        _ ≤ δ * ρ := mul_le_mul_of_nonneg_right hu hρ0
    rw [h1]
    linarith

private lemma one_sub_norm_le_norm_sub_one (x : ℂ) : 1 - ‖x‖ ≤ ‖x - 1‖ := by
  have hh := norm_sub_norm_le (1 : ℂ) x
  rw [norm_one, norm_sub_rev] at hh
  exact hh

/-- The `g - δρ - κ` branch gives the goal. -/
private lemma cone_le_of_B (e u F : ℂ) (ρ g κ c : ℝ)
    (hρ : ‖e‖ = ρ) (hg : g ≤ ‖e - 1‖) (hu : ‖u - 1‖ ≤ 1 / 8) (hF : ‖F - 1‖ ≤ κ)
    (hB : c * (1 + ρ) ≤ g - (1 / 8 : ℝ) * ρ - κ) :
    c * (1 + ρ) ≤ ‖e * u - F‖ :=
  hB.trans ((le_max_right _ _).trans (cone_arith e u F ρ g (1 / 8) κ hρ hg hu hF))

/-- The `(1 - δ)ρ - (1 + κ)` branch gives the goal. -/
private lemma cone_le_of_A (e u F : ℂ) (ρ g κ c : ℝ)
    (hρ : ‖e‖ = ρ) (hg : g ≤ ‖e - 1‖) (hu : ‖u - 1‖ ≤ 1 / 8) (hF : ‖F - 1‖ ≤ κ)
    (hA : c * (1 + ρ) ≤ (1 - (1 / 8 : ℝ)) * ρ - (1 + κ)) :
    c * (1 + ρ) ≤ ‖e * u - F‖ :=
  hA.trans ((le_max_left _ _).trans (cone_arith e u F ρ g (1 / 8) κ hρ hg hu hF))

/-! ## The main theorem -/

/-- **Divisor lower bound on the cusp-`±1` tile cone.**

For `w ∈ E = KEpsilon` (so `A := Im (S • w) ≥ 2`) and `z` in the *cone* `{z : 1 ≤ Im z}` whose
`S`-image is at distance `≥ 1/8` from `S • w` modulo the parabolic translations `ℤ`, the divisor
`Δ(z)(j(n + w) - j(z))` of the CKMRV kernel is bounded below by the exponential
`1 + e^{2π(A - Im z)}` (saturated at the constant `1` when `Im z ≥ A`). -/
theorem tile_divisor_lower_cone :
    ∃ c : ℝ, 0 < c ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon →
      ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ (z : UpperHalfPlane), 1 ≤ z.im →
        (∀ k : ℤ, (1 / 8 : ℝ) ≤
          ‖(z : ℂ) - ((ModularGroup.S • w : UpperHalfPlane) : ℂ) - ((k : ℤ) : ℂ)‖) →
        c * (1 + Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - z.im)))
          ≤ ‖Work.Kernels.DeltaFun z *
              (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) - Work.Kernels.jInvariantFun z)‖ := by
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro w hw n hn z hz hsep
  set τ : UpperHalfPlane := ModularGroup.S • w with hτdef
  have hA : 2 ≤ τ.im := hw.2
  have hjτ : Work.Kernels.jInvariantFun w = Work.Kernels.jInvariantFun τ := by
    rw [hτdef]; exact (Work.Kernels.KernelFacts.jInvariantFun_S_smul w).symm
  have hnj : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) = Work.Kernels.jInvariantFun τ :=
    (jInvariantFun_int_vadd n w).trans hjτ
  have hdiv : ‖Work.Kernels.DeltaFun z *
        (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) - Work.Kernels.jInvariantFun z)‖
      = ‖Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ - Work.Kernels.E4Fun z ^ 3‖ := by
    rw [hnj]
    rw [mul_sub]
    rw [Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun]
  rw [hdiv]
  set e : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((z : ℂ) - (τ : ℂ))) with hedef
  set A1 : ℂ := Work.Kernels.DeltaFun z / Work.Kernels.qParamFun z with hA1def
  set B1 : ℂ := Work.Kernels.qParamFun τ * Work.Kernels.jInvariantFun τ with hB1def
  have heu : e * (A1 * B1) = Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ := by
    have hqz : Work.Kernels.qParamFun z ≠ 0 := qParamFun_ne_zero' z
    have hqτ : Work.Kernels.qParamFun τ ≠ 0 := qParamFun_ne_zero' τ
    have hratio : Work.Kernels.qParamFun z / Work.Kernels.qParamFun τ = e := by
      rw [hedef, Work.Kernels.qParamFun, Work.Kernels.qParamFun, ← Complex.exp_sub]
      congr 1
      ring
    rw [hA1def, hB1def, ← hratio]
    field_simp
  rw [← heu]
  have hqτn : Work.Kernels.qParamFun τ ≠ 0 := Complex.exp_ne_zero _
  have hΔτn : Work.Kernels.DeltaFun τ ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ
  -- bounds on `A1` and `B1`
  have hA1 : ‖A1 - 1‖ ≤ 1 / 20 := by
    rw [hA1def]; exact DeltaFun_div_qParamFun_sub_one_le z hz
  have hAτ : ‖Work.Kernels.DeltaFun τ / Work.Kernels.qParamFun τ - 1‖ ≤ 1 / 20 :=
    DeltaFun_div_qParamFun_sub_one_le τ (le_trans (by norm_num) hA)
  have hEτ : ‖Work.Kernels.E4Fun τ ^ 3 - 1‖ ≤ 1 / 100 :=
    E4_cube_close_of τ (norm_qParam_le_162000 τ hA) (by norm_num) (by norm_num) (by norm_num)
  have hB1b : ‖B1 - 1‖ ≤ 1 / 15 := by
    have hj : Work.Kernels.jInvariantFun τ
        = Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ := rfl
    have hrew : B1 - 1 = (Work.Kernels.E4Fun τ ^ 3
          - Work.Kernels.DeltaFun τ / Work.Kernels.qParamFun τ)
        / (Work.Kernels.DeltaFun τ / Work.Kernels.qParamFun τ) := by
      rw [hB1def, hj]
      field_simp
    rw [hrew, norm_div]
    have hPpos : (19 / 20 : ℝ) ≤ ‖Work.Kernels.DeltaFun τ / Work.Kernels.qParamFun τ‖ := by
      have hh := one_sub_norm_le_norm_sub_one (Work.Kernels.DeltaFun τ / Work.Kernels.qParamFun τ)
      linarith [hAτ]
    have hnum : ‖Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.DeltaFun τ / Work.Kernels.qParamFun τ‖
        ≤ 1 / 100 + 1 / 20 := by
      have hh : Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.DeltaFun τ / Work.Kernels.qParamFun τ
          = (Work.Kernels.E4Fun τ ^ 3 - 1)
            - (Work.Kernels.DeltaFun τ / Work.Kernels.qParamFun τ - 1) := by ring
      rw [hh]
      have := norm_sub_le (Work.Kernels.E4Fun τ ^ 3 - 1)
        (Work.Kernels.DeltaFun τ / Work.Kernels.qParamFun τ - 1)
      linarith
    calc ‖Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.DeltaFun τ / Work.Kernels.qParamFun τ‖
          / ‖Work.Kernels.DeltaFun τ / Work.Kernels.qParamFun τ‖
        ≤ (1 / 100 + 1 / 20) / (19 / 20) :=
          div_le_div₀ (by norm_num) hnum (by norm_num) hPpos
      _ ≤ 1 / 15 := by norm_num
  have hu : ‖A1 * B1 - 1‖ ≤ 1 / 8 := by
    have h1 : A1 * B1 - 1 = (A1 - 1) * B1 + (B1 - 1) := by ring
    rw [h1]
    have hB1n : ‖B1‖ ≤ 1 + 1 / 15 := by
      have hh := norm_sub_norm_le B1 1
      rw [norm_one] at hh
      linarith
    calc ‖(A1 - 1) * B1 + (B1 - 1)‖ ≤ ‖(A1 - 1) * B1‖ + ‖B1 - 1‖ := norm_add_le _ _
      _ ≤ (1 / 20) * (1 + 1 / 15) + 1 / 15 := by
          rw [norm_mul]
          have hh := mul_le_mul hA1 hB1n (norm_nonneg B1) (by norm_num)
          linarith
      _ ≤ 1 / 8 := by norm_num
  -- the cone coordinates
  set β : ℝ := ((z : ℂ) - (τ : ℂ)).im with hβdef
  have hβeq : β = z.im - τ.im := by
    rw [hβdef]
    simp only [Complex.sub_im, UpperHalfPlane.coe_im]
  have hnorme : ‖e‖ = Real.exp (-(2 * Real.pi * β)) := by
    rw [hedef, Complex.norm_exp, hβdef]
    congr 1
    simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  have hexpβ : Real.exp (2 * Real.pi * (τ.im - z.im)) = Real.exp (-(2 * Real.pi * β)) := by
    rw [hβeq]; congr 1; ring
  have hsep' : ∀ k : ℤ, (1 / 8 : ℝ) ≤ ‖((z : ℂ) - (τ : ℂ)) - ((k : ℤ) : ℂ)‖ := by
    intro k
    have hh := hsep k
    rw [hτdef] at hh
    exact hh
  have hmain : (1 / 100) * (1 + Real.exp (-(2 * Real.pi * β)))
      ≤ ‖e * (A1 * B1) - Work.Kernels.E4Fun z ^ 3‖ := by
    rcases le_or_gt (1 / 12 : ℝ) β with hβL | hβL
    · -- Case `β ≥ 1/12`: `ρ ≤ 2/3`, the `1 - ρ` branch
      have hzim : 2 ≤ z.im := by linarith [hA, hβL, hβeq]
      have hκ : ‖Work.Kernels.E4Fun z ^ 3 - 1‖ ≤ 1 / 100 :=
        E4_cube_close_of z (norm_qParam_le_162000 z hzim) (by norm_num) (by norm_num) (by norm_num)
      have hρ : Real.exp (-(2 * Real.pi * β)) ≤ 2 / 3 := by
        have h1 : -(2 * Real.pi * β) ≤ -(1 / 2 : ℝ) := by
          have : (1 / 2 : ℝ) ≤ 2 * Real.pi * β := by nlinarith [Real.pi_gt_three, hβL]
          linarith
        exact (Real.exp_le_exp.mpr h1).trans exp_neg_half_le
      have hg : 1 - Real.exp (-(2 * Real.pi * β)) ≤ ‖e - 1‖ := by
        rw [← hnorme]
        exact one_sub_norm_le_norm_sub_one e
      refine cone_le_of_B e (A1 * B1) (Work.Kernels.E4Fun z ^ 3)
        (Real.exp (-(2 * Real.pi * β))) (1 - Real.exp (-(2 * Real.pi * β))) (1 / 100) (1 / 100)
        hnorme hg hu hκ ?_
      have hp := Real.exp_pos (-(2 * Real.pi * β))
      linarith
    · rcases le_or_gt (-(1 / 12) : ℝ) β with hβM | hβM
      · -- Case `|β| ≤ 1/12`: the sharp phase bound
        have hzim : 5 / 3 ≤ z.im := by linarith [hA, hβM, hβeq]
        have hκ : ‖Work.Kernels.E4Fun z ^ 3 - 1‖ ≤ 1 / 14 :=
          E4_cube_close_of z (norm_qParam_le_22000 z hzim) (by norm_num) (by norm_num) (by norm_num)
        have hρ : Real.exp (-(2 * Real.pi * β)) ≤ 211 / 100 := by
          have h1 : -(2 * Real.pi * β) ≤ Real.pi / 6 := by
            nlinarith [Real.pi_pos, hβM]
          exact (Real.exp_le_exp.mpr h1).trans exp_pi_div_six_le
        have hg : (1 / 2 : ℝ) ≤ ‖e - 1‖ := by
          have him : |((z : ℂ) - (τ : ℂ)).im| ≤ 1 / 12 := by
            rw [← hβdef, abs_le]
            exact ⟨hβM, le_of_lt hβL⟩
          have hph := phase_mid_bound ((z : ℂ) - (τ : ℂ)) hsep' him
          rwa [hedef]
        refine cone_le_of_B e (A1 * B1) (Work.Kernels.E4Fun z ^ 3)
          (Real.exp (-(2 * Real.pi * β))) (1 / 2) (1 / 14) (1 / 100) hnorme hg hu hκ ?_
        have hp := Real.exp_pos (-(2 * Real.pi * β))
        linarith
      · rcases le_or_gt (-(1 / 2) : ℝ) β with hβR | hβR
        · -- Case `-1/2 ≤ β ≤ -1/12`: `ρ ≥ 3/2`, the `ρ - 1` branch
          have hzim : 3 / 2 ≤ z.im := by linarith [hA, hβR, hβeq]
          have hκ : ‖Work.Kernels.E4Fun z ^ 3 - 1‖ ≤ 1 / 5 :=
            E4_cube_close_of z (norm_qParam_le_8000 z hzim) (by norm_num) (by norm_num)
              (by norm_num)
          have hρ : (3 / 2 : ℝ) ≤ Real.exp (-(2 * Real.pi * β)) := by
            have h1 : (1 / 2 : ℝ) ≤ -(2 * Real.pi * β) := by
              have h2 : β ≤ -(1 / 12 : ℝ) := hβM.le
              nlinarith [Real.pi_gt_three]
            exact exp_half_ge.trans (Real.exp_le_exp.mpr h1)
          have hg : Real.exp (-(2 * Real.pi * β)) - 1 ≤ ‖e - 1‖ := by
            have hh := norm_sub_norm_le e 1
            rw [norm_one, hnorme] at hh
            exact hh
          refine cone_le_of_B e (A1 * B1) (Work.Kernels.E4Fun z ^ 3)
            (Real.exp (-(2 * Real.pi * β))) (Real.exp (-(2 * Real.pi * β)) - 1) (1 / 5)
            (1 / 100) hnorme hg hu hκ ?_
          linarith
        · -- Case `β ≤ -1/2`: `ρ ≥ 20`, the `(1-δ)ρ` branch
          have hzim : 1 ≤ z.im := hz
          have hκ : ‖Work.Kernels.E4Fun z ^ 3 - 1‖ ≤ 7 :=
            E4_cube_close_of z (norm_qParam_le_512 z hzim) (by norm_num) (by norm_num) (by norm_num)
          have hρ : (20 : ℝ) ≤ Real.exp (-(2 * Real.pi * β)) := by
            have h1 : (3 : ℝ) ≤ -(2 * Real.pi * β) := by
              have h2 : β ≤ -(1 / 2 : ℝ) := le_of_lt hβR
              nlinarith [Real.pi_gt_three]
            exact exp_three_ge_twenty.trans (Real.exp_le_exp.mpr h1)
          have hg : Real.exp (-(2 * Real.pi * β)) - 1 ≤ ‖e - 1‖ := by
            have hh := norm_sub_norm_le e 1
            rw [norm_one, hnorme] at hh
            exact hh
          refine cone_le_of_A e (A1 * B1) (Work.Kernels.E4Fun z ^ 3)
            (Real.exp (-(2 * Real.pi * β))) (Real.exp (-(2 * Real.pi * β)) - 1) (7) (1 / 100)
            hnorme hg hu hκ ?_
          linarith
  rw [hexpβ]
  exact hmain

end

end Work.Asymptotics

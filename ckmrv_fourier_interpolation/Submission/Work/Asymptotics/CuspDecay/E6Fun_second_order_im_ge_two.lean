import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Modular.E6_qExpansion_coeff

namespace Work.Asymptotics.CuspDecay

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm Manifold

noncomputable section

/-! ## Elementary estimates

The proof of the explicit second-order `q`-expansion bound for `E₆` rests on two elementary
inequalities: a comparison of the sixth power with a geometric sequence, and the numerical
bound `e^{-4π} ≤ 1/200`.
-/

/-- `((n : ℝ) + 2) ^ 6 ≤ 64 * 32 ^ n` for every `n : ℕ`.  The base `32` is chosen so that the
induction is uniform: for `n ≥ 0` one has `n + 3 ≤ (3/2) (n + 2)` and `(3/2)^6 = 729/64 < 32`. -/
private lemma add_two_pow_six_le (n : ℕ) : ((n : ℝ) + 2) ^ 6 ≤ 64 * 32 ^ n := by
  induction n with
  | zero => norm_num
  | succ k _ih =>
    have hk1 : (((k + 1 : ℕ) : ℝ) + 2) = (k : ℝ) + 3 := by push_cast; ring
    rw [hk1]
    have h1 : ((k : ℝ) + 3) ≤ (3 / 2) * ((k : ℝ) + 2) := by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have h2 : ((k : ℝ) + 3) ^ 6 ≤ ((3 / 2) * ((k : ℝ) + 2)) ^ 6 :=
      pow_le_pow_left₀ (by linarith) h1 6
    have h3 : ((3 / 2 : ℝ) * ((k : ℝ) + 2)) ^ 6 = (729 / 64) * ((k : ℝ) + 2) ^ 6 := by ring
    have h4 : (729 / 64 : ℝ) * ((k : ℝ) + 2) ^ 6 ≤ 32 * ((k : ℝ) + 2) ^ 6 :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    calc ((k : ℝ) + 3) ^ 6 ≤ ((3 / 2) * ((k : ℝ) + 2)) ^ 6 := h2
      _ = (729 / 64) * ((k : ℝ) + 2) ^ 6 := h3
      _ ≤ 32 * ((k : ℝ) + 2) ^ 6 := h4
      _ ≤ 32 * (64 * 32 ^ k) := by linarith
      _ = 64 * 32 ^ (k + 1) := by rw [pow_succ]; ring

/-- `e^{-4π} ≤ 1/200`. -/
private lemma exp_neg_four_pi_le_inv_two_hundred : Real.exp (-(4 * Real.pi)) ≤ 1 / 200 := by
  have h1 : Real.exp (-(4 * Real.pi)) ≤ Real.exp (-12) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_gt_three]
  have h2 : Real.exp (-12) ≤ 1 / 200 := by
    have h4 : (200 : ℝ) ≤ Real.exp 12 := by
      have h : Real.exp 12 = (Real.exp 1) ^ 12 := by simp
      rw [h]
      have h5 : (2.7182818283 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 :=
        pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 12
      have h3 : (200 : ℝ) ≤ (2.7182818283 : ℝ) ^ 12 := by norm_num
      linarith
    have hprod : Real.exp 12 * Real.exp (-12) = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-12), h4, hprod]
  linarith

/-! ## The second-order bound -/

/-- Second-order `q`-expansion of `E₆` on the region `Im ≥ 2`, with an **explicit** constant.

On `Im u ≥ 2` one has `‖q u‖ = e^{-2π Im u} ≤ e^{-4π} ≤ 1/200`.  The `q`-expansion
`E₆ = 1 - 504 ∑_{n ≥ 1} σ₅(n) qⁿ` (`Work.Modular.E6_qExpansion_coeff`, via
`UpperHalfPlane.hasSum_qExpansion`) together with the elementary comparisons
`σ₅(m+2) ≤ (m+2)⁶` and `(m+2)⁶ ≤ 64·32^m` (valid for all `m : ℕ`) gives the tail bound
`∑_{m ≥ 0} (m+2)⁶ ‖q‖^m ≤ 64/(1 - 32‖q‖) ≤ 64·(25/21)` (using `‖q u‖ ≤ 1/200`), hence
`‖E₆ u - 1 + 504 q u‖ ≤ 504 · 64 · 25/21 · ‖q u‖² = 38400 ‖q u‖² < 40000 ‖q u‖²`.

The point of the explicit constant is that it must be comparable with the concrete number
`‖q u‖ ≤ 1/200`; an existential constant from `Work.Residues.E6FunSecondOrder` cannot be. -/
theorem E6Fun_second_order_im_ge_two (u : UpperHalfPlane) (hu : 2 ≤ u.im) :
    ‖Work.Kernels.E6Fun u - 1 + 504 * Work.Kernels.qParamFun u‖
      ≤ 40000 * ‖Work.Kernels.qParamFun u‖ ^ 2 := by
  -- `E₆` is periodic of period one, holomorphic, and bounded at the cusp.
  have hper : Function.Periodic (Work.Kernels.E6Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E6Fun := ModularForm.holo' ModularForm.E₆
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty Work.Kernels.E6Fun :=
    ModularFormClass.bdd_at_infty ModularForm.E₆
  -- The `q`-expansion of `E₆`, shifted by two.
  have hs := UpperHalfPlane.hasSum_qExpansion (h := 1) (f := Work.Kernels.E6Fun)
    one_pos hper hhol hbdd u
  have hs2 := (hasSum_nat_add_iff' 2).mpr hs
  have hq_eq : Function.Periodic.qParam 1 (u : ℂ) = Work.Kernels.qParamFun u := by
    simp [Function.Periodic.qParam, Work.Kernels.qParamFun]
  rw [hq_eq] at hs2
  -- The constant and linear coefficients of the `q`-expansion of `E₆` are `1` and `-504`.
  have hc0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 0 = 1 := by
    rw [Work.Modular.E6_qExpansion_coeff]; simp
  have hc1 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 1 = -504 := by
    rw [Work.Modular.E6_qExpansion_coeff]
    norm_num [ArithmeticFunction.sigma]
  have hsum2 : (∑ i ∈ Finset.range 2,
      (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff i
        • Work.Kernels.qParamFun u ^ i) = 1 - 504 * Work.Kernels.qParamFun u := by
    rw [Finset.sum_range_succ, Finset.sum_range_one, hc0, hc1]
    ring
  rw [hsum2] at hs2
  -- `E₆ u - 1 + 504 q u` is the tail of the `q`-expansion starting at `q²`.
  have hrep : Work.Kernels.E6Fun u - 1 + 504 * Work.Kernels.qParamFun u
      = ∑' n : ℕ, (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 2)
          • Work.Kernels.qParamFun u ^ (n + 2) := by
    rw [hs2.tsum_eq]; ring
  -- The numerical upper bound `‖q u‖ ≤ 1/200`.
  have hqnorm : ‖Work.Kernels.qParamFun u‖ = Real.exp (-(2 * Real.pi * u.im)) := by
    rw [← hq_eq, Function.Periodic.norm_qParam, div_one, UpperHalfPlane.coe_im]
    congr 1; ring
  have hr0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun u‖ := norm_nonneg _
  have hr1 : ‖Work.Kernels.qParamFun u‖ ≤ 1 / 200 := by
    rw [hqnorm]
    have h1 : Real.exp (-(2 * Real.pi * u.im)) ≤ Real.exp (-(4 * Real.pi)) := by
      rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hu]
    linarith [exp_neg_four_pi_le_inv_two_hundred]
  have h32r : 32 * ‖Work.Kernels.qParamFun u‖ ≤ 4 / 25 := by linarith
  have h32r0 : (0 : ℝ) ≤ 32 * ‖Work.Kernels.qParamFun u‖ := by linarith
  have h32r_lt : 32 * ‖Work.Kernels.qParamFun u‖ < 1 := by linarith
  -- Coefficient bound: `‖c m‖ ≤ 504 m⁶`.
  have hcoeff : ∀ m : ℕ, 1 ≤ m →
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff m‖ ≤ 504 * (m : ℝ) ^ 6 := by
    intro m hm
    have hm0 : m ≠ 0 := by omega
    rw [Work.Modular.E6_qExpansion_coeff m, if_neg hm0, norm_mul]
    have h504 : ‖(-504 : ℂ)‖ = (504 : ℝ) := by norm_num
    rw [h504, Complex.norm_natCast]
    have hσ : (ArithmeticFunction.sigma 5 m : ℝ) ≤ (m : ℝ) ^ 6 := by
      have h' : ArithmeticFunction.sigma 5 m ≤ m ^ 6 := by
        simpa using ArithmeticFunction.sigma_le_pow_succ 5 m
      exact_mod_cast h'
    exact mul_le_mul_of_nonneg_left hσ (by norm_num)
  -- Termwise bound.
  have hterm : ∀ n : ℕ,
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 2)
        • Work.Kernels.qParamFun u ^ (n + 2)‖
      ≤ 504 * 64 * ‖Work.Kernels.qParamFun u‖ ^ 2
          * (32 * ‖Work.Kernels.qParamFun u‖) ^ n := by
    intro n
    have hc : ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 2)‖
        ≤ 504 * ((n : ℝ) + 2) ^ 6 := by
      have h := hcoeff (n + 2) (by omega)
      simpa using h
    have hpoly : ((n : ℝ) + 2) ^ 6 ≤ 64 * 32 ^ n := add_two_pow_six_le n
    have hsplit : ‖Work.Kernels.qParamFun u‖ ^ (n + 2)
        = ‖Work.Kernels.qParamFun u‖ ^ 2 * ‖Work.Kernels.qParamFun u‖ ^ n := by
      rw [pow_add]; ring
    calc ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 2)
          • Work.Kernels.qParamFun u ^ (n + 2)‖
        = ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 2)‖
            * ‖Work.Kernels.qParamFun u‖ ^ (n + 2) := by
          rw [smul_eq_mul, norm_mul, norm_pow]
      _ ≤ (504 * ((n : ℝ) + 2) ^ 6) * ‖Work.Kernels.qParamFun u‖ ^ (n + 2) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 504 * (((n : ℝ) + 2) ^ 6 * ‖Work.Kernels.qParamFun u‖ ^ (n + 2)) := by ring
      _ ≤ 504 * ((64 * 32 ^ n) * ‖Work.Kernels.qParamFun u‖ ^ (n + 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hpoly (by positivity)
      _ = 504 * 64 * ‖Work.Kernels.qParamFun u‖ ^ 2
            * (32 * ‖Work.Kernels.qParamFun u‖) ^ n := by
          rw [hsplit, mul_pow]; ring
  -- Summability of the majorant.
  have hmaj : Summable (fun n : ℕ => 504 * 64 * ‖Work.Kernels.qParamFun u‖ ^ 2
      * (32 * ‖Work.Kernels.qParamFun u‖) ^ n) :=
    Summable.mul_left _ (summable_geometric_of_lt_one h32r0 h32r_lt)
  have hsumm : Summable (fun n : ℕ =>
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 2)
        • Work.Kernels.qParamFun u ^ (n + 2)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmaj
  -- The numerical comparison `504·64/(1 - 32‖q‖) ≤ 38400`.
  have h1m : 0 < 1 - 32 * ‖Work.Kernels.qParamFun u‖ := by linarith
  have hge : (21 : ℝ) / 25 ≤ 1 - 32 * ‖Work.Kernels.qParamFun u‖ := by linarith
  have hinv : (1 - 32 * ‖Work.Kernels.qParamFun u‖)⁻¹ ≤ 25 / 21 := by
    have h := (inv_le_inv₀ h1m (by norm_num : (0 : ℝ) < 21 / 25)).mpr hge
    rwa [show ((21 : ℝ) / 25)⁻¹ = 25 / 21 by norm_num] at h
  rw [hrep]
  calc ‖∑' n : ℕ, (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 2)
        • Work.Kernels.qParamFun u ^ (n + 2)‖
      ≤ ∑' n : ℕ, ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 2)
        • Work.Kernels.qParamFun u ^ (n + 2)‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' n : ℕ, 504 * 64 * ‖Work.Kernels.qParamFun u‖ ^ 2
          * (32 * ‖Work.Kernels.qParamFun u‖) ^ n :=
        Summable.tsum_le_tsum hterm hsumm hmaj
    _ = 504 * 64 * ‖Work.Kernels.qParamFun u‖ ^ 2
          * (1 - 32 * ‖Work.Kernels.qParamFun u‖)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one h32r0 h32r_lt]
    _ ≤ 504 * 64 * ‖Work.Kernels.qParamFun u‖ ^ 2 * (25 / 21) := by
        apply mul_le_mul_of_nonneg_left hinv
        positivity
    _ = 38400 * ‖Work.Kernels.qParamFun u‖ ^ 2 := by ring
    _ ≤ 40000 * ‖Work.Kernels.qParamFun u‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

end

end Work.Asymptotics.CuspDecay

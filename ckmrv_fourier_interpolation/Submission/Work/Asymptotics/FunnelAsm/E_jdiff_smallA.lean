/-
# Comparison of `j(w)` with `j(i t)` on the cusp-`0` tile `E = KEpsilon`

(statement + proof outline in the docstrings below)
-/
import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.EBase
import Submission.Work.Modular.E4_qExpansion_coeff
import Submission.Work.Modular.E6_qExpansion_coeff
import Submission.Work.Residues.QExpansionTail
import Submission.Work.Residues.E4FunSecondOrder
import Submission.Work.Residues.E6FunSecondOrder
import Submission.Work.Residues.DeltaExpansion
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atZero
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq

noncomputable section

open UpperHalfPlane ModularGroup ModularForm
open scoped MatrixGroups UpperHalfPlane Manifold

namespace Work.Asymptotics

/-! ## Elementary properties of the `q`-parameter -/

lemma norm_qParamFun_eq (τ : ℍ) :
    ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
  rw [Work.Kernels.qParamFun, Complex.norm_exp]
  congr 1
  have hrw : 2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)
      = ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * (τ : ℂ)) := by push_cast; ring
  rw [hrw, Complex.mul_re, Complex.I_mul_re, Complex.ofReal_re, Complex.ofReal_im,
    UpperHalfPlane.coe_im]
  ring

lemma qParamFun_ne_zero (τ : ℍ) : Work.Kernels.qParamFun τ ≠ 0 := Complex.exp_ne_zero _

lemma norm_qParamFun_le_exp (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.qParamFun τ‖ ≤ Real.exp (-(2 * Real.pi)) := by
  rw [norm_qParamFun_eq, Real.exp_le_exp]; nlinarith [Real.pi_pos, hτ]

lemma norm_qParamFun_le_one_A (τ : ℍ) : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := by
  rw [norm_qParamFun_eq, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, τ.im_pos])

/-- `e^{-2π} ≤ 1/512`. -/
lemma exp_neg_two_pi_le_inv512 : Real.exp (-(2 * Real.pi)) ≤ 1 / 512 := by
  have hpi : (6.28 : ℝ) < 2 * Real.pi := by linarith [Real.pi_gt_d20]
  have h1 : Real.exp (-(2 * Real.pi)) ≤ Real.exp (-6.28) := by
    rw [Real.exp_le_exp]; linarith
  have h2 : Real.exp (-6.28) ≤ 1 / 512 := by
    have hexp : (512 : ℝ) ≤ Real.exp 6.28 := by
      have hsplit : Real.exp 6.28 = Real.exp 6 * Real.exp 0.28 := by
        rw [← Real.exp_add]; norm_num
      have h6 : (400 : ℝ) ≤ Real.exp 6 := by
        have h : Real.exp 6 = (Real.exp 1) ^ 6 := by simp
        rw [h]
        have h1' : (2.7182818283 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 :=
          pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 6
        have h2' : (400 : ℝ) ≤ (2.7182818283 : ℝ) ^ 6 := by norm_num
        linarith
      have h028 : (1.28 : ℝ) ≤ Real.exp 0.28 := by
        have := Real.add_one_le_exp (0.28 : ℝ)
        linarith
      rw [hsplit]
      nlinarith
    have hpos : 0 < Real.exp 6.28 := Real.exp_pos _
    have hprod : Real.exp 6.28 * Real.exp (-6.28) = 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-6.28 : ℝ)]
  linarith

lemma norm_qParamFun_le_inv512 (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.qParamFun τ‖ ≤ 1 / 512 := by
  rw [norm_qParamFun_eq]
  have h1 : Real.exp (-(2 * Real.pi * τ.im)) ≤ Real.exp (-(2 * Real.pi)) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hτ]
  linarith [exp_neg_two_pi_le_inv512]

/-- `n⁴ ≤ 4 · 3ⁿ` for all `n : ℕ`. -/
lemma pow_four_le_four_mul_three_pow (n : ℕ) : (n : ℝ) ^ 4 ≤ 4 * 3 ^ n := by
  have aux : ∀ m : ℕ, 5 ≤ m → ((m : ℝ)) ^ 4 ≤ 4 * (3 : ℝ) ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have hk5 : (5 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by linarith
      have h1 : (k : ℝ) + 1 ≤ (6 / 5) * (k : ℝ) := by linarith
      have h2 : ((k : ℝ) + 1) ^ 4 ≤ ((6 / 5) * (k : ℝ)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) h1 4
      have h3 : ((6 / 5) * (k : ℝ)) ^ 4 = (1296 / 625) * (k : ℝ) ^ 4 := by ring
      have h4 : (1296 / 625 : ℝ) * (k : ℝ) ^ 4 ≤ 3 * (k : ℝ) ^ 4 := by
        nlinarith [pow_nonneg hk0 4]
      have h5 : 3 * (k : ℝ) ^ 4 ≤ 3 * (4 * (3 : ℝ) ^ k) := by linarith
      have h6 : 3 * (4 * (3 : ℝ) ^ k) = 4 * (3 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
      calc (((k + 1 : ℕ)) : ℝ) ^ 4 = ((k : ℝ) + 1) ^ 4 := by push_cast; ring
        _ ≤ ((6 / 5) * (k : ℝ)) ^ 4 := h2
        _ = (1296 / 625) * (k : ℝ) ^ 4 := h3
        _ ≤ 3 * (k : ℝ) ^ 4 := h4
        _ ≤ 4 * (3 : ℝ) ^ (k + 1) := by rw [← h6]; linarith
  rcases Nat.lt_or_ge n 5 with hn | hn
  · interval_cases n <;> norm_num
  · exact aux n hn

/-- `n⁶ ≤ 1000 · 4ⁿ` for all `n : ℕ`. -/
lemma pow_six_le (n : ℕ) : (n : ℝ) ^ 6 ≤ 1000 * 4 ^ n := by
  have aux : ∀ m : ℕ, 8 ≤ m → ((m : ℝ)) ^ 6 ≤ 1000 * (4 : ℝ) ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ k hk ih =>
      have hk8 : (8 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by linarith
      have h1 : (k : ℝ) + 1 ≤ (9 / 8) * (k : ℝ) := by linarith
      have h2 : ((k : ℝ) + 1) ^ 6 ≤ ((9 / 8) * (k : ℝ)) ^ 6 :=
        pow_le_pow_left₀ (by positivity) h1 6
      have h3 : ((9 / 8) * (k : ℝ)) ^ 6 = (531441 / 262144) * (k : ℝ) ^ 6 := by ring
      have h4 : (531441 / 262144 : ℝ) * (k : ℝ) ^ 6 ≤ 4 * (k : ℝ) ^ 6 := by
        nlinarith [pow_nonneg hk0 6]
      have h5 : 4 * (k : ℝ) ^ 6 ≤ 4 * (1000 * (4 : ℝ) ^ k) := by linarith
      have h6 : 4 * (1000 * (4 : ℝ) ^ k) = 1000 * (4 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring
      calc (((k + 1 : ℕ)) : ℝ) ^ 6 = ((k : ℝ) + 1) ^ 6 := by push_cast; ring
        _ ≤ ((9 / 8) * (k : ℝ)) ^ 6 := h2
        _ = (531441 / 262144) * (k : ℝ) ^ 6 := h3
        _ ≤ 4 * (k : ℝ) ^ 6 := h4
        _ ≤ 1000 * (4 : ℝ) ^ (k + 1) := by rw [← h6]; linarith
  rcases Nat.lt_or_ge n 8 with hn | hn
  · interval_cases n <;> norm_num
  · exact aux n hn

/-! ## The three-term `q`-expansions of `E₄`, `E₆` and `Δ` on `Im τ ≥ 1` -/

/-- `((n : ℝ) + 3)⁶ ≤ 1100 · 4ⁿ` (the sharper comparison used for the `E₆` tail). -/
lemma pow_six_shift (n : ℕ) : ((n : ℝ) + 3) ^ 6 ≤ 1100 * 4 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      rcases Nat.lt_or_ge 5 k with hk | hk
      · have hk5 : (5 : ℝ) ≤ (k : ℝ) := by
          have : (5 : ℕ) ≤ k := le_of_lt hk
          exact_mod_cast this
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := by linarith
        have h1 : (k : ℝ) + 4 ≤ (9 / 8) * ((k : ℝ) + 3) := by linarith
        have h2 : ((k : ℝ) + 4) ^ 6 ≤ ((9 / 8) * ((k : ℝ) + 3)) ^ 6 :=
          pow_le_pow_left₀ (by positivity) h1 6
        have h3 : ((9 / 8) * ((k : ℝ) + 3)) ^ 6 = (531441 / 262144) * ((k : ℝ) + 3) ^ 6 := by
          ring
        have h4 : (531441 / 262144 : ℝ) * ((k : ℝ) + 3) ^ 6 ≤ 4 * ((k : ℝ) + 3) ^ 6 := by
          nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) + 3) 6]
        have h5 : 4 * ((k : ℝ) + 3) ^ 6 ≤ 4 * (1100 * 4 ^ k) := by linarith
        have h6 : 4 * (1100 * (4 : ℝ) ^ k) = 1100 * 4 ^ (k + 1) := by rw [pow_succ]; ring
        have hgoal : (((k + 1 : ℕ)) : ℝ) + 3 = (k : ℝ) + 4 := by push_cast; ring
        rw [hgoal]
        calc ((k : ℝ) + 4) ^ 6 ≤ 4 * ((k : ℝ) + 3) ^ 6 :=
              le_trans h2 (le_trans (le_of_eq h3) h4)
          _ ≤ 1100 * 4 ^ (k + 1) := by rw [← h6]; linarith
      · interval_cases k <;> norm_num

/-- The coefficients of the `q`-expansion of `E₄` are `1, 240 σ₃(m)`. -/
lemma E4_qcoeff (m : ℕ) :
    (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff m =
      if m = 0 then 1 else 240 * ((ArithmeticFunction.sigma 3 m : ℕ) : ℂ) := by
  rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl, Work.Modular.E4_qExpansion_coeff]

/-- The coefficients of the `q`-expansion of `E₆` are `1, -504 σ₅(m)`. -/
lemma E6_qcoeff (m : ℕ) :
    (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff m =
      if m = 0 then 1 else -504 * ((ArithmeticFunction.sigma 5 m : ℕ) : ℂ) := by
  rw [show Work.Kernels.E6Fun = Work.Modular.E6 from rfl, Work.Modular.E6_qExpansion_coeff]

/-- Tail bound for `E₄` after three terms: on `Im w ≥ 1`,
`E₄ w = 1 + 240 q + 2160 q² + O(‖q‖³)` with explicit constant `30000`. -/
theorem E4_third_order (w : ℍ) (hw : 1 ≤ w.im) :
    ‖Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w
        - 2160 * Work.Kernels.qParamFun w ^ 2‖
      ≤ 30000 * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
  have hper : Function.Periodic (Work.Kernels.E4Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E4Fun := ModularForm.holo' ModularForm.E₄
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty Work.Kernels.E4Fun :=
    ModularFormClass.bdd_at_infty ModularForm.E₄
  have hs := UpperHalfPlane.hasSum_qExpansion (h := 1) (f := Work.Kernels.E4Fun)
    one_pos hper hhol hbdd w
  have hs3 := (hasSum_nat_add_iff' 3).mpr hs
  have hq_eq : Function.Periodic.qParam 1 (w : ℂ) = Work.Kernels.qParamFun w := by
    simp [Function.Periodic.qParam, Work.Kernels.qParamFun]
  have hcoeff : ∀ m : ℕ, 3 ≤ m →
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff m‖ ≤ 240 * (m : ℝ) ^ 4 := by
    intro m hm
    have hm0 : m ≠ 0 := by omega
    rw [E4_qcoeff m, if_neg hm0, norm_mul]
    have hσ : (ArithmeticFunction.sigma 3 m : ℝ) ≤ (m : ℝ) ^ 4 := by
      have h' : ArithmeticFunction.sigma 3 m ≤ m ^ 4 := by
        simpa using ArithmeticFunction.sigma_le_pow_succ 3 m
      exact_mod_cast h'
    have h240 : ‖(240 : ℂ)‖ = (240 : ℝ) := by norm_num
    rw [h240, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hσ (by norm_num)
  have hc0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 0 = 1 := by
    rw [E4_qcoeff]; norm_num
  have hc1 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 1 = 240 := by
    rw [E4_qcoeff 1, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma_one]
  have hc2 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 2 = 2160 := by
    rw [E4_qcoeff 2, if_neg (by norm_num : (2 : ℕ) ≠ 0)]
    have hs2 : ArithmeticFunction.sigma 3 2 = 9 := by decide +kernel
    rw [hs2]; norm_num
  have hsum3 : (∑ i ∈ Finset.range 3, (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff i
        • Function.Periodic.qParam 1 (w : ℂ) ^ i)
      = 1 + 240 * Function.Periodic.qParam 1 (w : ℂ)
        + 2160 * Function.Periodic.qParam 1 (w : ℂ) ^ 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hc0, hc1, hc2]
    simp only [smul_eq_mul, pow_zero, pow_one, mul_one]
  rw [hsum3, hq_eq] at hs3
  have hr0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun w‖ := norm_nonneg _
  have hr : ‖Work.Kernels.qParamFun w‖ ≤ 1 / 512 := norm_qParamFun_le_inv512 w hw
  have hr3 : 3 * ‖Work.Kernels.qParamFun w‖ < 1 := by linarith
  -- termwise bound
  have hterm : ∀ n : ℕ,
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 3)
        • Work.Kernels.qParamFun w ^ (n + 3)‖
      ≤ (240 * 108 : ℝ) * ((3 * ‖Work.Kernels.qParamFun w‖) ^ n
          * ‖Work.Kernels.qParamFun w‖ ^ 3) := by
    intro n
    have hc := hcoeff (n + 3) (by omega)
    have h4 : (((n : ℝ) + 3)) ^ 4 ≤ 108 * 3 ^ n := by
      have h := pow_four_le_four_mul_three_pow (n + 3)
      have hcast : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
      rw [hcast] at h
      have h3 : (4 : ℝ) * 3 ^ (n + 3) = 108 * 3 ^ n := by rw [pow_add]; ring
      linarith [h, h3.le, h3.ge]
    have hc' : ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 3)‖
        ≤ 240 * (((n : ℝ) + 3) ^ 4) := by
      have hcast : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
      rw [hcast] at hc
      exact hc
    calc ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 3)
          • Work.Kernels.qParamFun w ^ (n + 3)‖
        = ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 3)‖
          * ‖Work.Kernels.qParamFun w‖ ^ (n + 3) := by rw [smul_eq_mul, norm_mul, norm_pow]
      _ ≤ (240 * (((n : ℝ) + 3) ^ 4)) * ‖Work.Kernels.qParamFun w‖ ^ (n + 3) :=
          mul_le_mul_of_nonneg_right hc' (by positivity)
      _ ≤ (240 * (108 * 3 ^ n)) * ‖Work.Kernels.qParamFun w‖ ^ (n + 3) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left h4 (by norm_num)
      _ = (240 * 108 : ℝ) * ((3 * ‖Work.Kernels.qParamFun w‖) ^ n
            * ‖Work.Kernels.qParamFun w‖ ^ 3) := by rw [pow_add, mul_pow]; ring
  have hgeo : Summable (fun n : ℕ => (3 * ‖Work.Kernels.qParamFun w‖) ^ n) :=
    summable_geometric_of_lt_one (by positivity) hr3
  have hmaj : Summable (fun n : ℕ => (240 * 108 : ℝ)
      * ((3 * ‖Work.Kernels.qParamFun w‖) ^ n * ‖Work.Kernels.qParamFun w‖ ^ 3)) :=
    (hgeo.mul_right _).mul_left _
  have hsumm : Summable (fun n : ℕ =>
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 3)
        • Work.Kernels.qParamFun w ^ (n + 3)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmaj
  have hkey : ‖Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w
        - 2160 * Work.Kernels.qParamFun w ^ 2‖
      = ‖∑' n : ℕ, (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 3)
          • Work.Kernels.qParamFun w ^ (n + 3)‖ := by
    rw [hs3.tsum_eq]
    congr 1
    ring
  rw [hkey]
  calc ‖∑' n : ℕ, (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 3)
        • Work.Kernels.qParamFun w ^ (n + 3)‖
      ≤ ∑' n : ℕ, ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 3)
        • Work.Kernels.qParamFun w ^ (n + 3)‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' n : ℕ, (240 * 108 : ℝ) * ((3 * ‖Work.Kernels.qParamFun w‖) ^ n
          * ‖Work.Kernels.qParamFun w‖ ^ 3) :=
        Summable.tsum_le_tsum hterm hsumm hmaj
    _ = (240 * 108 : ℝ) * (∑' n : ℕ, (3 * ‖Work.Kernels.qParamFun w‖) ^ n)
          * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
        rw [tsum_mul_left, tsum_mul_right]; ring
    _ = (240 * 108 : ℝ) * (1 - 3 * ‖Work.Kernels.qParamFun w‖)⁻¹
          * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
        rw [tsum_geometric_of_lt_one (by positivity) hr3]
    _ ≤ 30000 * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
        have hpos : 0 < 1 - 3 * ‖Work.Kernels.qParamFun w‖ := by linarith
        have hb : (240 * 108 : ℝ) * (1 - 3 * ‖Work.Kernels.qParamFun w‖)⁻¹ ≤ 30000 := by
          rw [mul_inv_le_iff₀ hpos]
          nlinarith [hr, hr0]
        have hpow : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun w‖ ^ 3 := by positivity
        exact mul_le_mul_of_nonneg_right hb hpow

/-- Tail bound for `E₆` after three terms: on `Im w ≥ 1`,
`E₆ w = 1 - 504 q - 16632 q² + O(‖q‖³)` with explicit constant `10^6`. -/
theorem E6_third_order (w : ℍ) (hw : 1 ≤ w.im) :
    ‖Work.Kernels.E6Fun w - 1 + 504 * Work.Kernels.qParamFun w
        + 16632 * Work.Kernels.qParamFun w ^ 2‖
      ≤ 1000000 * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
  have hper : Function.Periodic (Work.Kernels.E6Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E6Fun := ModularForm.holo' ModularForm.E₆
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty Work.Kernels.E6Fun :=
    ModularFormClass.bdd_at_infty ModularForm.E₆
  have hs := UpperHalfPlane.hasSum_qExpansion (h := 1) (f := Work.Kernels.E6Fun)
    one_pos hper hhol hbdd w
  have hs3 := (hasSum_nat_add_iff' 3).mpr hs
  have hq_eq : Function.Periodic.qParam 1 (w : ℂ) = Work.Kernels.qParamFun w := by
    simp [Function.Periodic.qParam, Work.Kernels.qParamFun]
  have hcoeff : ∀ m : ℕ, 3 ≤ m →
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff m‖ ≤ 504 * (m : ℝ) ^ 6 := by
    intro m hm
    have hm0 : m ≠ 0 := by omega
    rw [E6_qcoeff m, if_neg hm0, norm_mul]
    have hσ : (ArithmeticFunction.sigma 5 m : ℝ) ≤ (m : ℝ) ^ 6 := by
      have h' : ArithmeticFunction.sigma 5 m ≤ m ^ 6 := by
        simpa using ArithmeticFunction.sigma_le_pow_succ 5 m
      exact_mod_cast h'
    have h504 : ‖(-504 : ℂ)‖ = (504 : ℝ) := by norm_num
    rw [h504, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left hσ (by norm_num)
  have hc0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 0 = 1 := by
    rw [E6_qcoeff]; norm_num
  have hc1 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 1 = -504 := by
    rw [E6_qcoeff 1, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma_one]
  have hc2 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 2 = -16632 := by
    rw [E6_qcoeff 2, if_neg (by norm_num : (2 : ℕ) ≠ 0)]
    have hs2 : ArithmeticFunction.sigma 5 2 = 33 := by decide +kernel
    rw [hs2]; norm_num
  have hsum3 : (∑ i ∈ Finset.range 3, (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff i
        • Function.Periodic.qParam 1 (w : ℂ) ^ i)
      = 1 - 504 * Function.Periodic.qParam 1 (w : ℂ)
        - 16632 * Function.Periodic.qParam 1 (w : ℂ) ^ 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hc0, hc1, hc2]
    simp only [smul_eq_mul, pow_zero, pow_one, mul_one]
    ring
  rw [hsum3, hq_eq] at hs3
  have hr0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun w‖ := norm_nonneg _
  have hr : ‖Work.Kernels.qParamFun w‖ ≤ 1 / 512 := norm_qParamFun_le_inv512 w hw
  have hr4 : 4 * ‖Work.Kernels.qParamFun w‖ < 1 := by linarith
  have hterm : ∀ n : ℕ,
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 3)
        • Work.Kernels.qParamFun w ^ (n + 3)‖
      ≤ (504 * 1100 : ℝ) * ((4 * ‖Work.Kernels.qParamFun w‖) ^ n
          * ‖Work.Kernels.qParamFun w‖ ^ 3) := by
    intro n
    have hc := hcoeff (n + 3) (by omega)
    have h6 : (((n : ℝ) + 3)) ^ 6 ≤ 1100 * 4 ^ n := pow_six_shift n
    have hc' : ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 3)‖
        ≤ 504 * (((n : ℝ) + 3) ^ 6) := by
      have hcast : ((n + 3 : ℕ) : ℝ) = (n : ℝ) + 3 := by push_cast; ring
      rw [hcast] at hc
      exact hc
    calc ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 3)
          • Work.Kernels.qParamFun w ^ (n + 3)‖
        = ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 3)‖
          * ‖Work.Kernels.qParamFun w‖ ^ (n + 3) := by rw [smul_eq_mul, norm_mul, norm_pow]
      _ ≤ (504 * (((n : ℝ) + 3) ^ 6)) * ‖Work.Kernels.qParamFun w‖ ^ (n + 3) :=
          mul_le_mul_of_nonneg_right hc' (by positivity)
      _ ≤ (504 * (1100 * 4 ^ n)) * ‖Work.Kernels.qParamFun w‖ ^ (n + 3) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left h6 (by norm_num)
      _ = (504 * 1100 : ℝ) * ((4 * ‖Work.Kernels.qParamFun w‖) ^ n
            * ‖Work.Kernels.qParamFun w‖ ^ 3) := by rw [pow_add, mul_pow]; ring
  have hgeo : Summable (fun n : ℕ => (4 * ‖Work.Kernels.qParamFun w‖) ^ n) :=
    summable_geometric_of_lt_one (by positivity) hr4
  have hmaj : Summable (fun n : ℕ => (504 * 1100 : ℝ)
      * ((4 * ‖Work.Kernels.qParamFun w‖) ^ n * ‖Work.Kernels.qParamFun w‖ ^ 3)) :=
    (hgeo.mul_right _).mul_left _
  have hsumm : Summable (fun n : ℕ =>
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 3)
        • Work.Kernels.qParamFun w ^ (n + 3)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmaj
  have hkey : ‖Work.Kernels.E6Fun w - 1 + 504 * Work.Kernels.qParamFun w
        + 16632 * Work.Kernels.qParamFun w ^ 2‖
      = ‖∑' n : ℕ, (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 3)
          • Work.Kernels.qParamFun w ^ (n + 3)‖ := by
    rw [hs3.tsum_eq]
    congr 1
    ring
  rw [hkey]
  calc ‖∑' n : ℕ, (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 3)
        • Work.Kernels.qParamFun w ^ (n + 3)‖
      ≤ ∑' n : ℕ, ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff (n + 3)
        • Work.Kernels.qParamFun w ^ (n + 3)‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' n : ℕ, (504 * 1100 : ℝ) * ((4 * ‖Work.Kernels.qParamFun w‖) ^ n
          * ‖Work.Kernels.qParamFun w‖ ^ 3) :=
        Summable.tsum_le_tsum hterm hsumm hmaj
    _ = (504 * 1100 : ℝ) * (∑' n : ℕ, (4 * ‖Work.Kernels.qParamFun w‖) ^ n)
          * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
        rw [tsum_mul_left, tsum_mul_right]; ring
    _ = (504 * 1100 : ℝ) * (1 - 4 * ‖Work.Kernels.qParamFun w‖)⁻¹
          * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
        rw [tsum_geometric_of_lt_one (by positivity) hr4]
    _ ≤ 1000000 * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
        have hpos : 0 < 1 - 4 * ‖Work.Kernels.qParamFun w‖ := by linarith
        have hb : (504 * 1100 : ℝ) * (1 - 4 * ‖Work.Kernels.qParamFun w‖)⁻¹ ≤ 1000000 := by
          rw [mul_inv_le_iff₀ hpos]
          nlinarith [hr, hr0]
        have hpow : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun w‖ ^ 3 := by positivity
        exact mul_le_mul_of_nonneg_right hb hpow

/-! ## The three-term expansion of `Δ` -/

/-- On `Im w ≥ 1`, `Δ w = q - 24 q² + O(‖q‖³)` with explicit constant `10^5`. -/
theorem Delta_third_order (w : ℍ) (hw : 1 ≤ w.im) :
    ‖Work.Kernels.DeltaFun w - Work.Kernels.qParamFun w
        + 24 * Work.Kernels.qParamFun w ^ 2‖
      ≤ 100000 * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
  set q := Work.Kernels.qParamFun w with hq
  have hr0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg _
  have hr : ‖q‖ ≤ 1 / 512 := by rw [hq]; exact norm_qParamFun_le_inv512 w hw
  have h4 : ‖Work.Kernels.E4Fun w - 1 - 240 * q - 2160 * q ^ 2‖ ≤ 30000 * ‖q‖ ^ 3 := by
    rw [hq]; exact E4_third_order w hw
  have h6 : ‖Work.Kernels.E6Fun w - 1 + 504 * q + 16632 * q ^ 2‖ ≤ 1000000 * ‖q‖ ^ 3 := by
    rw [hq]; exact E6_third_order w hw
  have hD : Work.Kernels.DeltaFun w
      = (Work.Kernels.E4Fun w ^ 3 - Work.Kernels.E6Fun w ^ 2) / 1728 := by
    have h1 : Work.Kernels.DeltaFun w = ModularForm.discriminant w := by
      rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant]
    rw [h1, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  -- abbreviations
  have hPnorm : ‖(1 : ℂ) + 240 * q + 2160 * q ^ 2‖ ≤ (3 / 2 : ℝ) := by
    have h1 : ‖(1 : ℂ) + 240 * q + 2160 * q ^ 2‖ ≤ 1 + 240 * ‖q‖ + 2160 * ‖q‖ ^ 2 := by
      calc ‖(1 : ℂ) + 240 * q + 2160 * q ^ 2‖ ≤ ‖(1 : ℂ) + 240 * q‖ + ‖2160 * q ^ 2‖ :=
            norm_add_le _ _
        _ ≤ (‖(1 : ℂ)‖ + ‖240 * q‖) + ‖2160 * q ^ 2‖ := by
            linarith [norm_add_le (1 : ℂ) (240 * q)]
        _ = 1 + 240 * ‖q‖ + 2160 * ‖q‖ ^ 2 := by
            rw [norm_one, norm_mul, norm_mul, norm_pow]
            norm_num
    nlinarith [hr, hr0]
  have hQnorm : ‖(1 : ℂ) - 504 * q - 16632 * q ^ 2‖ ≤ (3 : ℝ) := by
    have h1 : ‖(1 : ℂ) - 504 * q - 16632 * q ^ 2‖ ≤ 1 + 504 * ‖q‖ + 16632 * ‖q‖ ^ 2 := by
      calc ‖(1 : ℂ) - 504 * q - 16632 * q ^ 2‖ ≤ ‖(1 : ℂ) - 504 * q‖ + ‖16632 * q ^ 2‖ :=
            norm_sub_le _ _
        _ ≤ (‖(1 : ℂ)‖ + ‖504 * q‖) + ‖16632 * q ^ 2‖ := by
            linarith [norm_sub_le (1 : ℂ) (504 * q)]
        _ = 1 + 504 * ‖q‖ + 16632 * ‖q‖ ^ 2 := by
            rw [norm_one, norm_mul, norm_mul, norm_pow]
            norm_num
    nlinarith [hr, hr0]
  have hunorm4 : ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ ≤ 30000 * ‖q‖ ^ 3 := by
    rw [show Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)
        = Work.Kernels.E4Fun w - 1 - 240 * q - 2160 * q ^ 2 by ring]
    exact h4
  have hunorm6 : ‖Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)‖ ≤ 1000000 * ‖q‖ ^ 3 := by
    rw [show Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)
        = Work.Kernels.E6Fun w - 1 + 504 * q + 16632 * q ^ 2 by ring]
    exact h6
  -- the `E₄³` remainder
  have hA : ‖Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q - 179280 * q ^ 2‖ ≤ 20000000 * ‖q‖ ^ 3 := by
    have hid : Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q - 179280 * q ^ 2
        = (3110400 * q ^ 3 + 13996800 * q ^ 4 + (240 * q + 2160 * q ^ 2) ^ 3)
          + (3 * (1 + 240 * q + 2160 * q ^ 2) ^ 2 * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2))
            + 3 * (1 + 240 * q + 2160 * q ^ 2) * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 2
            + (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 3) := by ring
    rw [hid]
    have h1 : ‖3110400 * q ^ 3 + 13996800 * q ^ 4 + (240 * q + 2160 * q ^ 2) ^ 3‖
        ≤ 17900000 * ‖q‖ ^ 3 := by
      have hw3 : ‖(240 * q + 2160 * q ^ 2) ^ 3‖ ≤ (245 : ℝ) ^ 3 * ‖q‖ ^ 3 := by
        rw [norm_pow]
        have hb : ‖240 * q + 2160 * q ^ 2‖ ≤ 245 * ‖q‖ := by
          calc ‖240 * q + 2160 * q ^ 2‖ ≤ ‖240 * q‖ + ‖2160 * q ^ 2‖ := norm_add_le _ _
            _ = 240 * ‖q‖ + 2160 * ‖q‖ ^ 2 := by rw [norm_mul, norm_mul, norm_pow]; norm_num
            _ ≤ 245 * ‖q‖ := by
                have : 2160 * ‖q‖ ^ 2 ≤ 5 * ‖q‖ := by
                  have h5 : ‖q‖ * ‖q‖ ≤ (1 / 512) * ‖q‖ :=
                    mul_le_mul_of_nonneg_right hr hr0
                  nlinarith
                linarith
        have hb0 : (0 : ℝ) ≤ ‖240 * q + 2160 * q ^ 2‖ := norm_nonneg _
        calc ‖240 * q + 2160 * q ^ 2‖ ^ 3 ≤ (245 * ‖q‖) ^ 3 :=
              pow_le_pow_left₀ hb0 hb 3
          _ = 245 ^ 3 * ‖q‖ ^ 3 := by rw [mul_pow]
      have hq3 : ‖q ^ 3‖ = ‖q‖ ^ 3 := norm_pow _ _
      have hq4 : ‖q ^ 4‖ = ‖q‖ ^ 4 := norm_pow _ _
      have h4b : ‖q‖ ^ 4 ≤ (1 / 512) * ‖q‖ ^ 3 := by
        have : ‖q‖ * ‖q‖ ^ 3 ≤ (1 / 512) * ‖q‖ ^ 3 := mul_le_mul_of_nonneg_right hr (by positivity)
        calc ‖q‖ ^ 4 = ‖q‖ * ‖q‖ ^ 3 := by ring
          _ ≤ (1 / 512) * ‖q‖ ^ 3 := this
      calc ‖3110400 * q ^ 3 + 13996800 * q ^ 4 + (240 * q + 2160 * q ^ 2) ^ 3‖
          ≤ ‖3110400 * q ^ 3 + 13996800 * q ^ 4‖ + ‖(240 * q + 2160 * q ^ 2) ^ 3‖ :=
            norm_add_le _ _
        _ ≤ (‖3110400 * q ^ 3‖ + ‖13996800 * q ^ 4‖) + (245 : ℝ) ^ 3 * ‖q‖ ^ 3 := by
            linarith [norm_add_le (3110400 * q ^ 3) (13996800 * q ^ 4), hw3]
        _ = (3110400 * ‖q‖ ^ 3 + 13996800 * ‖q‖ ^ 4) + 245 ^ 3 * ‖q‖ ^ 3 := by
            rw [norm_mul, norm_mul, hq3, hq4]; norm_num
        _ ≤ 17900000 * ‖q‖ ^ 3 := by
            have h2 : 13996800 * ‖q‖ ^ 4 ≤ 13996800 * ((1 / 512) * ‖q‖ ^ 3) :=
              mul_le_mul_of_nonneg_left h4b (by norm_num)
            have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
            nlinarith [h2, h3]
    have h2 : ‖3 * (1 + 240 * q + 2160 * q ^ 2) ^ 2 * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2))
        + 3 * (1 + 240 * q + 2160 * q ^ 2) * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 2
        + (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 3‖ ≤ 400000 * ‖q‖ ^ 3 := by
      have hP2 : ‖(1 + 240 * q + 2160 * q ^ 2) ^ 2‖ ≤ (3 / 2 : ℝ) ^ 2 := by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hPnorm 2
      have hP0 : (0 : ℝ) ≤ ‖(1 : ℂ) + 240 * q + 2160 * q ^ 2‖ := norm_nonneg _
      have hu4b : ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ ^ 2
          ≤ 30000 * ‖q‖ ^ 3 := by
        have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
        calc ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ ^ 2
            ≤ (30000 * ‖q‖ ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hunorm4 2
          _ = 900000000 * ‖q‖ ^ 6 := by ring
          _ ≤ 900000000 * ((1 / 512) ^ 3 * ‖q‖ ^ 3) := by
              have : ‖q‖ ^ 6 = ‖q‖ ^ 3 * ‖q‖ ^ 3 := by ring
              have hq3 : ‖q‖ ^ 3 ≤ (1 / 512) ^ 3 := pow_le_pow_left₀ hr0 hr 3
              nlinarith [hq3, h3]
          _ ≤ 30000 * ‖q‖ ^ 3 := by
              have h3' : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
              nlinarith [h3']
      have h3b : ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ ^ 3 ≤ 30000 * ‖q‖ ^ 3 := by
        have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
        have hsmall : ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ ≤ 1 := by
          calc _ ≤ 30000 * ‖q‖ ^ 3 := hunorm4
            _ ≤ 30000 * ((1 / 512) ^ 3 * 1) := by
                have hq3 : ‖q‖ ^ 3 ≤ (1 / 512) ^ 3 := pow_le_pow_left₀ hr0 hr 3
                nlinarith
            _ ≤ 1 := by norm_num
        calc ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ ^ 3
            = ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ ^ 2
              * ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ := by ring
          _ ≤ (30000 * ‖q‖ ^ 3) * 1 :=
              mul_le_mul hu4b hsmall (norm_nonneg _) (by positivity)
          _ = 30000 * ‖q‖ ^ 3 := by ring
      calc ‖3 * (1 + 240 * q + 2160 * q ^ 2) ^ 2 * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2))
          + 3 * (1 + 240 * q + 2160 * q ^ 2) * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 2
          + (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 3‖
          ≤ ‖3 * (1 + 240 * q + 2160 * q ^ 2) ^ 2 * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2))
              + 3 * (1 + 240 * q + 2160 * q ^ 2) * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 2‖
            + ‖(Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 3‖ := norm_add_le _ _
        _ ≤ (‖3 * (1 + 240 * q + 2160 * q ^ 2) ^ 2 * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2))‖
              + ‖3 * (1 + 240 * q + 2160 * q ^ 2) * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 2‖)
            + ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ ^ 3 := by
            have h := norm_add_le (3 * (1 + 240 * q + 2160 * q ^ 2) ^ 2 * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)))
              (3 * (1 + 240 * q + 2160 * q ^ 2) * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 2)
            rw [norm_pow] at *
            linarith
        _ ≤ 400000 * ‖q‖ ^ 3 := by
            have hterm1 : ‖3 * (1 + 240 * q + 2160 * q ^ 2) ^ 2 * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2))‖
                ≤ 3 * (3 / 2 : ℝ) ^ 2 * (30000 * ‖q‖ ^ 3) := by
              rw [norm_mul, norm_mul]
              have h3n : ‖(3 : ℂ)‖ = (3 : ℝ) := by norm_num
              rw [h3n]
              have hu0 : (0 : ℝ) ≤ ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ := norm_nonneg _
              have h3nn : (0 : ℝ) ≤ (3 : ℝ) := by norm_num
              calc 3 * ‖(1 + 240 * q + 2160 * q ^ 2) ^ 2‖ * ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖
                  ≤ 3 * (3 / 2 : ℝ) ^ 2 * (30000 * ‖q‖ ^ 3) := by
                    apply mul_le_mul (mul_le_mul_of_nonneg_left hP2 h3nn) hunorm4 hu0 (by positivity)
                _ = _ := rfl
            have hterm2 : ‖3 * (1 + 240 * q + 2160 * q ^ 2) * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 2‖
                ≤ 3 * (3 / 2 : ℝ) * (30000 * ‖q‖ ^ 3) := by
              rw [norm_mul, norm_mul, norm_pow]
              have h3n : ‖(3 : ℂ)‖ = (3 : ℝ) := by norm_num
              rw [h3n]
              apply mul_le_mul (mul_le_mul_of_nonneg_left hPnorm (by norm_num : (0:ℝ) ≤ 3)) hu4b (by positivity) (by positivity)
            have h3pow : ‖Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)‖ ^ 3 ≤ 30000 * ‖q‖ ^ 3 := h3b
            nlinarith [hterm1, hterm2, h3pow, hr0]
    calc ‖(3110400 * q ^ 3 + 13996800 * q ^ 4 + (240 * q + 2160 * q ^ 2) ^ 3)
          + (3 * (1 + 240 * q + 2160 * q ^ 2) ^ 2 * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2))
            + 3 * (1 + 240 * q + 2160 * q ^ 2) * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 2
            + (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 3)‖
        ≤ ‖3110400 * q ^ 3 + 13996800 * q ^ 4 + (240 * q + 2160 * q ^ 2) ^ 3‖
          + ‖3 * (1 + 240 * q + 2160 * q ^ 2) ^ 2 * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2))
            + 3 * (1 + 240 * q + 2160 * q ^ 2) * (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 2
            + (Work.Kernels.E4Fun w - (1 + 240 * q + 2160 * q ^ 2)) ^ 3‖ := norm_add_le _ _
      _ ≤ 17900000 * ‖q‖ ^ 3 + 400000 * ‖q‖ ^ 3 := add_le_add h1 h2
      _ ≤ 20000000 * ‖q‖ ^ 3 := by
          have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
          linarith
  -- the `E₆²` remainder
  have hB : ‖Work.Kernels.E6Fun w ^ 2 - 1 + 1008 * q - 220752 * q ^ 2‖ ≤ 30000000 * ‖q‖ ^ 3 := by
    have hid : Work.Kernels.E6Fun w ^ 2 - 1 + 1008 * q - 220752 * q ^ 2
        = (16765056 * q ^ 3 + 276623424 * q ^ 4)
          + (2 * (1 - 504 * q - 16632 * q ^ 2) * (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2))
            + (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)) ^ 2) := by ring
    rw [hid]
    have h1 : ‖16765056 * q ^ 3 + 276623424 * q ^ 4‖ ≤ 17400000 * ‖q‖ ^ 3 := by
      have hq3 : ‖q ^ 3‖ = ‖q‖ ^ 3 := norm_pow _ _
      have hq4 : ‖q‖ ^ 4 ≤ (1 / 512) * ‖q‖ ^ 3 := by
        have : ‖q‖ * ‖q‖ ^ 3 ≤ (1 / 512) * ‖q‖ ^ 3 := mul_le_mul_of_nonneg_right hr (by positivity)
        calc ‖q‖ ^ 4 = ‖q‖ * ‖q‖ ^ 3 := by ring
          _ ≤ (1 / 512) * ‖q‖ ^ 3 := this
      calc ‖16765056 * q ^ 3 + 276623424 * q ^ 4‖
          ≤ ‖16765056 * q ^ 3‖ + ‖276623424 * q ^ 4‖ := norm_add_le _ _
        _ = 16765056 * ‖q‖ ^ 3 + 276623424 * ‖q‖ ^ 4 := by
            rw [norm_mul, norm_mul, norm_pow, norm_pow]
            norm_num
        _ ≤ 17400000 * ‖q‖ ^ 3 := by
            have h2 : 276623424 * ‖q‖ ^ 4 ≤ 276623424 * ((1 / 512) * ‖q‖ ^ 3) :=
              mul_le_mul_of_nonneg_left hq4 (by norm_num)
            have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
            nlinarith [h2, h3]
    have h2 : ‖2 * (1 - 504 * q - 16632 * q ^ 2) * (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2))
        + (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)) ^ 2‖ ≤ 8000000 * ‖q‖ ^ 3 := by
      have hv2 : ‖Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)‖ ^ 2 ≤ 1000000 * ‖q‖ ^ 3 := by
        have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
        calc ‖Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)‖ ^ 2
            ≤ (1000000 * ‖q‖ ^ 3) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hunorm6 2
          _ = 1000000000000 * ‖q‖ ^ 6 := by ring
          _ ≤ 1000000000000 * ((1 / 512) ^ 3 * ‖q‖ ^ 3) := by
              have : ‖q‖ ^ 6 = ‖q‖ ^ 3 * ‖q‖ ^ 3 := by ring
              have hq3 : ‖q‖ ^ 3 ≤ (1 / 512) ^ 3 := pow_le_pow_left₀ hr0 hr 3
              nlinarith [hq3, h3]
          _ ≤ 1000000 * ‖q‖ ^ 3 := by
              have h3' : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
              nlinarith [h3']
      calc ‖2 * (1 - 504 * q - 16632 * q ^ 2) * (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2))
          + (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)) ^ 2‖
          ≤ ‖2 * (1 - 504 * q - 16632 * q ^ 2) * (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2))‖
            + ‖(Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)) ^ 2‖ := norm_add_le _ _
        _ = 2 * ‖(1 - 504 * q - 16632 * q ^ 2)‖ * ‖Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)‖
            + ‖Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)‖ ^ 2 := by
            rw [norm_mul, norm_mul, norm_pow]
            norm_num
        _ ≤ 2 * 3 * (1000000 * ‖q‖ ^ 3) + 1000000 * ‖q‖ ^ 3 := by
            have hv0 : (0 : ℝ) ≤ ‖Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)‖ := norm_nonneg _
            have h2 : 2 * ‖(1 - 504 * q - 16632 * q ^ 2)‖ ≤ 2 * 3 := by linarith [hQnorm]
            have h3 : 2 * ‖(1 - 504 * q - 16632 * q ^ 2)‖ * ‖Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)‖
                ≤ 6 * (1000000 * ‖q‖ ^ 3) := by
              calc _ ≤ (2 * 3) * (1000000 * ‖q‖ ^ 3) := by
                    apply mul_le_mul h2 hunorm6 hv0 (by norm_num)
                _ = 6 * (1000000 * ‖q‖ ^ 3) := by ring
            linarith [h3, hv2]
        _ ≤ 8000000 * ‖q‖ ^ 3 := by
            have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
            nlinarith [h3]
    calc ‖(16765056 * q ^ 3 + 276623424 * q ^ 4)
          + (2 * (1 - 504 * q - 16632 * q ^ 2) * (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2))
            + (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)) ^ 2)‖
        ≤ ‖16765056 * q ^ 3 + 276623424 * q ^ 4‖
          + ‖2 * (1 - 504 * q - 16632 * q ^ 2) * (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2))
            + (Work.Kernels.E6Fun w - (1 - 504 * q - 16632 * q ^ 2)) ^ 2‖ := norm_add_le _ _
      _ ≤ 17400000 * ‖q‖ ^ 3 + 8000000 * ‖q‖ ^ 3 := add_le_add h1 h2
      _ ≤ 30000000 * ‖q‖ ^ 3 := by
          have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
          linarith
  -- conclusion
  have hkey : (Work.Kernels.E4Fun w ^ 3 - Work.Kernels.E6Fun w ^ 2) / 1728 - q + 24 * q ^ 2
      = ((Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q - 179280 * q ^ 2)
          - (Work.Kernels.E6Fun w ^ 2 - 1 + 1008 * q - 220752 * q ^ 2)) / 1728 := by ring
  have hnum : ‖(Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q - 179280 * q ^ 2)
      - (Work.Kernels.E6Fun w ^ 2 - 1 + 1008 * q - 220752 * q ^ 2)‖
      ≤ 50000000 * ‖q‖ ^ 3 := by
    calc _ ≤ ‖Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q - 179280 * q ^ 2‖
          + ‖Work.Kernels.E6Fun w ^ 2 - 1 + 1008 * q - 220752 * q ^ 2‖ := norm_sub_le _ _
      _ ≤ 20000000 * ‖q‖ ^ 3 + 30000000 * ‖q‖ ^ 3 := add_le_add hA hB
      _ = 50000000 * ‖q‖ ^ 3 := by ring
  rw [hD, hkey, norm_div, Complex.norm_ofNat]
  have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
  calc ‖(Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q - 179280 * q ^ 2)
        - (Work.Kernels.E6Fun w ^ 2 - 1 + 1008 * q - 220752 * q ^ 2)‖ / 1728
      ≤ (50000000 * ‖q‖ ^ 3) / 1728 := by
        exact div_le_div_of_nonneg_right hnum (by norm_num)
    _ ≤ 100000 * ‖q‖ ^ 3 := by linarith

/-! ## The main pointwise bound `‖j - q⁻¹ - 744‖ ≤ 10^7 ‖q‖` on `Im ≥ 1` -/

/-- Elementary power comparison: if `0 ≤ r ≤ c` then `r ^ (n+1) ≤ c * r ^ n`. -/
lemma pow_succ_le_mul {r c : ℝ} (h0 : 0 ≤ r) (h : r ≤ c) (n : ℕ) :
    r ^ (n + 1) ≤ c * r ^ n := by
  rw [pow_succ]
  calc r ^ n * r ≤ r ^ n * c := mul_le_mul_of_nonneg_left h (pow_nonneg h0 n)
    _ = c * r ^ n := by ring

/-- Second-order expansion of `E₄` with explicit constant: on `Im w ≥ 1`,
`E₄ w = 1 + 240 q + O(‖q‖²)`. -/
lemma E4_second_order_explicit (w : ℍ) (hw : 1 ≤ w.im) :
    ‖Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w‖
      ≤ 2300 * ‖Work.Kernels.qParamFun w‖ ^ 2 := by
  have h := E4_third_order w hw
  have hr : ‖Work.Kernels.qParamFun w‖ ≤ 1 / 512 := norm_qParamFun_le_inv512 w hw
  have hr0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun w‖ := norm_nonneg _
  have hid : Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w
      = 2160 * Work.Kernels.qParamFun w ^ 2
        + (Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w
            - 2160 * Work.Kernels.qParamFun w ^ 2) := by ring
  rw [hid]
  have h2160 : ‖(2160 : ℂ) * Work.Kernels.qParamFun w ^ 2‖
      = 2160 * ‖Work.Kernels.qParamFun w‖ ^ 2 := by
    rw [norm_mul, norm_pow]; norm_num
  calc ‖2160 * Work.Kernels.qParamFun w ^ 2
        + (Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w
            - 2160 * Work.Kernels.qParamFun w ^ 2)‖
      ≤ ‖2160 * Work.Kernels.qParamFun w ^ 2‖
        + ‖Work.Kernels.E4Fun w - 1 - 240 * Work.Kernels.qParamFun w
            - 2160 * Work.Kernels.qParamFun w ^ 2‖ := norm_add_le _ _
    _ ≤ 2160 * ‖Work.Kernels.qParamFun w‖ ^ 2 + 30000 * ‖Work.Kernels.qParamFun w‖ ^ 3 := by
        rw [h2160]; linarith [h]
    _ ≤ 2300 * ‖Work.Kernels.qParamFun w‖ ^ 2 := by
        have h3 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun w‖ ^ 2 := by positivity
        have h6 : ‖Work.Kernels.qParamFun w‖ ^ 3 ≤ (1 / 512) * ‖Work.Kernels.qParamFun w‖ ^ 2 :=
          pow_succ_le_mul hr0 hr 2
        nlinarith [h3, h6]

/-- Third-order expansion of the cube: on `Im w ≥ 1`, `E₄ w³ - 1 - 720 q = O(‖q‖²)`. -/
lemma E4_cube_bound (w : ℍ) (hw : 1 ≤ w.im) :
    ‖Work.Kernels.E4Fun w ^ 3 - 1 - 720 * Work.Kernels.qParamFun w‖
      ≤ 300000 * ‖Work.Kernels.qParamFun w‖ ^ 2 := by
  set q := Work.Kernels.qParamFun w with hq
  have hr : ‖q‖ ≤ 1 / 512 := by rw [hq]; exact norm_qParamFun_le_inv512 w hw
  have hr0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg _
  have h2 : ‖Work.Kernels.E4Fun w - (1 + 240 * q)‖ ≤ 2300 * ‖q‖ ^ 2 := by
    rw [show Work.Kernels.E4Fun w - (1 + 240 * q)
        = Work.Kernels.E4Fun w - 1 - 240 * q by ring]
    rw [hq]; exact E4_second_order_explicit w hw
  have hid : Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q
      = 3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) + 172800 * q ^ 2
        + 1440 * q * (Work.Kernels.E4Fun w - (1 + 240 * q))
        + 3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) ^ 2
        + (240 * q + (Work.Kernels.E4Fun w - (1 + 240 * q))) ^ 3 := by ring
  rw [hid]
  -- individual bounds
  have hq2 : ‖q ^ 2‖ = ‖q‖ ^ 2 := norm_pow _ _
  have hq3 : ‖q ^ 3‖ = ‖q‖ ^ 3 := norm_pow _ _
  have h2sq : ‖Work.Kernels.E4Fun w - (1 + 240 * q)‖ ^ 2 ≤ 11000 * ‖q‖ ^ 3 := by
    have h3 : (0 : ℝ) ≤ ‖q‖ ^ 3 := by positivity
    calc ‖Work.Kernels.E4Fun w - (1 + 240 * q)‖ ^ 2 ≤ (2300 * ‖q‖ ^ 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ = 5290000 * ‖q‖ ^ 4 := by ring
      _ ≤ 5290000 * ((1 / 512) * ‖q‖ ^ 3) :=
          mul_le_mul_of_nonneg_left (pow_succ_le_mul hr0 hr 3) (by norm_num)
      _ ≤ 11000 * ‖q‖ ^ 3 := by nlinarith [h3]
  have hsum_w : ‖240 * q + (Work.Kernels.E4Fun w - (1 + 240 * q))‖ ≤ 245 * ‖q‖ := by
    have hb : ‖240 * q + (Work.Kernels.E4Fun w - (1 + 240 * q))‖
        ≤ 240 * ‖q‖ + 2300 * ‖q‖ ^ 2 := by
      calc ‖240 * q + (Work.Kernels.E4Fun w - (1 + 240 * q))‖
          ≤ ‖240 * q‖ + ‖Work.Kernels.E4Fun w - (1 + 240 * q)‖ := norm_add_le _ _
        _ ≤ 240 * ‖q‖ + 2300 * ‖q‖ ^ 2 := by
            have h240 : ‖240 * q‖ = 240 * ‖q‖ := by rw [norm_mul]; norm_num
            rw [h240]; linarith [h2]
    have h5 : 2300 * ‖q‖ ^ 2 ≤ 5 * ‖q‖ := by
      have h6 : ‖q‖ ^ 2 ≤ (1 / 512) * ‖q‖ := by
        simpa using pow_succ_le_mul hr0 hr 1
      linarith [mul_le_mul_of_nonneg_left h6 (by norm_num : (0 : ℝ) ≤ 2300), hr0]
    linarith
  have hcu : ‖(240 * q + (Work.Kernels.E4Fun w - (1 + 240 * q))) ^ 3‖ ≤ 245 ^ 3 * ‖q‖ ^ 3 := by
    rw [norm_pow]
    calc ‖240 * q + (Work.Kernels.E4Fun w - (1 + 240 * q))‖ ^ 3 ≤ (245 * ‖q‖) ^ 3 :=
          pow_le_pow_left₀ (norm_nonneg _) hsum_w 3
      _ = 245 ^ 3 * ‖q‖ ^ 3 := by rw [mul_pow]
  calc ‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) + 172800 * q ^ 2
        + 1440 * q * (Work.Kernels.E4Fun w - (1 + 240 * q))
        + 3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) ^ 2
        + (240 * q + (Work.Kernels.E4Fun w - (1 + 240 * q))) ^ 3‖
      ≤ ‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) + 172800 * q ^ 2
          + 1440 * q * (Work.Kernels.E4Fun w - (1 + 240 * q))
          + 3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) ^ 2‖
        + ‖(240 * q + (Work.Kernels.E4Fun w - (1 + 240 * q))) ^ 3‖ := norm_add_le _ _
    _ ≤ (‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) + 172800 * q ^ 2
          + 1440 * q * (Work.Kernels.E4Fun w - (1 + 240 * q))‖
          + ‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) ^ 2‖) + 245 ^ 3 * ‖q‖ ^ 3 := by
        linarith [norm_add_le (3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) + 172800 * q ^ 2
          + 1440 * q * (Work.Kernels.E4Fun w - (1 + 240 * q)))
          (3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) ^ 2), hcu]
    _ ≤ ((‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) + 172800 * q ^ 2‖
          + ‖1440 * q * (Work.Kernels.E4Fun w - (1 + 240 * q))‖)
          + ‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) ^ 2‖) + 245 ^ 3 * ‖q‖ ^ 3 := by
        linarith [norm_add_le (3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) + 172800 * q ^ 2)
          (1440 * q * (Work.Kernels.E4Fun w - (1 + 240 * q)))]
    _ ≤ (((‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q))‖ + ‖172800 * q ^ 2‖)
          + ‖1440 * q * (Work.Kernels.E4Fun w - (1 + 240 * q))‖)
          + ‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) ^ 2‖) + 245 ^ 3 * ‖q‖ ^ 3 := by
        linarith [norm_add_le (3 * (Work.Kernels.E4Fun w - (1 + 240 * q))) (172800 * q ^ 2)]
    _ ≤ (((3 * (2300 * ‖q‖ ^ 2) + 172800 * ‖q‖ ^ 2)
          + 1440 * (‖q‖ * (2300 * ‖q‖ ^ 2)))
          + 3 * (11000 * ‖q‖ ^ 3)) + 245 ^ 3 * ‖q‖ ^ 3 := by
        have h3n : ‖(3 : ℂ)‖ = (3 : ℝ) := by norm_num
        have h1440 : ‖(1440 : ℂ)‖ = (1440 : ℝ) := by norm_num
        have h172800 : ‖(172800 : ℂ)‖ = (172800 : ℝ) := by norm_num
        have hA : ‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q))‖ ≤ 3 * (2300 * ‖q‖ ^ 2) := by
          rw [norm_mul, h3n]
          exact mul_le_mul_of_nonneg_left h2 (by norm_num)
        have hB : ‖172800 * q ^ 2‖ = 172800 * ‖q‖ ^ 2 := by rw [norm_mul, hq2, h172800]
        have hC : ‖1440 * q * (Work.Kernels.E4Fun w - (1 + 240 * q))‖
            ≤ 1440 * (‖q‖ * (2300 * ‖q‖ ^ 2)) := by
          rw [norm_mul, norm_mul, h1440]
          rw [show (1440 : ℝ) * (‖q‖ * (2300 * ‖q‖ ^ 2)) = (1440 * ‖q‖) * (2300 * ‖q‖ ^ 2) by ring]
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
        have hD : ‖3 * (Work.Kernels.E4Fun w - (1 + 240 * q)) ^ 2‖
            ≤ 3 * (11000 * ‖q‖ ^ 3) := by
          rw [norm_mul, h3n, norm_pow]
          exact mul_le_mul_of_nonneg_left h2sq (by norm_num)
        linarith [hA, hB, hC, hD]
    _ ≤ 300000 * ‖q‖ ^ 2 := by
        have h3 : (0 : ℝ) ≤ ‖q‖ ^ 2 := by positivity
        have h6 : ‖q‖ ^ 3 ≤ (1 / 512) * ‖q‖ ^ 2 := pow_succ_le_mul hr0 hr 2
        nlinarith [h3, h6]

/-- **The second-order cusp expansion of `j` on `Im ≥ 1`, with an explicit constant.**
`‖j w - q⁻¹ - 744‖ ≤ 10^7 ‖q w‖` for `Im w ≥ 1`. -/
theorem E_j_pointwise_Im_one (w : ℍ) (hw : 1 ≤ w.im) :
    ‖Work.Kernels.jInvariantFun w - (Work.Kernels.qParamFun w)⁻¹ - 744‖
      ≤ 10 ^ 7 * ‖Work.Kernels.qParamFun w‖ := by
  set q := Work.Kernels.qParamFun w with hq
  have hr : ‖q‖ ≤ 1 / 512 := by rw [hq]; exact norm_qParamFun_le_inv512 w hw
  have hr0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg _
  have hq0 : q ≠ 0 := by rw [hq]; exact qParamFun_ne_zero w
  have hΔne : Work.Kernels.DeltaFun w ≠ 0 := by
    simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero w
  have hΔ : ‖Work.Kernels.DeltaFun w - q + 24 * q ^ 2‖ ≤ 100000 * ‖q‖ ^ 3 := by
    rw [hq]; exact Delta_third_order w hw
  have hcube : ‖Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q‖ ≤ 300000 * ‖q‖ ^ 2 := by
    rw [hq]; exact E4_cube_bound w hw
  -- the numerator `E₄³ - Δ (q⁻¹ + 744)`
  have hnum : ‖Work.Kernels.E4Fun w ^ 3 - Work.Kernels.DeltaFun w * (q⁻¹ + 744)‖
      ≤ 600000 * ‖q‖ ^ 2 := by
    have hid : Work.Kernels.E4Fun w ^ 3 - Work.Kernels.DeltaFun w * (q⁻¹ + 744)
        = (Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q)
          - (Work.Kernels.DeltaFun w - q + 24 * q ^ 2) * q⁻¹
          - 744 * (Work.Kernels.DeltaFun w - q + 24 * q ^ 2) + 17856 * q ^ 2 := by
      field_simp
      ring
    rw [hid]
    have heq : ‖(Work.Kernels.DeltaFun w - q + 24 * q ^ 2) * q⁻¹‖ ≤ 100000 * ‖q‖ ^ 2 := by
      rw [norm_mul, norm_inv]
      calc ‖Work.Kernels.DeltaFun w - q + 24 * q ^ 2‖ * ‖q‖⁻¹
          ≤ (100000 * ‖q‖ ^ 3) * ‖q‖⁻¹ := mul_le_mul_of_nonneg_right hΔ (by positivity)
        _ = 100000 * ‖q‖ ^ 2 := by
            have hc : ‖q‖ ^ 3 * ‖q‖⁻¹ = ‖q‖ ^ 2 := by
              rw [show ‖q‖ ^ 3 = ‖q‖ ^ 2 * ‖q‖ by ring, mul_assoc,
                mul_inv_cancel₀ (norm_ne_zero_iff.mpr hq0), mul_one]
            calc (100000 * ‖q‖ ^ 3) * ‖q‖⁻¹ = 100000 * (‖q‖ ^ 3 * ‖q‖⁻¹) := by ring
              _ = 100000 * ‖q‖ ^ 2 := by rw [hc]
    have he7 : ‖744 * (Work.Kernels.DeltaFun w - q + 24 * q ^ 2)‖ ≤ 145500 * ‖q‖ ^ 2 := by
      rw [norm_mul]
      have h744 : ‖(744 : ℂ)‖ = (744 : ℝ) := by norm_num
      rw [h744]
      have h6 : ‖q‖ ^ 3 ≤ (1 / 512) * ‖q‖ ^ 2 := pow_succ_le_mul hr0 hr 2
      calc 744 * ‖Work.Kernels.DeltaFun w - q + 24 * q ^ 2‖
          ≤ 744 * (100000 * ‖q‖ ^ 3) := mul_le_mul_of_nonneg_left hΔ (by norm_num)
        _ ≤ 145500 * ‖q‖ ^ 2 := by nlinarith [h6]
    have h18 : ‖17856 * q ^ 2‖ = 17856 * ‖q‖ ^ 2 := by
      rw [norm_mul, norm_pow]; norm_num
    have hstep1 : ‖(Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q)
          - (Work.Kernels.DeltaFun w - q + 24 * q ^ 2) * q⁻¹
          - 744 * (Work.Kernels.DeltaFun w - q + 24 * q ^ 2)‖
        ≤ 300000 * ‖q‖ ^ 2 + 100000 * ‖q‖ ^ 2 + 145500 * ‖q‖ ^ 2 := by
      calc _ ≤ ‖(Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q)
            - (Work.Kernels.DeltaFun w - q + 24 * q ^ 2) * q⁻¹‖
            + ‖744 * (Work.Kernels.DeltaFun w - q + 24 * q ^ 2)‖ := norm_sub_le _ _
        _ ≤ (‖Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q‖
            + ‖(Work.Kernels.DeltaFun w - q + 24 * q ^ 2) * q⁻¹‖) + 145500 * ‖q‖ ^ 2 := by
            linarith [norm_sub_le (Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q)
              ((Work.Kernels.DeltaFun w - q + 24 * q ^ 2) * q⁻¹), he7]
        _ ≤ _ := by linarith [hcube, heq]
    calc ‖(Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q)
          - (Work.Kernels.DeltaFun w - q + 24 * q ^ 2) * q⁻¹
          - 744 * (Work.Kernels.DeltaFun w - q + 24 * q ^ 2) + 17856 * q ^ 2‖
        ≤ ‖(Work.Kernels.E4Fun w ^ 3 - 1 - 720 * q)
          - (Work.Kernels.DeltaFun w - q + 24 * q ^ 2) * q⁻¹
          - 744 * (Work.Kernels.DeltaFun w - q + 24 * q ^ 2)‖ + ‖17856 * q ^ 2‖ :=
          norm_add_le _ _
      _ ≤ (300000 * ‖q‖ ^ 2 + 100000 * ‖q‖ ^ 2 + 145500 * ‖q‖ ^ 2) + 17856 * ‖q‖ ^ 2 := by
          rw [h18]; linarith [hstep1]
      _ ≤ 600000 * ‖q‖ ^ 2 := by
          have h3 : (0 : ℝ) ≤ ‖q‖ ^ 2 := by positivity
          linarith
  have hden : (1 / 2 : ℝ) * ‖q‖ ≤ ‖Work.Kernels.DeltaFun w‖ := by
    have h6 : ‖q‖ ^ 3 ≤ (1 / 512) * ‖q‖ ^ 2 := pow_succ_le_mul hr0 hr 2
    have h7 : ‖Work.Kernels.DeltaFun w - q‖ ≤ (1 / 2 : ℝ) * ‖q‖ := by
      have h24 : ‖24 * q ^ 2‖ = 24 * ‖q‖ ^ 2 := by rw [norm_mul, norm_pow]; norm_num
      calc ‖Work.Kernels.DeltaFun w - q‖
          ≤ ‖Work.Kernels.DeltaFun w - q + 24 * q ^ 2‖ + ‖24 * q ^ 2‖ := by
            have h := norm_add_le (Work.Kernels.DeltaFun w - q + 24 * q ^ 2) (-(24 * q ^ 2))
            have he : Work.Kernels.DeltaFun w - q + 24 * q ^ 2 + -(24 * q ^ 2)
                = Work.Kernels.DeltaFun w - q := by ring
            rw [he, norm_neg] at h
            exact h
        _ ≤ 100000 * ‖q‖ ^ 3 + 24 * ‖q‖ ^ 2 := by rw [h24]; linarith [hΔ]
        _ ≤ (1 / 2 : ℝ) * ‖q‖ := by
            have h3 : (0 : ℝ) ≤ ‖q‖ ^ 2 := by positivity
            nlinarith [h6, h3]
    have h2 : ‖q‖ - ‖Work.Kernels.DeltaFun w - q‖ ≤ ‖Work.Kernels.DeltaFun w‖ := by
      have h3 := norm_sub_le (Work.Kernels.DeltaFun w) (Work.Kernels.DeltaFun w - q)
      have he : Work.Kernels.DeltaFun w - (Work.Kernels.DeltaFun w - q) = q := by ring
      rw [he] at h3
      linarith
    linarith
  have hj : Work.Kernels.jInvariantFun w - q⁻¹ - 744
      = (Work.Kernels.E4Fun w ^ 3 - Work.Kernels.DeltaFun w * (q⁻¹ + 744))
        / Work.Kernels.DeltaFun w := by
    rw [Work.Kernels.jInvariantFun]
    field_simp
    ring
  have hΔpos : 0 < ‖Work.Kernels.DeltaFun w‖ := norm_pos_iff.mpr hΔne
  have hqpos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  rw [hj]
  calc ‖(Work.Kernels.E4Fun w ^ 3 - Work.Kernels.DeltaFun w * (q⁻¹ + 744))
        / Work.Kernels.DeltaFun w‖
      = ‖Work.Kernels.E4Fun w ^ 3 - Work.Kernels.DeltaFun w * (q⁻¹ + 744)‖
        / ‖Work.Kernels.DeltaFun w‖ := norm_div _ _
    _ ≤ (600000 * ‖q‖ ^ 2) / ((1 / 2 : ℝ) * ‖q‖) :=
        div_le_div₀ (by positivity) hnum (by positivity) hden
    _ = 1200000 * ‖q‖ := by
        field_simp
        ring
    _ ≤ 10 ^ 7 * ‖q‖ := by nlinarith [hr0]

/-! ## The lift of `F = j - q⁻¹ - 744` and its mean-value bound -/

/-- The lift of `F w = j w - q w⁻¹ - 744` to the upper half plane (as a function on `ℂ`). -/
def F_lift (z : ℂ) : ℂ :=
  Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)
    - (Work.Kernels.qParamFun (UpperHalfPlane.ofComplex z))⁻¹ - 744

lemma F_lift_eq (z : ℂ) :
    F_lift z = Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex z)
      - (Work.Kernels.qParamFun (UpperHalfPlane.ofComplex z))⁻¹ - 744 := rfl

lemma coe_ofComplex (z : ℂ) (hz : 0 < z.im) :
    ((UpperHalfPlane.ofComplex z : ℍ) : ℂ) = z := by
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz, UpperHalfPlane.coe_mk]

/-- `F_lift` satisfies the pointwise bound of `E_j_pointwise_Im_one`. -/
lemma F_lift_bound (z : ℂ) (hz : 1 ≤ z.im) :
    ‖F_lift z‖ ≤ 10 ^ 7 * Real.exp (-(2 * Real.pi * z.im)) := by
  have hpos : 0 < z.im := by linarith
  have hcoe := coe_ofComplex z hpos
  have him : 1 ≤ (UpperHalfPlane.ofComplex z).im := by
    rw [← UpperHalfPlane.coe_im, hcoe]; exact hz
  have h := E_j_pointwise_Im_one (UpperHalfPlane.ofComplex z) him
  have hq : ‖Work.Kernels.qParamFun (UpperHalfPlane.ofComplex z)‖
      = Real.exp (-(2 * Real.pi * z.im)) := by
    rw [norm_qParamFun_eq, ← UpperHalfPlane.coe_im, hcoe]
  rw [hq] at h
  rw [F_lift_eq]
  exact h

/-- `F_lift` is complex differentiable on the upper half plane. -/
lemma F_lift_differentiableOn :
    DifferentiableOn ℂ F_lift {z : ℂ | 0 < z.im} := by
  have hΔ : Work.Kernels.DeltaFun = ⇑CuspForm.discriminant := rfl
  have hDne : ∀ w : ℍ, Work.Kernels.DeltaFun w ≠ 0 := fun w => by
    rw [hΔ]; exact ModularForm.discriminant_ne_zero w
  have hj : MDiff Work.Kernels.jInvariantFun :=
    ((ModularFormClass.holo ModularForm.E₄).pow 3).div
      (CuspFormClass.holo CuspForm.discriminant) hDne
  have hq : MDiff (fun w : ℍ => (Work.Kernels.qParamFun w)⁻¹) := by
    have h1 : MDiff Work.Kernels.qParamFun := by
      rw [UpperHalfPlane.mdifferentiable_iff]
      have hg : DifferentiableOn ℂ
          (fun z : ℂ => Complex.exp (2 * Real.pi * Complex.I * z)) {z : ℂ | 0 < z.im} :=
        (by fun_prop : Differentiable ℂ
          (fun z : ℂ => Complex.exp (2 * Real.pi * Complex.I * z))).differentiableOn
      refine hg.congr (fun z hz => ?_)
      rw [Function.comp_apply, Work.Kernels.qParamFun, coe_ofComplex z hz]
    exact h1.inv fun w => qParamFun_ne_zero w
  have hF : MDiff (fun w : ℍ => Work.Kernels.jInvariantFun w
      - (Work.Kernels.qParamFun w)⁻¹ - 744) :=
    (hj.sub hq).sub mdifferentiable_const
  have := (UpperHalfPlane.mdifferentiable_iff).mp hF
  exact this

/-- The closed ball of radius `1/2` about a point of `Im ≥ 3/2` stays in `Im ≥ 1 > 0`. -/
lemma closedBall_subset_im_pos (z : ℂ) (hz : 3 / 2 ≤ z.im) :
    closure (Metric.ball z (1 / 2)) ⊆ {w : ℂ | 0 < w.im} := by
  intro w hw
  have hw' : w ∈ Metric.closedBall z (1 / 2) := Metric.closure_ball_subset_closedBall hw
  rw [Metric.mem_closedBall, Complex.dist_eq] at hw'
  have h2 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
  have h4 : -((w - z).im) ≤ ‖w - z‖ := le_trans (neg_le_abs _) h2
  rw [Complex.sub_im] at h4
  have : (0 : ℝ) < w.im := by linarith
  simpa using this

/-- **Cauchy's estimate for the derivative of the lift** (radius `1/2`). -/
lemma F_lift_deriv_bound (z : ℂ) (hz : 3 / 2 ≤ z.im) :
    ‖deriv F_lift z‖ ≤ 2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * z.im)) := by
  have hR : (0 : ℝ) < 1 / 2 := by norm_num
  have hsub : Metric.ball z (1 / 2) ⊆ {w : ℂ | 0 < w.im} :=
    subset_closure.trans (closedBall_subset_im_pos z hz)
  have hdiff : DiffContOnCl ℂ F_lift (Metric.ball z (1 / 2)) :=
    ⟨F_lift_differentiableOn.mono hsub,
      F_lift_differentiableOn.continuousOn.mono (closedBall_subset_im_pos z hz)⟩
  have hexpπ : Real.exp Real.pi ≤ 55 := by
    have h1 : Real.exp Real.pi ≤ Real.exp 4 := Real.exp_le_exp.mpr (le_of_lt Real.pi_lt_four)
    have h2 : Real.exp 4 = (Real.exp 1) ^ 4 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h2] at h1
    have h3 : (2.7182818286 : ℝ) ^ 4 ≤ 55 := by norm_num
    have h4 : (Real.exp 1) ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
      pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_d9) 4
    linarith
  have hsp : ∀ w ∈ Metric.sphere z (1 / 2),
      ‖F_lift w‖ ≤ 10 ^ 7 * Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im)) := by
    intro w hw
    have hw' : ‖w - z‖ = 1 / 2 := by
      rw [Metric.mem_sphere, Complex.dist_eq] at hw; exact hw
    have him : 1 ≤ w.im := by
      have h2 : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm _
      have h3 : -((w - z).im) ≤ ‖w - z‖ := le_trans (neg_le_abs _) h2
      rw [Complex.sub_im] at h3
      linarith [hw']
    calc ‖F_lift w‖ ≤ 10 ^ 7 * Real.exp (-(2 * Real.pi * w.im)) := F_lift_bound w him
      _ ≤ 10 ^ 7 * Real.exp (-(2 * Real.pi * (z.im - 1 / 2))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.exp_le_exp.mpr
          have h3 : -((w - z).im) ≤ ‖w - z‖ := le_trans (neg_le_abs _) (Complex.abs_im_le_norm _)
          rw [Complex.sub_im] at h3
          have h3' : z.im - w.im ≤ 1 / 2 := by linarith [h3, hw']
          rw [show -(2 * Real.pi * (z.im - 1 / 2)) = -(2 * Real.pi * z.im) + Real.pi by ring]
          nlinarith [h3', Real.pi_pos]
      _ = 10 ^ 7 * Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im)) := by
          rw [show -(2 * Real.pi * (z.im - 1 / 2)) = Real.pi + -(2 * Real.pi * z.im) by ring,
            Real.exp_add]
          ring
  have hmain := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := 1 / 2)
    (C := 10 ^ 7 * Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im))) hR hdiff hsp
  rw [div_eq_mul_inv] at hmain
  have hexp : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * z.im)) := (Real.exp_pos _).le
  calc ‖deriv F_lift z‖
      ≤ (10 ^ 7 * Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im))) * (1 / 2)⁻¹ := hmain
    _ = 2 * 10 ^ 7 * Real.exp Real.pi * Real.exp (-(2 * Real.pi * z.im)) := by norm_num; ring
    _ ≤ 2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * z.im)) := by nlinarith [hexp, hexpπ]

/-- **The mean-value bound for the lift.**  If the segment joining `z₀` and `z` stays in
`Im ≥ 3/2`, then `‖F_lift z - F_lift z₀‖ ≤ 2·10⁹ e^{-2π min (Im z) (Im z₀)} ‖z - z₀‖`. -/
theorem F_lift_diff_bound (z z₀ : ℂ)
    (hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → 3 / 2 ≤ (z₀ + s • (z - z₀)).im) :
    ‖F_lift z - F_lift z₀‖
      ≤ 2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * min z.im z₀.im)) * ‖z - z₀‖ := by
  have hFdiff : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℂ F_lift w := fun w hw =>
    F_lift_differentiableOn.differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds (by simpa using hw))
  have hγ : ∀ s : ℝ, HasDerivAt (fun s : ℝ => z₀ + s • (z - z₀)) (z - z₀) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => s • (z - z₀)) ((1 : ℝ) • (z - z₀)) s :=
      (hasDerivAt_id s).smul_const (z - z₀)
    have h2 := h1.const_add z₀
    simpa using h2
  have hcomp : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s : ℝ => F_lift (z₀ + s • (z - z₀)))
        (deriv F_lift (z₀ + s • (z - z₀)) * (z - z₀)) (Set.Icc (0 : ℝ) 1) s := by
    intro s hs
    have him : 0 < (z₀ + s • (z - z₀)).im := by linarith [hseg s hs]
    exact (((hFdiff _ him).hasDerivAt).comp s (hγ s)).hasDerivWithinAt
  have him_le : ∀ s ∈ Set.Icc (0 : ℝ) 1, min z.im z₀.im ≤ (z₀ + s • (z - z₀)).im := by
    intro s hs
    have hγim : (z₀ + s • (z - z₀)).im = (1 - s) * z₀.im + s * z.im := by
      simp only [Complex.add_im, Complex.smul_im, Complex.sub_im]
      ring
    rw [hγim]
    have h1 : min z.im z₀.im ≤ z.im := min_le_left _ _
    have h2 : min z.im z₀.im ≤ z₀.im := min_le_right _ _
    nlinarith [hs.1, hs.2]
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) 1,
      ‖deriv F_lift (z₀ + s • (z - z₀)) * (z - z₀)‖
        ≤ 2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * min z.im z₀.im)) * ‖z - z₀‖ := by
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self hs
    have him : 3 / 2 ≤ (z₀ + s • (z - z₀)).im := hseg s hs'
    calc ‖deriv F_lift (z₀ + s • (z - z₀)) * (z - z₀)‖
        = ‖deriv F_lift (z₀ + s • (z - z₀))‖ * ‖z - z₀‖ := norm_mul _ _
      _ ≤ (2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * (z₀ + s • (z - z₀)).im))) * ‖z - z₀‖ :=
          mul_le_mul_of_nonneg_right (F_lift_deriv_bound _ him) (norm_nonneg _)
      _ ≤ (2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * min z.im z₀.im))) * ‖z - z₀‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.exp_le_exp.mpr
          nlinarith [him_le s hs', Real.pi_pos]
  have hmain := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := 1) hcomp hbound 1
    (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  have h1 : F_lift (z₀ + (1 : ℝ) • (z - z₀)) = F_lift z := by
    rw [one_smul]; congr 1; ring
  have h0 : F_lift (z₀ + (0 : ℝ) • (z - z₀)) = F_lift z₀ := by
    rw [zero_smul, add_zero]
  rw [h1, h0, sub_zero, mul_one] at hmain
  exact hmain




/-! ## Integer translations of `j` and of `F` -/

/-- `F w = j w - q w⁻¹ - 744`. -/
def Ffun (w : ℍ) : ℂ := Work.Kernels.jInvariantFun w - (Work.Kernels.qParamFun w)⁻¹ - 744

lemma Ffun_eq_F_lift (w : ℍ) : Ffun w = F_lift (w : ℂ) := by
  simp [Ffun, F_lift, UpperHalfPlane.ofComplex_apply]

lemma qParamFun_vadd_one (τ : ℍ) :
    Work.Kernels.qParamFun ((1 : ℝ) +ᵥ τ) = Work.Kernels.qParamFun τ := by
  simp only [Work.Kernels.qParamFun]
  rw [show ((((1 : ℝ) +ᵥ τ : ℍ)) : ℂ) = 1 + (τ : ℂ) by
    rw [UpperHalfPlane.coe_vadd]; push_cast; ring]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 + (τ : ℂ))
      = (1 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) + 2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) by
        push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

lemma Ffun_vadd_one (τ : ℍ) : Ffun ((1 : ℝ) +ᵥ τ) = Ffun τ := by
  simp only [Ffun, qParamFun_vadd_one, Work.Kernels.KernelFacts.jInvariantFun_vadd_one]

lemma Ffun_nat_vadd : ∀ (m : ℕ) (τ : ℍ), Ffun ((m : ℝ) +ᵥ τ) = Ffun τ := by
  intro m
  induction m with
  | zero => intro τ; simp
  | succ k ih =>
      intro τ
      have h1 : ((k + 1 : ℕ) : ℝ) +ᵥ τ = (1 : ℝ) +ᵥ (((k : ℕ) : ℝ) +ᵥ τ) := by
        rw [← add_vadd]; push_cast; ring_nf
      rw [h1, Ffun_vadd_one, ih]

lemma Ffun_int_vadd (k : ℤ) (τ : ℍ) : Ffun ((k : ℝ) +ᵥ τ) = Ffun τ := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · rw [hm]; push_cast; exact Ffun_nat_vadd m τ
  · rw [hm]
    have h1 : ((m : ℝ) +ᵥ ((-(m : ℝ)) +ᵥ τ)) = τ := by rw [← add_vadd]; simp
    have h2 := Ffun_nat_vadd m ((-(m : ℝ)) +ᵥ τ)
    rw [h1] at h2
    push_cast
    exact h2.symm

/-! ## Integer translations of `j` and of `q` -/

lemma jInvariantFun_nat_vadd : ∀ (m : ℕ) (τ : ℍ),
    Work.Kernels.jInvariantFun ((m : ℝ) +ᵥ τ) = Work.Kernels.jInvariantFun τ := by
  intro m
  induction m with
  | zero => intro τ; simp
  | succ k ih =>
      intro τ
      have h1 : ((k + 1 : ℕ) : ℝ) +ᵥ τ = (1 : ℝ) +ᵥ (((k : ℕ) : ℝ) +ᵥ τ) := by
        rw [← add_vadd]; push_cast; ring_nf
      rw [h1, Work.Kernels.KernelFacts.jInvariantFun_vadd_one, ih]

lemma jInvariantFun_int_vadd (k : ℤ) (τ : ℍ) :
    Work.Kernels.jInvariantFun ((k : ℝ) +ᵥ τ) = Work.Kernels.jInvariantFun τ := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · rw [hm]; push_cast; exact jInvariantFun_nat_vadd m τ
  · rw [hm]
    have h1 : ((m : ℝ) +ᵥ ((-(m : ℝ)) +ᵥ τ)) = τ := by rw [← add_vadd]; simp
    have h2 := jInvariantFun_nat_vadd m ((-(m : ℝ)) +ᵥ τ)
    rw [h1] at h2
    push_cast
    exact h2.symm

lemma qParamFun_nat_vadd : ∀ (m : ℕ) (τ : ℍ),
    Work.Kernels.qParamFun ((m : ℝ) +ᵥ τ) = Work.Kernels.qParamFun τ := by
  intro m
  induction m with
  | zero => intro τ; simp
  | succ k ih =>
      intro τ
      have h1 : ((k + 1 : ℕ) : ℝ) +ᵥ τ = (1 : ℝ) +ᵥ (((k : ℕ) : ℝ) +ᵥ τ) := by
        rw [← add_vadd]; push_cast; ring_nf
      rw [h1, qParamFun_vadd_one, ih]

lemma qParamFun_int_vadd (k : ℤ) (τ : ℍ) :
    Work.Kernels.qParamFun ((k : ℝ) +ᵥ τ) = Work.Kernels.qParamFun τ := by
  obtain ⟨m, hm | hm⟩ := Int.eq_nat_or_neg k
  · rw [hm]; push_cast; exact qParamFun_nat_vadd m τ
  · rw [hm]
    have h1 : ((m : ℝ) +ᵥ ((-(m : ℝ)) +ᵥ τ)) = τ := by rw [← add_vadd]; simp
    have h2 := qParamFun_nat_vadd m ((-(m : ℝ)) +ᵥ τ)
    rw [h1] at h2
    push_cast
    exact h2.symm

/-! ## The exponential difference bound used in the "thin" case -/

/-- `|e^u - 1| ≥ |u|/2` for real `|u| ≤ 1`. -/
lemma abs_exp_sub_one_ge_half_A (u : ℝ) (hu : |u| ≤ 1) : |Real.exp u - 1| ≥ |u| / 2 := by
  rcases lt_or_ge u 0 with h | h
  · have h1 : Real.exp u ≤ 1 / (1 + (-u)) := by
      rw [le_div_iff₀ (by linarith)]
      have h3 : 1 + (-u) ≤ Real.exp (-u) := by linarith [Real.add_one_le_exp (-u)]
      have h4 : Real.exp u * Real.exp (-u) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      nlinarith [Real.exp_pos u, Real.exp_pos (-u), h3, h4]
    rw [abs_of_neg h, abs_of_neg (by rw [sub_neg]; exact Real.exp_lt_one_iff.mpr h)]
    have h5 : 1 - 1 / (1 + (-u)) ≤ 1 - Real.exp u := by linarith
    have h6 : 1 - 1 / (1 + (-u)) = (-u) / (1 + (-u)) := by
      rw [one_sub_div (by linarith : (1 : ℝ) + (-u) ≠ 0)]
      ring
    have h7 : (-u) / 2 ≤ (-u) / (1 + (-u)) := by
      apply div_le_div_of_nonneg_left (by linarith) (by linarith)
      linarith [(abs_le.mp hu).1]
    linarith [h5, h6.le, h6.ge, h7]
  · rw [abs_of_nonneg h,
      abs_of_nonneg (by linarith [Real.add_one_le_exp u] : (0 : ℝ) ≤ Real.exp u - 1)]
    linarith [Real.add_one_le_exp u]

/-- **Key bound for the thin case.**  For `|Re X| ≤ 1/2` and `|Im X| ≤ 1/8`,
`‖exp (-2πiX) - 1‖ ≥ 2‖X‖`. -/
lemma norm_exp_neg_two_pi_I_sub_one_ge (X : ℂ) (h1 : |X.re| ≤ 1 / 2) (h2 : |X.im| ≤ 1 / 8) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I * X)) - 1‖ ≥ 2 * ‖X‖ := by
  have harg : -(2 * Real.pi * Complex.I * X)
      = ((2 * Real.pi * X.im : ℝ) : ℂ) + ((-(2 * Real.pi * X.re) : ℝ) : ℂ) * Complex.I := by
    push_cast
    rw [Complex.ext_iff]
    constructor <;>
      simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_re,
        Complex.add_im] <;> ring
  have hRe : (-(2 * Real.pi * Complex.I * X)).re = 2 * Real.pi * X.im := by
    rw [harg, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re]
    ring
  have hIm : (-(2 * Real.pi * Complex.I * X)).im = -(2 * Real.pi * X.re) := by
    rw [harg, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_im]
    ring
  have hnorm : ‖Complex.exp (-(2 * Real.pi * Complex.I * X))‖ = Real.exp (2 * Real.pi * X.im) := by
    rw [Complex.norm_exp, hRe]
  have hReE : (Complex.exp (-(2 * Real.pi * Complex.I * X))).re
      = Real.exp (2 * Real.pi * X.im) * Real.cos (2 * Real.pi * X.re) := by
    rw [Complex.exp_re, hRe, hIm, Real.cos_neg]
  have hImE : (Complex.exp (-(2 * Real.pi * Complex.I * X))).im
      = -(Real.exp (2 * Real.pi * X.im) * Real.sin (2 * Real.pi * X.re)) := by
    rw [Complex.exp_im, hRe, hIm, Real.sin_neg]
    ring
  have hsq : ‖Complex.exp (-(2 * Real.pi * Complex.I * X)) - 1‖ ^ 2
      = (Real.exp (2 * Real.pi * X.im) - 1) ^ 2
        + 2 * Real.exp (2 * Real.pi * X.im) * (1 - Real.cos (2 * Real.pi * X.re)) := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hReE, hImE,
      Complex.one_re, Complex.one_im]
    have htrig : Real.cos (Real.pi * X.re * 2) ^ 2 + Real.sin (Real.pi * X.re * 2) ^ 2 = 1 := by
      rw [show Real.pi * X.re * 2 = 2 * Real.pi * X.re by ring]
      exact Real.cos_sq_add_sin_sq _
    ring_nf
    nlinarith [htrig]
  have hcos : 1 - Real.cos (2 * Real.pi * X.re) ≥ 8 * X.re ^ 2 := by
    have h := Real.cos_le_one_sub_mul_cos_sq (x := 2 * Real.pi * X.re) (by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
      nlinarith [Real.pi_pos, h1])
    have h' : (2 / Real.pi ^ 2) * (2 * Real.pi * X.re) ^ 2 = 8 * X.re ^ 2 := by
      have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
      field_simp
      ring
    linarith [h, h'.le, h'.ge]
  have hEim : (1 / 3 : ℝ) ≤ Real.exp (2 * Real.pi * X.im) := by
    have h3 : -(1 : ℝ) ≤ 2 * Real.pi * X.im := by
      have := neg_abs_le X.im
      nlinarith [Real.pi_pos, Real.pi_lt_four, h2, this]
    have h4 : Real.exp (-(1 : ℝ)) ≤ Real.exp (2 * Real.pi * X.im) := Real.exp_le_exp.mpr h3
    have h5 : (1 / 3 : ℝ) ≤ Real.exp (-(1 : ℝ)) := by
      rw [Real.exp_neg]
      have h6 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      have h8 : (3 : ℝ)⁻¹ ≤ (Real.exp 1)⁻¹ :=
        (inv_le_inv₀ (by norm_num) (Real.exp_pos 1)).mpr h6
      simpa [one_div] using h8
    linarith
  have h6 : (Real.exp (2 * Real.pi * X.im) - 1) ^ 2 ≥ Real.pi ^ 2 * X.im ^ 2 := by
    have h7 : |2 * Real.pi * X.im| ≤ 1 := by
      calc |2 * Real.pi * X.im| = 2 * Real.pi * |X.im| := by
            rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
        _ ≤ 2 * Real.pi * (1 / 8) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ 1 := by nlinarith [Real.pi_lt_four]
    have h8 := abs_exp_sub_one_ge_half_A (2 * Real.pi * X.im) h7
    have h9 : |2 * Real.pi * X.im| = 2 * Real.pi * |X.im| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    rw [h9] at h8
    have h10 : Real.pi * |X.im| ≤ |Real.exp (2 * Real.pi * X.im) - 1| := by linarith [h8]
    have h11 : (Real.pi * |X.im|) ^ 2 ≤ (Real.exp (2 * Real.pi * X.im) - 1) ^ 2 := by
      have h11a : (Real.pi * |X.im|) ^ 2 ≤ |Real.exp (2 * Real.pi * X.im) - 1| ^ 2 :=
        pow_le_pow_left₀ (by positivity) h10 2
      rwa [sq_abs (Real.exp (2 * Real.pi * X.im) - 1)] at h11a
    have h12b : |X.im| ^ 2 = X.im ^ 2 := sq_abs X.im
    rw [show (Real.pi * |X.im|) ^ 2 = Real.pi ^ 2 * |X.im| ^ 2 by ring, h12b] at h11
    exact h11
  have h10 : 2 * Real.exp (2 * Real.pi * X.im) * (1 - Real.cos (2 * Real.pi * X.re))
      ≥ 2 * (1 / 3) * (8 * X.re ^ 2) := by
    have h1 : (1 / 3 : ℝ) * (8 * X.re ^ 2)
        ≤ Real.exp (2 * Real.pi * X.im) * (1 - Real.cos (2 * Real.pi * X.re)) :=
      mul_le_mul hEim hcos (by positivity) (by positivity)
    linarith
  have h11 : Real.pi ^ 2 * X.im ^ 2 ≥ 4 * X.im ^ 2 := by
    have hπ : (4 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    have h := mul_le_mul_of_nonneg_right hπ (sq_nonneg X.im)
    linarith [h]
  have h12 : 2 * (1 / 3 : ℝ) * (8 * X.re ^ 2) ≥ 4 * X.re ^ 2 := by nlinarith [sq_nonneg X.re]
  have h13 : (2 * ‖X‖) ^ 2 = 4 * (X.re ^ 2 + X.im ^ 2) := by
    rw [mul_pow, Complex.sq_norm, Complex.normSq_apply]; ring
  have h14 : ‖Complex.exp (-(2 * Real.pi * Complex.I * X)) - 1‖ ^ 2 ≥ (2 * ‖X‖) ^ 2 := by
    have h6' : Real.pi ^ 2 * X.im ^ 2 ≤ (Real.exp (2 * Real.pi * X.im) - 1) ^ 2 := h6
    have h10' : 2 * (1 / 3 : ℝ) * (8 * X.re ^ 2)
        ≤ 2 * Real.exp (2 * Real.pi * X.im) * (1 - Real.cos (2 * Real.pi * X.re)) := h10
    rw [hsq, h13]
    linarith [h6', h10', h11, h12]
  have h15 := Real.sqrt_le_sqrt h14
  rw [Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)] at h15
  exact h15
/-! ## Numeric relations for the case analysis -/

lemma exp_mul_exp_neg (u : ℝ) : Real.exp u * Real.exp (-u) = 1 := by
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

lemma exp_neg_mul_exp (u : ℝ) : Real.exp (-u) * Real.exp u = 1 := by
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

/-- `2 ≤ e^{3/4}`, used to detect that a large `‖Eun‖` forces `‖1 - Eun‖` to be large. -/
lemma exp_three_quarters_ge_two : (2 : ℝ) ≤ Real.exp (3 / 4) := by
  have h1 : Real.exp (3 / 4 : ℝ) = (Real.exp (1 / 8)) ^ 6 := by
    rw [show (3 / 4 : ℝ) = ((6 : ℕ) : ℝ) * (1 / 8) by norm_num, Real.exp_nat_mul]
  rw [h1]
  have h2 : (1.125 : ℝ) ≤ Real.exp (1 / 8) := by
    have h := Real.add_one_le_exp (1 / 8 : ℝ)
    linarith
  have h3 : (1.125 : ℝ) ^ 6 ≤ (Real.exp (1 / 8)) ^ 6 := pow_le_pow_left₀ (by norm_num) h2 6
  have h4 : (2 : ℝ) ≤ (1.125 : ℝ) ^ 6 := by norm_num
  linarith

lemma exp_four_le_sixty (v : ℝ) (h1 : v ≤ 1 / 10) : Real.exp (4 * Real.pi * v) ≤ 60 := by
  have h2 : 4 * Real.pi * v ≤ 2 := by nlinarith [Real.pi_lt_d20, Real.pi_pos]
  have h3 : Real.exp (4 * Real.pi * v) ≤ Real.exp 2 := Real.exp_le_exp.mpr h2
  have h4 : Real.exp 2 = (Real.exp 1) ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  have h5 : (Real.exp 1) ^ 2 ≤ 9 := by
    have h6 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
    nlinarith [h6, Real.exp_pos 1]
  rw [h4] at h3
  linarith

lemma exp_two_pi_le_598 : Real.exp (2 * Real.pi) ≤ 598 := by
  have h1 : 2 * Real.pi ≤ 6.3 := by nlinarith [Real.pi_lt_d20]
  refine le_trans (Real.exp_le_exp.mpr h1) ?_
  have h3 : (6.3 : ℝ) = 6 + 0.3 := by norm_num
  rw [h3, Real.exp_add]
  have h4 : Real.exp 6 ≤ 404 := by
    have h5 : Real.exp 6 = (Real.exp 1) ^ 6 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h5]
    have h6 : Real.exp 1 ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
    have h7 : (2.7182818286 : ℝ) ^ 6 ≤ 404 := by norm_num
    exact le_trans (pow_le_pow_left₀ (Real.exp_pos 1).le h6 6) h7
  have h8 : Real.exp 0.3 ≤ 1.43 := by
    have h9 := Real.exp_bound_div_one_sub_of_interval (x := 0.3) (by norm_num) (by norm_num)
    have h10 : (1 : ℝ) / (1 - 0.3) ≤ 1.43 := by norm_num
    linarith
  calc Real.exp 6 * Real.exp 0.3 ≤ 404 * 1.43 :=
        mul_le_mul h4 h8 (Real.exp_pos 0.3).le (by norm_num)
    _ ≤ 598 := by norm_num

lemma exp_four_mul_le (v : ℝ) (h1 : 1 / 10 ≤ v) (h2 : v ≤ 1) :
    Real.exp (4 * Real.pi * v) ≤ 601 * (Real.exp (2 * Real.pi * v) - 1) := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hz : 0 < Real.exp (2 * Real.pi * v) := Real.exp_pos _
  have hlo : (1.5 : ℝ) ≤ Real.exp (2 * Real.pi * v) := by
    have h3 : (0.5 : ℝ) ≤ 2 * Real.pi * v := by nlinarith [Real.pi_gt_three]
    calc (1.5 : ℝ) = 0.5 + 1 := by norm_num
      _ ≤ Real.exp 0.5 := by linarith [Real.add_one_le_exp (0.5 : ℝ)]
      _ ≤ Real.exp (2 * Real.pi * v) := Real.exp_le_exp.mpr h3
  have hhi : Real.exp (2 * Real.pi * v) ≤ 598 := by
    have h3 : 2 * Real.pi * v ≤ 2 * Real.pi := by nlinarith [hp, h2]
    exact le_trans (Real.exp_le_exp.mpr h3) exp_two_pi_le_598
  have he : Real.exp (4 * Real.pi * v)
      = Real.exp (2 * Real.pi * v) * Real.exp (2 * Real.pi * v) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he]
  have key : 1 ≤ (Real.exp (2 * Real.pi * v) - 1) * (600 - Real.exp (2 * Real.pi * v)) := by
    nlinarith [hlo, hhi]
  nlinarith [key, hz]

/-- For `0 ≤ v ≤ 1`: `e^{4πv} ≤ 601 · max (1/10) (e^{2πv} - 1)`. -/
lemma max_exp_relation (v : ℝ) (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    Real.exp (4 * Real.pi * v) ≤ 601 * max (1 / 10) (Real.exp (2 * Real.pi * v) - 1) := by
  rcases lt_or_ge v (1 / 10) with hv | hv
  · have h2 : Real.exp (4 * Real.pi * v) ≤ 60 := exp_four_le_sixty v hv.le
    have h3 : (1 / 10 : ℝ) ≤ max (1 / 10) (Real.exp (2 * Real.pi * v) - 1) := le_max_left _ _
    nlinarith
  · have h2 : (1 / 10 : ℝ) ≤ Real.exp (2 * Real.pi * v) - 1 := by
      have h3 : (2 * Real.pi) * (1 / 10) ≤ 2 * Real.pi * v := by nlinarith [Real.pi_pos, hv]
      have h4 : Real.exp ((2 * Real.pi) * (1 / 10)) ≤ Real.exp (2 * Real.pi * v) :=
        Real.exp_le_exp.mpr h3
      have h5 : (1 / 10 : ℝ) ≤ Real.exp ((2 * Real.pi) * (1 / 10)) - 1 := by
        have h6 : (2 * Real.pi) * (1 / 10) + 1 ≤ Real.exp ((2 * Real.pi) * (1 / 10)) :=
          Real.add_one_le_exp _
        nlinarith [Real.pi_gt_three, h6]
      linarith
    rw [max_eq_right h2]
    exact exp_four_mul_le v hv h1

lemma exp_8pi_ge : (2.6 * 10 ^ 10 : ℝ) ≤ Real.exp (8 * Real.pi) := by
  have h2 : (24 : ℝ) ≤ 8 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h3 : Real.exp 24 ≤ Real.exp (8 * Real.pi) := Real.exp_le_exp.mpr h2
  have h4 : Real.exp 24 = (Real.exp 1) ^ 24 := by
    rw [show (24 : ℝ) = ((24 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  have h5 : (2.6 * 10 ^ 10 : ℝ) ≤ (Real.exp 1) ^ 24 := by
    have h6 : (2.7182818283 : ℝ) ^ 24 ≤ (Real.exp 1) ^ 24 :=
      pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 24
    have h7 : (2.6 * 10 ^ 10 : ℝ) ≤ (2.7182818283 : ℝ) ^ 24 := by norm_num
    linarith
  rw [h4] at h3
  linarith

lemma exp_23_ge : (8 * 10 ^ 9 : ℝ) ≤ Real.exp 23 := by
  have h4 : Real.exp 23 = (Real.exp 1) ^ 23 := by
    rw [show (23 : ℝ) = ((23 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  rw [h4]
  have h6 : (2.7182818283 : ℝ) ^ 23 ≤ (Real.exp 1) ^ 23 :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 23
  have h7 : (8 * 10 ^ 9 : ℝ) ≤ (2.7182818283 : ℝ) ^ 23 := by norm_num
  linarith

lemma exp_two_pi_sub_one_ge_500 : (500 : ℝ) ≤ Real.exp (2 * Real.pi) - 1 := by
  have h1 : Real.exp 6 * Real.exp 0.28 ≤ Real.exp (2 * Real.pi) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [Real.pi_gt_d20])
  have h2 : (1.28 : ℝ) ≤ Real.exp 0.28 := by
    have h := Real.add_one_le_exp (0.28 : ℝ)
    linarith
  have h3 : (403 : ℝ) ≤ Real.exp 6 := by
    have h4 : Real.exp 6 = (Real.exp 1) ^ 6 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
    rw [h4]
    have h5 : (2.7182818283 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 :=
      pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 6
    have h6 : (403 : ℝ) ≤ (2.7182818283 : ℝ) ^ 6 := by norm_num
    linarith
  nlinarith [h1, h2, h3]

lemma exp_neg_4pi_le : Real.exp (-(4 * Real.pi)) ≤ 1 / 100000 := by
  have h1 : Real.exp (-(4 * Real.pi)) ≤ Real.exp (-(12 : ℝ)) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
  refine le_trans h1 ?_
  rw [Real.exp_neg, inv_eq_one_div]
  refine one_div_le_one_div_of_le (by norm_num) ?_
  have h4 : Real.exp 12 = (Real.exp 1) ^ 12 := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  rw [h4]
  have h5 : (2.7182818283 : ℝ) ^ 12 ≤ (Real.exp 1) ^ 12 :=
    pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) 12
  have h6 : (100000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 12 := by norm_num
  linarith

/-- **Non-thin case, real arithmetic.** -/
lemma nonthin_real {A B err D : ℝ} (hA : 2 ≤ A) (hB : 1 ≤ B)
    (hD1 : Real.exp (2 * Real.pi * A) * (1 / 10) ≤ D)
    (hD2 : |Real.exp (2 * Real.pi * A) - Real.exp (2 * Real.pi * B)| ≤ D)
    (herr : err ≤ 2 * 10 ^ 7 * Real.exp (-(2 * Real.pi * min A B))) : err ≤ D / 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hA8 : 8 * Real.pi ≤ 4 * Real.pi * A := by nlinarith [hpi, hA]
  have hbig : 4 * 10 ^ 7 * 601 ≤ Real.exp (4 * Real.pi * A) := by
    have h1 : Real.exp (8 * Real.pi) ≤ Real.exp (4 * Real.pi * A) := Real.exp_le_exp.mpr hA8
    have h2 : (4 * 10 ^ 7 * 601 : ℝ) ≤ 2.6 * 10 ^ 10 := by norm_num
    linarith [exp_8pi_ge, h1, h2]
  have hbig2 : (4 * 10 ^ 8 : ℝ) ≤ Real.exp (4 * Real.pi * A) := by
    have h1 : (4 * 10 ^ 8 : ℝ) ≤ 4 * 10 ^ 7 * 601 := by norm_num
    linarith [hbig, h1]
  rcases lt_or_ge B A with hBA | hBA
  · rw [min_eq_right hBA.le] at herr
    have hD2' : Real.exp (2 * Real.pi * B) * (Real.exp (2 * Real.pi * (A - B)) - 1) ≤ D := by
      have h3 : Real.exp (2 * Real.pi * A) - Real.exp (2 * Real.pi * B)
          = Real.exp (2 * Real.pi * B) * (Real.exp (2 * Real.pi * (A - B)) - 1) := by
        rw [mul_sub, mul_one, ← Real.exp_add]
        congr 1
        ring
      have h4 : 0 ≤ Real.exp (2 * Real.pi * A) - Real.exp (2 * Real.pi * B) := by
        have h5 : Real.exp (2 * Real.pi * B) ≤ Real.exp (2 * Real.pi * A) :=
          Real.exp_le_exp.mpr (by nlinarith [hpi, hBA.le])
        linarith
      rw [abs_of_nonneg h4, h3] at hD2
      exact hD2
    have hDm : Real.exp (2 * Real.pi * B) * max (1 / 10) (Real.exp (2 * Real.pi * (A - B)) - 1)
        ≤ D := by
      rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le]
      refine max_le ?_ hD2'
      have h6 : Real.exp (2 * Real.pi * B) ≤ Real.exp (2 * Real.pi * A) :=
        Real.exp_le_exp.mpr (by nlinarith [hpi, hBA.le])
      linarith [hD1, h6]
    rcases lt_or_ge (A - B) 1 with hv1 | hv1
    · have hv0 : 0 ≤ A - B := by linarith [hBA.le]
      have hm := max_exp_relation (A - B) hv0 hv1.le
      have hdiv : Real.exp (4 * Real.pi * (A - B)) / 601
          ≤ max (1 / 10) (Real.exp (2 * Real.pi * (A - B)) - 1) := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 601)]
        linarith [hm]
      have hm2 : Real.exp (2 * Real.pi * B) * (Real.exp (4 * Real.pi * (A - B)) / 601)
          ≤ Real.exp (2 * Real.pi * B)
            * max (1 / 10) (Real.exp (2 * Real.pi * (A - B)) - 1) :=
        mul_le_mul_of_nonneg_left hdiv (Real.exp_pos _).le
      have key : 4 * 10 ^ 7 * Real.exp (-(2 * Real.pi * B))
          ≤ Real.exp (2 * Real.pi * B) * (Real.exp (4 * Real.pi * (A - B)) / 601) := by
        have h601 : (0 : ℝ) < 601 := by norm_num
        rw [show Real.exp (2 * Real.pi * B) * (Real.exp (4 * Real.pi * (A - B)) / 601)
              = Real.exp (2 * Real.pi * B) * Real.exp (4 * Real.pi * (A - B)) / 601 by ring]
        rw [le_div_iff₀ h601]
        have hC : (4 * 10 ^ 7 * 601 : ℝ) * Real.exp (-(2 * Real.pi * B))
            ≤ Real.exp (4 * Real.pi * A) * Real.exp (-(2 * Real.pi * B)) :=
          mul_le_mul_of_nonneg_right hbig (Real.exp_pos _).le
        have h1 : Real.exp (4 * Real.pi * A) * Real.exp (-(2 * Real.pi * B))
            = Real.exp (2 * Real.pi * B) * Real.exp (4 * Real.pi * (A - B)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        rw [h1] at hC
        have he : (4 * 10 ^ 7 * 601 : ℝ) * Real.exp (-(2 * Real.pi * B))
            = 4 * 10 ^ 7 * Real.exp (-(2 * Real.pi * B)) * 601 := by ring
        rw [he] at hC
        exact hC
      have h2err : 2 * err ≤ D := by
        have e1 : 2 * err ≤ 4 * 10 ^ 7 * Real.exp (-(2 * Real.pi * B)) := by linarith [herr]
        exact le_trans e1 (le_trans key (le_trans hm2 hDm))
      linarith
    · have hD2'' : Real.exp (2 * Real.pi * B) * (Real.exp (2 * Real.pi) - 1) ≤ D := by
        have h4 : Real.exp (2 * Real.pi) - 1 ≤ Real.exp (2 * Real.pi * (A - B)) - 1 := by
          have h5 : Real.exp (2 * Real.pi) ≤ Real.exp (2 * Real.pi * (A - B)) :=
            Real.exp_le_exp.mpr (by nlinarith [hpi, hv1])
          linarith
        have h6 := mul_le_mul_of_nonneg_left h4 (Real.exp_pos (2 * Real.pi * B)).le
        linarith [hD2', h6]
      have key2 : 4 * 10 ^ 7 * Real.exp (-(2 * Real.pi * B))
          ≤ Real.exp (2 * Real.pi * B) * (Real.exp (2 * Real.pi) - 1) := by
        have h4 : 4 * 10 ^ 7 * Real.exp (-(4 * Real.pi * B)) ≤ Real.exp (2 * Real.pi) - 1 := by
          have h5 : Real.exp (-(4 * Real.pi * B)) ≤ Real.exp (-(4 * Real.pi)) :=
            Real.exp_le_exp.mpr (by nlinarith [hpi, hB])
          have h6 : 4 * 10 ^ 7 * Real.exp (-(4 * Real.pi)) ≤ Real.exp (2 * Real.pi) - 1 := by
            have h7 : 4 * 10 ^ 7 * Real.exp (-(4 * Real.pi)) ≤ 4 * 10 ^ 7 * (1 / 100000) :=
              mul_le_mul_of_nonneg_left exp_neg_4pi_le (by norm_num)
            linarith [h7, exp_two_pi_sub_one_ge_500]
          calc 4 * 10 ^ 7 * Real.exp (-(4 * Real.pi * B))
                ≤ 4 * 10 ^ 7 * Real.exp (-(4 * Real.pi)) :=
                mul_le_mul_of_nonneg_left h5 (by norm_num)
            _ ≤ Real.exp (2 * Real.pi) - 1 := h6
        have h8 := mul_le_mul_of_nonneg_right h4 (Real.exp_pos (2 * Real.pi * B)).le
        have h9 : (4 * 10 ^ 7 * Real.exp (-(4 * Real.pi * B))) * Real.exp (2 * Real.pi * B)
            = 4 * 10 ^ 7 * Real.exp (-(2 * Real.pi * B)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 1
          ring
        rw [h9] at h8
        linarith [h8]
      have h2err : 2 * err ≤ D := by
        have e1 : 2 * err ≤ 4 * 10 ^ 7 * Real.exp (-(2 * Real.pi * B)) := by linarith [herr]
        exact le_trans e1 (le_trans key2 hD2'')
      linarith
  · rw [min_eq_left hBA] at herr
    have key3 : 4 * 10 ^ 7 * Real.exp (-(2 * Real.pi * A))
        ≤ Real.exp (2 * Real.pi * A) * (1 / 10) := by
      rw [show Real.exp (2 * Real.pi * A) * (1 / 10) = Real.exp (2 * Real.pi * A) / 10 by ring]
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10)]
      have h10 : Real.exp (-(2 * Real.pi * A)) * Real.exp (2 * Real.pi * A) = 1 :=
        exp_neg_mul_exp _
      have h11 : Real.exp (2 * Real.pi * A) * Real.exp (2 * Real.pi * A)
          = Real.exp (4 * Real.pi * A) := by
        rw [← Real.exp_add]; congr 1; ring
      have s1 : (4 * 10 ^ 8 : ℝ)
          ≤ Real.exp (2 * Real.pi * A) * Real.exp (2 * Real.pi * A) := by
        rw [h11]; exact hbig2
      have s2 : (4 * 10 ^ 8) * Real.exp (-(2 * Real.pi * A))
          ≤ (Real.exp (2 * Real.pi * A) * Real.exp (2 * Real.pi * A))
            * Real.exp (-(2 * Real.pi * A)) :=
        mul_le_mul_of_nonneg_right s1 (Real.exp_pos _).le
      have s3 : (Real.exp (2 * Real.pi * A) * Real.exp (2 * Real.pi * A))
            * Real.exp (-(2 * Real.pi * A)) = Real.exp (2 * Real.pi * A) := by
        calc (Real.exp (2 * Real.pi * A) * Real.exp (2 * Real.pi * A))
              * Real.exp (-(2 * Real.pi * A))
            = Real.exp (2 * Real.pi * A)
              * (Real.exp (2 * Real.pi * A) * Real.exp (-(2 * Real.pi * A))) := by ring
          _ = Real.exp (2 * Real.pi * A) * 1 := by rw [exp_mul_exp_neg]
          _ = Real.exp (2 * Real.pi * A) := by ring
      rw [s3] at s2
      have s4 : (4 * 10 ^ 8) * Real.exp (-(2 * Real.pi * A))
          = 4 * 10 ^ 7 * Real.exp (-(2 * Real.pi * A)) * 10 := by ring
      rw [s4] at s2
      exact s2
    have h2err : 2 * err ≤ D := by
      have e1 : 2 * err ≤ 4 * 10 ^ 7 * Real.exp (-(2 * Real.pi * A)) := by linarith [herr]
      exact le_trans e1 (le_trans key3 hD1)
    linarith

/-- **Thin case, real arithmetic.** -/
lemma thin_real {A B err D X : ℝ} (hA : 2 ≤ A) (hB : 15 / 8 ≤ B) (hX : 0 ≤ X)
    (hD : 2 * Real.exp (2 * Real.pi * B) * X ≤ D)
    (herr : err ≤ 2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * (15 / 8))) * X) : err ≤ D / 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hKey : 4 * 10 ^ 9 ≤ Real.exp (15 * Real.pi / 2) := by
    have h1 : (23 : ℝ) ≤ 15 * Real.pi / 2 := by nlinarith [Real.pi_gt_d20]
    have h2 : Real.exp 23 ≤ Real.exp (15 * Real.pi / 2) := Real.exp_le_exp.mpr h1
    linarith [exp_23_ge, h2]
  have hE : Real.exp (2 * Real.pi * (15 / 8)) = Real.exp (15 * Real.pi / 4) := by
    congr 1; ring
  have hD2 : Real.exp (15 * Real.pi / 4) * X ≤ D / 2 := by
    have h1 : Real.exp (2 * Real.pi * (15 / 8)) ≤ Real.exp (2 * Real.pi * B) :=
      Real.exp_le_exp.mpr (by nlinarith [hpi, hB])
    have h2 : Real.exp (2 * Real.pi * (15 / 8)) * X ≤ Real.exp (2 * Real.pi * B) * X :=
      mul_le_mul_of_nonneg_right h1 hX
    rw [hE] at h2
    linarith [h2, hD]
  have hstep : 2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * (15 / 8))) * X
      ≤ Real.exp (15 * Real.pi / 4) * X := by
    have h1 : 2 * 10 ^ 9 * Real.exp (-(15 * Real.pi / 4)) ≤ Real.exp (15 * Real.pi / 4) := by
      have h2 : (4 * 10 ^ 9) * Real.exp (-(15 * Real.pi / 4))
          ≤ Real.exp (15 * Real.pi / 2) * Real.exp (-(15 * Real.pi / 4)) :=
        mul_le_mul_of_nonneg_right hKey (Real.exp_pos _).le
      have h3 : Real.exp (15 * Real.pi / 2) * Real.exp (-(15 * Real.pi / 4))
          = Real.exp (15 * Real.pi / 4) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [h3] at h2
      have h4 : (2 * 10 ^ 9 : ℝ) * Real.exp (-(15 * Real.pi / 4))
          ≤ (4 * 10 ^ 9) * Real.exp (-(15 * Real.pi / 4)) :=
        mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
      linarith [h2, h4]
    have h5 : Real.exp (-(2 * Real.pi * (15 / 8))) = Real.exp (-(15 * Real.pi / 4)) := by
      congr 1; ring
    rw [h5]
    exact mul_le_mul_of_nonneg_right h1 hX
  linarith [herr, hstep, hD2]

/-! ## Auxiliary computations -/

/-- The point `i s` of the upper half plane, as a complex number. -/
lemma imagAxis_coe (s : ℝ) (hs : 0 < s) :
    ((Work.Kernels.imagAxis s hs : ℍ) : ℂ) = (s : ℂ) * Complex.I :=
  UpperHalfPlane.coe_mk _ _

/-- `j(i t) = j(i / t)`: `S` exchanges the two points. -/
lemma jInvariantFun_imagAxis_inv (t : ℝ) (ht : 0 < t) :
    Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht)) := by
  rw [← Work.Kernels.KernelFacts.jInvariantFun_S_smul (Work.Kernels.imagAxis t ht),
    Work.Asymptotics.imagAxis_smul_S t ht]

/-- `-((t i)⁻¹) = i/t` (as complex numbers). -/
lemma neg_inv_mul_I (t : ℝ) (ht : 0 < t) :
    -(((t : ℂ) * Complex.I)⁻¹) = ((Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) : ℍ) : ℂ) := by
  rw [imagAxis_coe t⁻¹ (inv_pos.mpr ht), mul_inv, Complex.inv_I, ← Complex.ofReal_inv]
  ring

/-- Every real number is within `1/2` of an integer. -/
lemma exists_int_abs_sub_le_half (x : ℝ) : ∃ n : ℤ, |x - (n : ℝ)| ≤ 1 / 2 := by
  rcases lt_or_ge (x - (⌊x⌋ : ℝ)) (1 / 2) with h | h
  · refine ⟨⌊x⌋, ?_⟩
    rw [abs_of_nonneg (by linarith [Int.floor_le x])]
    linarith
  · refine ⟨⌊x⌋ + 1, ?_⟩
    rw [abs_of_nonpos (by push_cast; linarith [Int.lt_floor_add_one x])]
    push_cast
    linarith [Int.lt_floor_add_one x]

/-! ## The main theorem -/

theorem E_jdiff_small :
    ∃ c : ℝ, 0 < c ∧ ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
      w ∈ Work.Asymptotics.KEpsilon → t ≤ 1 →
        c * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
            * ‖1 - Complex.exp (2 * Real.pi * Complex.I
                * ((((ModularGroup.S • w : UpperHalfPlane)) : ℂ) - (-(((t : ℂ) * Complex.I)⁻¹))))‖
          ≤ ‖Work.Kernels.jInvariantFun w
              - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by
  refine ⟨1 / 10, by norm_num, ?_⟩
  intro w t ht hw htle
  rw [neg_inv_mul_I t ht]
  set w' : ℍ := ModularGroup.S • w with hw'def
  set τ₀ : ℍ := Work.Kernels.imagAxis t⁻¹ (inv_pos.mpr ht) with hτ₀def
  set Eun : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((w' : ℂ) - (τ₀ : ℂ))) with hEun_def
  have hA2 : 2 ≤ w'.im := hw.2
  have hBge : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr htle
  have hτ₀im : τ₀.im = t⁻¹ := by
    rw [hτ₀def]
    simp [Work.Kernels.imagAxis]
  have hτ₀coe : ((τ₀ : ℍ) : ℂ) = ((t⁻¹ : ℝ) : ℂ) * Complex.I := by
    rw [hτ₀def]
    exact imagAxis_coe t⁻¹ (inv_pos.mpr ht)
  have hjw : Work.Kernels.jInvariantFun w = Work.Kernels.jInvariantFun w' := by
    rw [hw'def]
    exact (Work.Kernels.KernelFacts.jInvariantFun_S_smul w).symm
  have hjt : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
      = Work.Kernels.jInvariantFun τ₀ := by
    rw [hτ₀def]
    exact jInvariantFun_imagAxis_inv t ht
  have hqwn : ‖Work.Kernels.qParamFun w'‖ = Real.exp (-(2 * Real.pi * w'.im)) :=
    norm_qParamFun_eq w'
  have hqtn : ‖Work.Kernels.qParamFun τ₀‖ = Real.exp (-(2 * Real.pi * t⁻¹)) := by
    rw [norm_qParamFun_eq, hτ₀im]
  have hqw0 : Work.Kernels.qParamFun w' ≠ 0 := qParamFun_ne_zero w'
  have hEun0 : Eun ≠ 0 := by
    rw [hEun_def]
    exact Complex.exp_ne_zero _
  have hqrel : Work.Kernels.qParamFun w' * (Work.Kernels.qParamFun τ₀)⁻¹ = Eun := by
    rw [hEun_def]
    simp only [Work.Kernels.qParamFun]
    rw [← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    ring
  have hDnorm1 : ‖(Work.Kernels.qParamFun w')⁻¹‖ = Real.exp (2 * Real.pi * w'.im) := by
    rw [norm_inv, hqwn, ← Real.exp_neg]
    congr 1
    ring
  have hDnorm2 : ‖(Work.Kernels.qParamFun τ₀)⁻¹‖ = Real.exp (2 * Real.pi * t⁻¹) := by
    rw [norm_inv, hqtn, ← Real.exp_neg]
    congr 1
    ring
  have hDnorm : ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖
      = Real.exp (2 * Real.pi * w'.im) * ‖1 - Eun‖ := by
    have h1 : (Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹
        = (Work.Kernels.qParamFun w')⁻¹ * (1 - Eun) := by
      rw [← hqrel, mul_sub, mul_one, ← mul_assoc, inv_mul_cancel₀ hqw0, one_mul]
    rw [h1, norm_mul, hDnorm1]
  have hsplit : ‖Work.Kernels.jInvariantFun w
        - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖
      ≥ ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖
        - ‖Ffun w' - Ffun τ₀‖ := by
    have h1 : Work.Kernels.jInvariantFun w
          - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
        = (Ffun w' - Ffun τ₀)
          + ((Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹) := by
      rw [hjw, hjt]
      simp only [Ffun]
      ring
    rw [h1]
    have h2 := abs_norm_sub_norm_le
      ((Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹)
      (-(Ffun w' - Ffun τ₀))
    have h3 : ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖
          - ‖Ffun w' - Ffun τ₀‖
        ≤ ‖((Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹)
            - (-(Ffun w' - Ffun τ₀))‖ := by
      have h := (abs_le.mp h2).2
      rwa [norm_neg] at h
    have h4 : ((Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹)
          - (-(Ffun w' - Ffun τ₀))
        = (Ffun w' - Ffun τ₀)
          + ((Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹) := by ring
    rw [h4] at h3
    exact h3
  obtain ⟨n, hn⟩ := exists_int_abs_sub_le_half w'.re
  set ζ : ℍ := (n : ℝ) +ᵥ τ₀ with hζdef
  set X : ℂ := (w' : ℂ) - (ζ : ℂ) with hXdef
  have hζcoe : ((ζ : ℍ) : ℂ) = ((n : ℤ) : ℂ) + (τ₀ : ℂ) := by
    rw [hζdef, UpperHalfPlane.coe_vadd]
    push_cast
    ring
  have hζim : ζ.im = t⁻¹ := by
    rw [← UpperHalfPlane.coe_im, hζcoe, hτ₀coe]
    simp only [Complex.add_im, Complex.intCast_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hFζ : Ffun ζ = Ffun τ₀ := by
    rw [hζdef]
    exact Ffun_int_vadd n τ₀
  have hXre : |X.re| ≤ 1 / 2 := by
    have h1 : X.re = w'.re - (n : ℝ) := by
      rw [hXdef, hζcoe, hτ₀coe]
      simp only [Complex.sub_re, Complex.add_re, Complex.intCast_re, UpperHalfPlane.coe_re,
        Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im]
      ring
    rw [h1]
    exact hn
  have hXim : X.im = w'.im - t⁻¹ := by
    rw [hXdef, hζcoe, hτ₀coe]
    simp only [Complex.sub_im, Complex.add_im, Complex.intCast_im, UpperHalfPlane.coe_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  -- the error bound in the non-thin case
  have herr_nonthin : ‖Ffun w' - Ffun τ₀‖
      ≤ 2 * 10 ^ 7 * Real.exp (-(2 * Real.pi * min w'.im t⁻¹)) := by
    have h3 : ‖F_lift (w' : ℂ)‖ ≤ 10 ^ 7 * Real.exp (-(2 * Real.pi * w'.im)) := by
      have h := F_lift_bound (w' : ℂ) (by rw [UpperHalfPlane.coe_im]; linarith)
      rwa [UpperHalfPlane.coe_im] at h
    have h4 : ‖F_lift (τ₀ : ℂ)‖ ≤ 10 ^ 7 * Real.exp (-(2 * Real.pi * t⁻¹)) := by
      have h := F_lift_bound (τ₀ : ℂ) (by rw [UpperHalfPlane.coe_im, hτ₀im]; linarith)
      rwa [UpperHalfPlane.coe_im, hτ₀im] at h
    have h9 : 10 ^ 7 * Real.exp (-(2 * Real.pi * w'.im))
          + 10 ^ 7 * Real.exp (-(2 * Real.pi * t⁻¹))
        ≤ 2 * 10 ^ 7 * Real.exp (-(2 * Real.pi * min w'.im t⁻¹)) := by
      have h6 : Real.exp (-(2 * Real.pi * w'.im))
          ≤ Real.exp (-(2 * Real.pi * min w'.im t⁻¹)) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, min_le_left w'.im t⁻¹])
      have h7 : Real.exp (-(2 * Real.pi * t⁻¹))
          ≤ Real.exp (-(2 * Real.pi * min w'.im t⁻¹)) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, min_le_right w'.im t⁻¹])
      have ha : (10 : ℝ) ^ 7 = 10000000 := by norm_num
      rw [ha]
      linarith
    calc ‖Ffun w' - Ffun τ₀‖
        = ‖F_lift (w' : ℂ) - F_lift (τ₀ : ℂ)‖ := by
          rw [Ffun_eq_F_lift w', Ffun_eq_F_lift τ₀]
      _ ≤ ‖F_lift (w' : ℂ)‖ + ‖F_lift (τ₀ : ℂ)‖ := norm_sub_le _ _
      _ ≤ 10 ^ 7 * Real.exp (-(2 * Real.pi * w'.im))
            + 10 ^ 7 * Real.exp (-(2 * Real.pi * t⁻¹)) := add_le_add h3 h4
      _ ≤ 2 * 10 ^ 7 * Real.exp (-(2 * Real.pi * min w'.im t⁻¹)) := h9
  by_cases hthin : ‖1 - Eun‖ < 1 / 10
  · -- ### the thin case
    have hEunnorm : ‖Eun‖ = Real.exp (-(2 * Real.pi * (w'.im - t⁻¹))) := by
      have hre : (2 * Real.pi * Complex.I * ((w' : ℂ) - (τ₀ : ℂ))).re
          = -(2 * Real.pi * (w'.im - t⁻¹)) := by
        have h2pi : (2 * Real.pi * Complex.I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [hτ₀coe, h2pi]
        simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
          UpperHalfPlane.coe_im]
        ring
      rw [hEun_def, Complex.norm_exp, hre]
    have hXim_le : X.im ≤ 1 / 8 := by
      by_contra h
      push_neg at h
      have h1 : Real.exp (-(2 * Real.pi * X.im)) ≤ 1 / 2 := by
        have h6 : Real.exp (-(2 * Real.pi * X.im)) ≤ Real.exp (-(3 / 4 : ℝ)) := by
          rw [Real.exp_le_exp]
          nlinarith [Real.pi_gt_three, h]
        have h7 : Real.exp (-(3 / 4 : ℝ)) ≤ 1 / 2 := by
          have h8 : (2 : ℝ) ≤ Real.exp (3 / 4) := exp_three_quarters_ge_two
          have h9 : (Real.exp (3 / 4))⁻¹ ≤ (2 : ℝ)⁻¹ :=
            (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr h8
          rw [Real.exp_neg]
          simpa using h9
        linarith
      have h2 : ‖Eun‖ ≤ 1 / 2 := by
        rw [hEunnorm, ← hXim]
        exact h1
      have h3 := abs_norm_sub_norm_le Eun 1
      rw [norm_one, norm_sub_rev] at h3
      have h4 : (1 / 2 : ℝ) ≤ ‖1 - Eun‖ := by
        have h5 : |‖Eun‖ - 1| = 1 - ‖Eun‖ := by
          rw [abs_of_nonpos (by linarith)]
          ring
        linarith [h3, h2, h5]
      linarith [hthin, h4]
    have hXim_ge : -(1 / 8) ≤ X.im := by
      by_contra h
      push_neg at h
      have h1 : (2 : ℝ) ≤ Real.exp (-(2 * Real.pi * X.im)) := by
        have h6 : Real.exp (3 / 4) ≤ Real.exp (-(2 * Real.pi * X.im)) := by
          rw [Real.exp_le_exp]
          nlinarith [Real.pi_gt_three, h]
        linarith [exp_three_quarters_ge_two, h6]
      have h2 : 2 ≤ ‖Eun‖ := by
        rw [hEunnorm, ← hXim]
        exact h1
      have h3 := abs_norm_sub_norm_le Eun 1
      rw [norm_one, norm_sub_rev] at h3
      have h4 : (1 : ℝ) ≤ ‖1 - Eun‖ := by
        have h5 : |‖Eun‖ - 1| = ‖Eun‖ - 1 := by
          rw [abs_of_nonneg (by linarith)]
        linarith [h3, h2, h5]
      linarith [hthin, h4]
    have hXimabs : |X.im| ≤ 1 / 8 := abs_le.mpr ⟨hXim_ge, hXim_le⟩
    have hB15 : 15 / 8 ≤ t⁻¹ := by
      have h7 : t⁻¹ = w'.im - X.im := by rw [hXim]; ring
      rw [h7]
      linarith [hA2, hXim_le]
    have hEuninv : Complex.exp (-(2 * Real.pi * Complex.I * X)) = Eun⁻¹ := by
      have h1 : -(2 * Real.pi * Complex.I * X)
          = -(2 * Real.pi * Complex.I * ((w' : ℂ) - (τ₀ : ℂ)))
            + ((n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hXdef, hζcoe]
        ring
      rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one, hEun_def,
        ← Complex.exp_neg]
    have h2 : ‖Eun⁻¹ - 1‖ ≥ 2 * ‖X‖ := by
      have h3 := norm_exp_neg_two_pi_I_sub_one_ge X hXre hXimabs
      rwa [hEuninv] at h3
    have h4 : ‖1 - Eun‖ = ‖Eun‖ * ‖Eun⁻¹ - 1‖ := by
      have h5 : 1 - Eun = Eun * (Eun⁻¹ - 1) := by
        rw [mul_sub, mul_one, mul_inv_cancel₀ hEun0]
      rw [h5, norm_mul]
    have h6 : ‖Eun‖ * (2 * ‖X‖) ≤ ‖1 - Eun‖ := by
      rw [h4]
      exact mul_le_mul_of_nonneg_left h2 (norm_nonneg Eun)
    have hDthin : 2 * Real.exp (2 * Real.pi * t⁻¹) * ‖X‖
        ≤ ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖ := by
      rw [hDnorm]
      have h7 : Real.exp (2 * Real.pi * w'.im) * (‖Eun‖ * (2 * ‖X‖))
          ≤ Real.exp (2 * Real.pi * w'.im) * ‖1 - Eun‖ :=
        mul_le_mul_of_nonneg_left h6 (Real.exp_pos _).le
      have h8 : Real.exp (2 * Real.pi * w'.im) * (‖Eun‖ * (2 * ‖X‖))
          = 2 * Real.exp (2 * Real.pi * t⁻¹) * ‖X‖ := by
        have h9 : Real.exp (2 * Real.pi * w'.im) * Real.exp (-(2 * Real.pi * X.im))
            = Real.exp (2 * Real.pi * t⁻¹) := by
          rw [← Real.exp_add]
          congr 1
          rw [hXim]
          ring
        rw [hEunnorm, ← hXim, ← h9]
        ring
      linarith [h7, h8]
    have herr_thin : ‖Ffun w' - Ffun τ₀‖
        ≤ 2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * (15 / 8))) * ‖X‖ := by
      have hseg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
          3 / 2 ≤ ((ζ : ℂ) + s • ((w' : ℂ) - (ζ : ℂ))).im := by
        intro s hs
        have h1 : ((ζ : ℂ) + s • ((w' : ℂ) - (ζ : ℂ))).im = (1 - s) * ζ.im + s * w'.im := by
          simp only [Complex.add_im, Complex.smul_im, Complex.sub_im, UpperHalfPlane.coe_im]
          ring
        rw [h1]
        have h2 : 15 / 8 ≤ ζ.im := by
          rw [hζim]
          exact hB15
        nlinarith [hs.1, hs.2, h2, hA2]
      have hdiff := F_lift_diff_bound (w' : ℂ) (ζ : ℂ) hseg
      simp only [UpperHalfPlane.coe_im, hζim] at hdiff
      have h2 : 15 / 8 ≤ min w'.im t⁻¹ := le_min (by linarith) hB15
      have h3 : Real.exp (-(2 * Real.pi * min w'.im t⁻¹))
          ≤ Real.exp (-(2 * Real.pi * (15 / 8))) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, h2])
      have h4 : Ffun w' - Ffun τ₀ = F_lift (w' : ℂ) - F_lift (ζ : ℂ) := by
        rw [Ffun_eq_F_lift w', ← hFζ, Ffun_eq_F_lift ζ]
      have h5 : ‖(w' : ℂ) - (ζ : ℂ)‖ = ‖X‖ := by rw [← hXdef]
      rw [h4]
      calc ‖F_lift (w' : ℂ) - F_lift (ζ : ℂ)‖
          ≤ 2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * min w'.im t⁻¹))
              * ‖(w' : ℂ) - (ζ : ℂ)‖ := hdiff
        _ ≤ 2 * 10 ^ 9 * Real.exp (-(2 * Real.pi * (15 / 8))) * ‖X‖ := by
            have hz : (0 : ℝ) ≤ 2 * 10 ^ 9 := by norm_num
            have hN : 0 ≤ ‖X‖ := norm_nonneg _
            have h6 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hz) hN
            rw [h5] at h6
            exact h6
    have hmain := thin_real (A := w'.im) (B := t⁻¹) (err := ‖Ffun w' - Ffun τ₀‖)
      (D := ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖) (X := ‖X‖)
      hA2 hB15 (norm_nonneg X) hDthin herr_thin
    have hfin : (1 / 10) * ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖
        ≤ ‖Work.Kernels.jInvariantFun w
            - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by
      have h2 : ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖ / 2
          ≤ ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖
            - ‖Ffun w' - Ffun τ₀‖ := by
        linarith [hmain]
      linarith [hsplit, h2,
        norm_nonneg ((Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹)]
    calc 1 / 10 * Real.exp (2 * Real.pi * w'.im) * ‖1 - Eun‖
        = 1 / 10 * ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖ := by
          rw [hDnorm]; ring
      _ ≤ ‖Work.Kernels.jInvariantFun w
            - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := hfin
  · -- ### the non-thin case
    push_neg at hthin
    have hD1 : Real.exp (2 * Real.pi * w'.im) * (1 / 10)
        ≤ ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖ := by
      rw [hDnorm]
      exact mul_le_mul_of_nonneg_left hthin (Real.exp_pos _).le
    have hD2 : |Real.exp (2 * Real.pi * w'.im) - Real.exp (2 * Real.pi * t⁻¹)|
        ≤ ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖ := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · have h := abs_norm_sub_norm_le (Work.Kernels.qParamFun τ₀)⁻¹
          (Work.Kernels.qParamFun w')⁻¹
        rw [hDnorm2, hDnorm1, norm_sub_rev, abs_sub_comm] at h
        exact (abs_le.mp h).1
      · have h := abs_norm_sub_norm_le (Work.Kernels.qParamFun w')⁻¹
          (Work.Kernels.qParamFun τ₀)⁻¹
        rw [hDnorm1, hDnorm2] at h
        exact (abs_le.mp h).2
    have hmain := nonthin_real (A := w'.im) (B := t⁻¹) (err := ‖Ffun w' - Ffun τ₀‖)
      (D := ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖)
      hA2 hBge hD1 hD2 herr_nonthin
    have hfin : (1 / 10) * ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖
        ≤ ‖Work.Kernels.jInvariantFun w
            - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by
      have h2 : ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖ / 2
          ≤ ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖
            - ‖Ffun w' - Ffun τ₀‖ := by
        linarith [hmain]
      linarith [hsplit, h2,
        norm_nonneg ((Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹)]
    calc 1 / 10 * Real.exp (2 * Real.pi * w'.im) * ‖1 - Eun‖
        = 1 / 10 * ‖(Work.Kernels.qParamFun w')⁻¹ - (Work.Kernels.qParamFun τ₀)⁻¹‖ := by
          rw [hDnorm]; ring
      _ ≤ ‖Work.Kernels.jInvariantFun w
            - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := hfin

end Work.Asymptotics

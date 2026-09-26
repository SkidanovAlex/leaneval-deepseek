import Mathlib
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Residues.E4FunSecondOrder
import Submission.Work.Residues.QExpansionTail
import Submission.Work.Modular.E4_qExpansion_coeff

/-!
# The bound `‖E₄‖ ≤ 3/2` on the half-plane `Im τ ≥ 1`

The weight-four Eisenstein series has the `q`-expansion `E₄ = 1 + 240 ∑_{n ≥ 1} σ₃(n) qⁿ`
with `q = exp (2 π i τ)`.  On `Im τ ≥ 1` one has `‖q‖ ≤ e^{-2π} ≤ 1/512`, and the
elementary comparison `(m+1)⁴ ≤ 16^m` turns the tail `240 ∑_{m ≥ 0} (m+1)⁴ ‖q‖^{m+1}` into
the geometric series `240 ‖q‖ (1 - 16 ‖q‖)⁻¹ ≤ 240 · (1/496) ≤ 1/2`.  Hence
`‖E₄ τ - 1‖ ≤ 1/2` and therefore `‖E₄ τ‖ ≤ 3/2`.
-/

namespace Work.Asymptotics

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm Manifold Bundle

noncomputable section

/-! ## Numerical input: `e^{-2π} ≤ 1/512` -/

/-- `e^{-2π} ≤ 1/512`.  (Since `2π > 6.28` and `e^{6.28} = e⁶ · e^{0.28} > 400 · 1.28 = 512`.) -/
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

/-- `‖qParamFun τ‖ ≤ 1/512` for `Im τ ≥ 1`. -/
lemma norm_qParamFun_le_inv512 {τ : ℍ} (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.qParamFun τ‖ ≤ 1 / 512 := by
  rw [norm_qParamFun]
  have h1 : Real.exp (-(2 * Real.pi * τ.im)) ≤ Real.exp (-(2 * Real.pi)) := by
    rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hτ]
  linarith [exp_neg_two_pi_le_inv512]

/-! ## The elementary tail estimate -/

/-- `(m + 1) ^ 4 ≤ 16 ^ m` for every `m : ℕ`. -/
private lemma succ_pow_four_le_16_pow (m : ℕ) : ((m : ℝ) + 1) ^ 4 ≤ 16 ^ m := by
  induction m with
  | zero => norm_num
  | succ n ih =>
    push_cast
    have hstep : (n : ℝ) + 1 + 1 ≤ 2 * ((n : ℝ) + 1) := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    calc ((n : ℝ) + 1 + 1) ^ 4 ≤ (2 * ((n : ℝ) + 1)) ^ 4 :=
          pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1 + 1) hstep 4
      _ = 16 * ((n : ℝ) + 1) ^ 4 := by ring
      _ ≤ 16 * 16 ^ n := by linarith
      _ = 16 ^ (n + 1) := by rw [pow_succ]; ring

/-- Termwise comparison of the shifted fourth-power series with the geometric majorant. -/
private lemma succ_pow_four_mul_shift_le_majorant (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    ((m : ℝ) + 1) ^ 4 * x ^ (m + 1) ≤ x * (16 * x) ^ m := by
  have h1 : ((m : ℝ) + 1) ^ 4 ≤ 16 ^ m := succ_pow_four_le_16_pow m
  have h2 : ((m : ℝ) + 1) ^ 4 * x ^ (m + 1) ≤ 16 ^ m * x ^ (m + 1) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  have hR : x * (16 * x) ^ m = 16 ^ m * x ^ (m + 1) := by
    rw [mul_pow, pow_succ']; ring
  rw [hR]
  exact h2

/-- Summability of the shifted fourth-power series for `0 ≤ x ≤ 1/512`. -/
private lemma summable_succ_pow_four_mul_shift (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1 / 512) :
    Summable (fun m : ℕ => ((m : ℝ) + 1) ^ 4 * x ^ (m + 1)) := by
  have h16 : ‖(16 * x : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  refine Summable.of_nonneg_of_le (fun m => by positivity)
    (fun m => succ_pow_four_mul_shift_le_majorant x hx m) ?_
  exact (summable_geometric_of_norm_lt_one h16).mul_left x

/-- `∑_{m ≥ 0} (m + 1)⁴ x^{m+1} ≤ 1/496` for `0 ≤ x ≤ 1/512`. -/
private lemma tsum_succ_pow_four_mul_shift_le (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1 / 512) :
    ∑' m : ℕ, ((m : ℝ) + 1) ^ 4 * x ^ (m + 1) ≤ 1 / 496 := by
  have h16 : ‖(16 * x : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hmaj : Summable (fun m : ℕ => x * (16 * x) ^ m) :=
    (summable_geometric_of_norm_lt_one h16).mul_left x
  have htsum : ∑' m : ℕ, ((m : ℝ) + 1) ^ 4 * x ^ (m + 1) ≤ x * (1 - 16 * x)⁻¹ := by
    calc ∑' m : ℕ, ((m : ℝ) + 1) ^ 4 * x ^ (m + 1)
        ≤ ∑' m : ℕ, x * (16 * x) ^ m :=
          Summable.tsum_le_tsum (fun m => succ_pow_four_mul_shift_le_majorant x hx m)
            (summable_succ_pow_four_mul_shift x hx hx1) hmaj
      _ = x * (1 - 16 * x)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_norm_lt_one h16]
  have hpos : 0 < 1 - 16 * x := by linarith
  have h31 : (31 / 32 : ℝ) ≤ 1 - 16 * x := by linarith
  have hinv : (1 - 16 * x)⁻¹ ≤ 32 / 31 := by
    calc (1 - 16 * x)⁻¹ ≤ (31 / 32 : ℝ)⁻¹ :=
          (inv_le_inv₀ hpos (by norm_num)).mpr h31
      _ = 32 / 31 := by norm_num
  have hbound : x * (1 - 16 * x)⁻¹ ≤ 1 / 496 := by
    calc x * (1 - 16 * x)⁻¹ ≤ (1 / 512) * (32 / 31) :=
          mul_le_mul hx1 hinv (inv_nonneg.mpr hpos.le) (by norm_num)
      _ = 1 / 496 := by norm_num
  linarith

/-! ## The `q`-expansion of `E₄` -/

/-- The `(m+1)`-st `q`-expansion coefficient of `E₄` is `240 σ₃(m+1)`, of modulus `≤ 240 (m+1)⁴`. -/
private lemma E4_coeff_succ_le (m : ℕ) :
    ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (m + 1)‖ ≤ 240 * ((m : ℝ) + 1) ^ 4 := by
  have hm0 : m + 1 ≠ 0 := by omega
  rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl,
    Work.Modular.E4_qExpansion_coeff (m + 1), if_neg hm0]
  have hσ : (ArithmeticFunction.sigma 3 (m + 1) : ℝ) ≤ ((m : ℝ) + 1) ^ 4 := by
    have h' : ArithmeticFunction.sigma 3 (m + 1) ≤ (m + 1) ^ 4 := by
      simpa using ArithmeticFunction.sigma_le_pow_succ 3 (m + 1)
    have h'' : (((m + 1) ^ 4 : ℕ) : ℝ) = ((m : ℝ) + 1) ^ 4 := by push_cast; ring
    rw [← h'']
    exact_mod_cast h'
  rw [norm_mul, Complex.norm_ofNat, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hσ (by norm_num)

/-- The `q`-expansion of `E₄` isolated at the constant term: `E₄ - 1` is a series in `q`. -/
private lemma E4_hasSum_shift (w : ℍ) :
    HasSum (fun n : ℕ => (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 1) •
      Work.Kernels.qParamFun w ^ (n + 1)) (Work.Kernels.E4Fun w - 1) := by
  have hper : Function.Periodic (Work.Kernels.E4Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E4Fun := ModularForm.holo' ModularForm.E₄
  have hbdd : UpperHalfPlane.IsBoundedAtImInfty Work.Kernels.E4Fun :=
    ModularFormClass.bdd_at_infty ModularForm.E₄
  have hs := UpperHalfPlane.hasSum_qExpansion (h := 1) (f := Work.Kernels.E4Fun)
    one_pos hper hhol hbdd w
  have hs1 := (hasSum_nat_add_iff' 1).mpr hs
  have hc0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 0 = 1 := by
    rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl, Work.Modular.E4_qExpansion_coeff]
    norm_num
  have hsum1 : (∑ i ∈ Finset.range 1,
      (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff i
        • Function.Periodic.qParam 1 (w : ℂ) ^ i) = 1 := by
    rw [Finset.sum_range_one, hc0, pow_zero, smul_eq_mul, mul_one]
  rw [hsum1] at hs1
  have hq_eq : Function.Periodic.qParam 1 (w : ℂ) = Work.Kernels.qParamFun w := by
    simp [Function.Periodic.qParam, Work.Kernels.qParamFun]
  rw [hq_eq] at hs1
  exact hs1

/-! ## The main theorem -/

theorem E4Fun_upper_half (τ : UpperHalfPlane) (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.E4Fun τ‖ ≤ 3 / 2 := by
  have hx : ‖Work.Kernels.qParamFun τ‖ ≤ 1 / 512 := norm_qParamFun_le_inv512 hτ
  have hx0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hterm : ∀ n : ℕ,
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 1) •
        Work.Kernels.qParamFun τ ^ (n + 1)‖
      ≤ 240 * (((n : ℝ) + 1) ^ 4 * ‖Work.Kernels.qParamFun τ‖ ^ (n + 1)) := by
    intro n
    rw [smul_eq_mul, norm_mul, norm_pow]
    have hc := E4_coeff_succ_le n
    have hxnn : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ (n + 1) := by positivity
    calc ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 1)‖ *
          ‖Work.Kernels.qParamFun τ‖ ^ (n + 1)
        ≤ (240 * ((n : ℝ) + 1) ^ 4) * ‖Work.Kernels.qParamFun τ‖ ^ (n + 1) :=
          mul_le_mul_of_nonneg_right hc hxnn
      _ = 240 * (((n : ℝ) + 1) ^ 4 * ‖Work.Kernels.qParamFun τ‖ ^ (n + 1)) := by ring
  have hmaj : Summable (fun n : ℕ =>
      240 * (((n : ℝ) + 1) ^ 4 * ‖Work.Kernels.qParamFun τ‖ ^ (n + 1))) :=
    (summable_succ_pow_four_mul_shift _ hx0 hx).mul_left 240
  have hsumm : Summable (fun n : ℕ =>
      ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 1) •
        Work.Kernels.qParamFun τ ^ (n + 1)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmaj
  have hsub : ‖Work.Kernels.E4Fun τ - 1‖ ≤ 1 / 2 := by
    calc ‖Work.Kernels.E4Fun τ - 1‖
        = ‖∑' n : ℕ, (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 1) •
            Work.Kernels.qParamFun τ ^ (n + 1)‖ := by rw [(E4_hasSum_shift τ).tsum_eq]
      _ ≤ ∑' n : ℕ, ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff (n + 1) •
            Work.Kernels.qParamFun τ ^ (n + 1)‖ := norm_tsum_le_tsum_norm hsumm
      _ ≤ ∑' n : ℕ, 240 * (((n : ℝ) + 1) ^ 4 * ‖Work.Kernels.qParamFun τ‖ ^ (n + 1)) :=
          Summable.tsum_le_tsum hterm hsumm hmaj
      _ = 240 * ∑' n : ℕ, ((n : ℝ) + 1) ^ 4 * ‖Work.Kernels.qParamFun τ‖ ^ (n + 1) :=
          tsum_mul_left
      _ ≤ 240 * (1 / 496) :=
          mul_le_mul_of_nonneg_left (tsum_succ_pow_four_mul_shift_le _ hx0 hx) (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  calc ‖Work.Kernels.E4Fun τ‖
      = ‖(Work.Kernels.E4Fun τ - 1) + 1‖ := by
        rw [show (Work.Kernels.E4Fun τ - 1) + 1 = Work.Kernels.E4Fun τ by ring]
    _ ≤ ‖Work.Kernels.E4Fun τ - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 1 / 2 + 1 := by rw [norm_one]; linarith
    _ = 3 / 2 := by norm_num

end

end Work.Asymptotics

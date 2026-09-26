import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.psi_second_order
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.CuspL_eq
import Submission.Work.Asymptotics.jInvariantFun_cusp_second
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.FunnelNumerics.E4_funnel_bounds
import Submission.Work.Kernels.ModerateGrowth

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Manifold Bundle

noncomputable section

set_option maxHeartbeats 4000000

/-!
# First-order cusp expansion of the `E(z)¹`-combination `E1combo8`

The target identity is the funnel bound
`E1combo8 ℓ τ = (737280·Λ + 122880)·q(τ) + O((scale τ)^N ‖q(τ)‖²)`, with
`Λ = πiτ + cuspC ℓ` and `q = qParamFun`.  Everything is deduced from

* the second-order expansions of `ψ₂`, `ψ₄` (`KhatE1Core.psi_second_order`),
* the expansion `j = q⁻¹ + 744 + O(q)` (`jFunnelBound` below),
* the second-order expansion of the ratio `E₆/E₄` (`E6DivE4SecondOrder` below),
* the one-term expansion `E₄ = 1 + 240 q + O(q²)` (`E4Fun_two_term`).
-/

/-! ## The linear cusp term `Λ` and the `j`-invariant -/

/-- The linear cusp term `Λ = πiτ + cuspC ℓ`. -/
private noncomputable def Lam (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) : ℂ :=
  (Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ

/-- `‖Λ‖ ≤ (π + 4) · scale τ`. -/
private lemma norm_Lam_le (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    ‖Lam ℓ τ‖ ≤ (Real.pi + 4) * Work.Kernels.scale τ := by
  have hc : Work.Asymptotics.Compact.cuspC ℓ = 4 * (Real.log 2 : ℂ) :=
    Work.Asymptotics.CuspL_eq ℓ
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hπ : ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ ≤ Real.pi * Work.Kernels.scale τ := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have h := Work.Kernels.coe_norm_le_scale τ
    nlinarith [Real.pi_pos]
  have hlog : ‖(4 : ℂ) * (Real.log 2 : ℂ)‖ ≤ 4 := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
    have h1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
    linarith
  have hsc := Work.Kernels.one_le_scale τ
  rw [Lam, hc]
  calc ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ) + 4 * (Real.log 2 : ℂ)‖
      ≤ ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ + ‖(4 : ℂ) * (Real.log 2 : ℂ)‖ := norm_add_le _ _
    _ ≤ Real.pi * Work.Kernels.scale τ + 4 := add_le_add hπ hlog
    _ ≤ (Real.pi + 4) * Work.Kernels.scale τ := by nlinarith [Real.pi_pos, hsc]

/-- **The `j`-invariant on the funnel:** `j = q⁻¹ + 744 + O(‖q‖)`. -/
private lemma jFunnelBound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Kernels.jInvariantFun τ - (Work.Kernels.qParamFun τ)⁻¹ - 744‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ := by
  obtain ⟨Cr, hCr, hE4c⟩ := Work.Asymptotics.E4cube_cusp_second
  obtain ⟨Cs, hCs, hinvΔ⟩ := Work.Asymptotics.cusp_invDelta
  refine ⟨17280 + 721 * Cs + (25 + Cs) * Cr + 1, by positivity, fun τ hτ => ?_⟩
  have him : (1 : ℝ) ≤ τ.im := Work.Asymptotics.Funnel.im_one hτ
  set q : ℂ := Work.Kernels.qParamFun τ with hqdef
  set E : ℂ := Work.Residues.Ept τ with hEdef
  have hqE : q = E ^ 2 := by
    rw [hqdef, hEdef, Work.Kernels.qParamFun, Work.Residues.Ept, sq, ← Complex.exp_add]
    congr 1; ring
  have hqnorm : ‖q‖ = ‖E‖ ^ 2 := by rw [hqE, norm_pow]
  have hqle1 : ‖q‖ ≤ 1 := by
    rw [hqnorm]
    have h : ‖E‖ < 1 := by rw [hEdef]; exact Work.Residues.norm_Ept_lt_one τ
    nlinarith [norm_nonneg E]
  have hEinv : (Work.Residues.Ept τ)⁻¹ ^ 2 = q⁻¹ := by
    rw [← hEdef, hqE, inv_pow]
  have hq_ne : q ≠ 0 := by
    rw [hqE]; exact pow_ne_zero 2 (by rw [hEdef]; exact Work.Residues.Ept_ne_zero τ)
  set r : ℂ := Work.Kernels.E4Fun τ ^ 3 - 1 - 720 * q with hrdef
  set s : ℂ := (Work.Kernels.DeltaFun τ)⁻¹ - (q⁻¹ + 24) with hsdef
  have hr_bound : ‖r‖ ≤ Cr * ‖q‖ ^ 2 := by rw [hrdef, hqdef]; exact hE4c τ him
  have hs_bound : ‖s‖ ≤ Cs * ‖q‖ := by
    have h := hinvΔ τ him
    rw [show (Work.Residues.Ept τ)⁻¹ ^ 2 = q⁻¹ from hEinv] at h
    rw [show ‖Work.Residues.Ept τ‖ ^ 2 = ‖q‖ from by rw [← hEdef, hqnorm]] at h
    rw [← hsdef] at h
    exact h
  have hjr : Work.Kernels.jInvariantFun τ
      = Work.Kernels.E4Fun τ ^ 3 * (Work.Kernels.DeltaFun τ)⁻¹ := by
    rw [Work.Kernels.jInvariantFun, div_eq_mul_inv]
  have hE4 : Work.Kernels.E4Fun τ ^ 3 = 1 + 720 * q + r := by rw [hrdef]; ring
  have hDinv : (Work.Kernels.DeltaFun τ)⁻¹ = q⁻¹ + 24 + s := by rw [hsdef]; ring
  have hid : (1 + 720 * q + r) * (q⁻¹ + 24 + s) - q⁻¹ - 744
      = 17280 * q + s * (1 + 720 * q) + r * (q⁻¹ + 24 + s) := by
    field_simp
    ring
  have hmain : Work.Kernels.jInvariantFun τ - (Work.Residues.Ept τ)⁻¹ ^ 2 - 744
      = 17280 * q + s * (1 + 720 * q) + r * (q⁻¹ + 24 + s) := by
    rw [hjr, hE4, hDinv, hEinv]
    exact hid
  rw [← hEinv, hmain]
  have ht0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg _
  have h720 : ‖(1 : ℂ) + 720 * q‖ ≤ 1 + 720 * ‖q‖ := by
    calc ‖(1 : ℂ) + 720 * q‖ ≤ ‖(1 : ℂ)‖ + ‖(720 : ℂ) * q‖ := norm_add_le _ _
      _ = 1 + 720 * ‖q‖ := by rw [norm_mul, Complex.norm_ofNat]; norm_num
  have hs2 : ‖s * (1 + 720 * q)‖ ≤ Cs * ‖q‖ * (1 + 720 * ‖q‖) := by
    rw [norm_mul]
    exact mul_le_mul hs_bound h720 (norm_nonneg _) (by positivity)
  have hqs : ‖q⁻¹ + 24 + s‖ ≤ ‖q‖⁻¹ + 24 + Cs * ‖q‖ := by
    have h1 : ‖q⁻¹ + 24 + s‖ ≤ ‖q⁻¹ + 24‖ + ‖s‖ := norm_add_le _ _
    have h2 : ‖q⁻¹ + 24‖ ≤ ‖q⁻¹‖ + ‖(24 : ℂ)‖ := norm_add_le _ _
    rw [norm_inv, Complex.norm_ofNat] at h2
    linarith [h1, h2, hs_bound]
  have hr3 : ‖r * (q⁻¹ + 24 + s)‖ ≤ Cr * ‖q‖ ^ 2 * (‖q‖⁻¹ + 24 + Cs * ‖q‖) := by
    rw [norm_mul]
    exact mul_le_mul hr_bound hqs (norm_nonneg _) (by positivity)
  have hsum : ‖17280 * q + s * (1 + 720 * q) + r * (q⁻¹ + 24 + s)‖
      ≤ 17280 * ‖q‖ + Cs * ‖q‖ * (1 + 720 * ‖q‖)
        + Cr * ‖q‖ ^ 2 * (‖q‖⁻¹ + 24 + Cs * ‖q‖) := by
    have h1 : ‖(17280 : ℂ) * q‖ = 17280 * ‖q‖ := by rw [norm_mul, Complex.norm_ofNat]
    have h2 : ‖17280 * q + s * (1 + 720 * q) + r * (q⁻¹ + 24 + s)‖
        ≤ ‖17280 * q‖ + ‖s * (1 + 720 * q)‖ + ‖r * (q⁻¹ + 24 + s)‖ := by
      have ha := norm_add_le (17280 * q + s * (1 + 720 * q)) (r * (q⁻¹ + 24 + s))
      have hb := norm_add_le ((17280 : ℂ) * q) (s * (1 + 720 * q))
      linarith
    rw [h1] at h2
    linarith [h2, hs2, hr3]
  have hfinal : 17280 * ‖q‖ + Cs * ‖q‖ * (1 + 720 * ‖q‖)
        + Cr * ‖q‖ ^ 2 * (‖q‖⁻¹ + 24 + Cs * ‖q‖)
      ≤ (17280 + 721 * Cs + (25 + Cs) * Cr) * ‖q‖ := by
    have h6 : ‖q‖ ^ 2 * ‖q‖⁻¹ = ‖q‖ := by
      rcases eq_or_ne ‖q‖ 0 with h | h
      · rw [h]; ring
      · rw [pow_two, mul_assoc, mul_inv_cancel₀ h, mul_one]
    have h2 : ‖q‖ ^ 2 ≤ ‖q‖ := by
      calc ‖q‖ ^ 2 = ‖q‖ * ‖q‖ := by ring
        _ ≤ ‖q‖ * 1 := mul_le_mul_of_nonneg_left hqle1 ht0
        _ = ‖q‖ := by ring
    have h3 : ‖q‖ ^ 3 ≤ ‖q‖ := by
      calc ‖q‖ ^ 3 = ‖q‖ ^ 2 * ‖q‖ := by ring
        _ ≤ ‖q‖ * ‖q‖ := mul_le_mul_of_nonneg_right h2 ht0
        _ = ‖q‖ ^ 2 := by ring
        _ ≤ ‖q‖ := h2
    nlinarith [h6, h2, h3, ht0, hCs.le, hCr.le, norm_nonneg q,
      mul_nonneg hCs.le hCr.le]
  calc ‖17280 * q + s * (1 + 720 * q) + r * (q⁻¹ + 24 + s)‖
      ≤ 17280 * ‖q‖ + Cs * ‖q‖ * (1 + 720 * ‖q‖)
        + Cr * ‖q‖ ^ 2 * (‖q‖⁻¹ + 24 + Cs * ‖q‖) := hsum
    _ ≤ (17280 + 721 * Cs + (25 + Cs) * Cr) * ‖q‖ := hfinal
    _ ≤ (17280 + 721 * Cs + (25 + Cs) * Cr + 1) * ‖q‖ := by
        have := norm_nonneg q
        nlinarith

/-! ## Three-term `q`-expansions of `E₄`, `E₆` (needed for `E₆/E₄`) -/

/-- `qExpansion_tail_bound` restated with the explicit `qParamFun`. -/
private lemma qExp_tail (r : ℕ) {f : UpperHalfPlane → ℂ}
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1)
    (hhol : MDiff f) (hbdd : UpperHalfPlane.IsBoundedAtImInfty f)
    (M : ℝ) (K : ℕ) (hM : 0 ≤ M)
    (ha : ∀ m : ℕ, r ≤ m → ‖(PowerSeries.coeff m) (UpperHalfPlane.qExpansion 1 f)‖ ≤ M * (m:ℝ)^K) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖f τ - ∑ m ∈ Finset.range r,
          (PowerSeries.coeff m) (UpperHalfPlane.qExpansion 1 f) * Work.Kernels.qParamFun τ ^ m‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ r := by
  obtain ⟨C, hC, h⟩ := Work.Residues.qExpansion_tail_bound r hper hhol hbdd M K hM ha
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have hq : Function.Periodic.qParam 1 (τ : ℂ) = Work.Kernels.qParamFun τ := by
    simp [Work.Kernels.qParamFun, Function.Periodic.qParam]
  simpa [hq] using h τ hτ

private lemma E4_coeff_bound3 : ∀ m : ℕ, 4 ≤ m →
    ‖(PowerSeries.coeff m) (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun)‖ ≤ 240 * (m:ℝ)^4 := by
  intro m hm
  have hm0 : m ≠ 0 := by omega
  have hc : (PowerSeries.coeff m) (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun)
      = (240 : ℂ) * ((ArithmeticFunction.sigma 3 m : ℕ) : ℂ) := by
    rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl,
      Work.Modular.E4_qExpansion_coeff, if_neg hm0]
  have hsig : (ArithmeticFunction.sigma 3 m : ℝ) ≤ (m:ℝ)^4 := by
    have h' : ArithmeticFunction.sigma 3 m ≤ m^4 := by
      simpa using ArithmeticFunction.sigma_le_pow_succ 3 m
    exact_mod_cast h'
  rw [hc, norm_mul, Complex.norm_ofNat, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hsig (by norm_num)

private lemma E6_coeff_bound3 : ∀ m : ℕ, 4 ≤ m →
    ‖(PowerSeries.coeff m) (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun)‖ ≤ 504 * (m:ℝ)^6 := by
  intro m hm
  have hm0 : m ≠ 0 := by omega
  have hc : (PowerSeries.coeff m) (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun)
      = (-504 : ℂ) * ((ArithmeticFunction.sigma 5 m : ℕ) : ℂ) := by
    rw [show Work.Kernels.E6Fun = Work.Modular.E6 from rfl,
      Work.Modular.E6_qExpansion_coeff, if_neg hm0]
  have hsig : (ArithmeticFunction.sigma 5 m : ℝ) ≤ (m:ℝ)^6 := by
    have h' : ArithmeticFunction.sigma 5 m ≤ m^6 := by
      simpa using ArithmeticFunction.sigma_le_pow_succ 5 m
    exact_mod_cast h'
  rw [hc, norm_mul, show ‖(-504 : ℂ)‖ = (504:ℝ) from by norm_num, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hsig (by norm_num)

/-- `E₄ = 1 + 240 q + 2160 q² + O(‖q‖³)` on `{Im τ ≥ 1}`. -/
private lemma E4_three_term :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.E4Fun τ - (1 + 240 * Work.Kernels.qParamFun τ
          + 2160 * Work.Kernels.qParamFun τ ^ 2)‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  have hper : Function.Periodic (Work.Kernels.E4Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E4Fun := ModularForm.holo' ModularForm.E₄
  have hbdd : IsBoundedAtImInfty Work.Kernels.E4Fun := ModularFormClass.bdd_at_infty ModularForm.E₄
  obtain ⟨C, hC, h⟩ := qExp_tail 4 hper hhol hbdd 240 4 (by norm_num) E4_coeff_bound3
  refine ⟨C + 6720 + 1, by positivity, fun τ hτ => ?_⟩
  have h' := h τ hτ
  have hq1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := Work.Asymptotics.norm_qParamFun_le_one τ hτ
  have hq0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hsum : (∑ m ∈ Finset.range 4,
        (PowerSeries.coeff m) (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun)
          * Work.Kernels.qParamFun τ ^ m)
      = 1 + 240 * Work.Kernels.qParamFun τ + 2160 * Work.Kernels.qParamFun τ ^ 2
        + 6720 * Work.Kernels.qParamFun τ ^ 3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : (PowerSeries.coeff 0) (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun) = 1 := by
      rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl, Work.Modular.E4_qExpansion_coeff]
      simp
    have h1 : (PowerSeries.coeff 1) (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun) = 240 := by
      rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl,
        Work.Modular.E4_qExpansion_coeff 1, if_neg (by norm_num : (1:ℕ) ≠ 0)]
      norm_num [ArithmeticFunction.sigma]
    have h2 : (PowerSeries.coeff 2) (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun) = 2160 := by
      rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl,
        Work.Modular.E4_qExpansion_coeff 2, if_neg (by norm_num : (2:ℕ) ≠ 0)]
      norm_num [ArithmeticFunction.sigma]
    have h3 : (PowerSeries.coeff 3) (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun) = 6720 := by
      rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl,
        Work.Modular.E4_qExpansion_coeff 3, if_neg (by norm_num : (3:ℕ) ≠ 0)]
      norm_num [ArithmeticFunction.sigma]
    rw [h0, h1, h2, h3]; ring
  rw [hsum] at h'
  have hsplit : Work.Kernels.E4Fun τ - (1 + 240 * Work.Kernels.qParamFun τ
        + 2160 * Work.Kernels.qParamFun τ ^ 2)
      = (Work.Kernels.E4Fun τ - (1 + 240 * Work.Kernels.qParamFun τ
            + 2160 * Work.Kernels.qParamFun τ ^ 2 + 6720 * Work.Kernels.qParamFun τ ^ 3))
        + 6720 * Work.Kernels.qParamFun τ ^ 3 := by ring
  rw [hsplit]
  have h4 : ‖(6720 : ℂ) * Work.Kernels.qParamFun τ ^ 3‖
      = 6720 * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]
  have hb1 : ‖Work.Kernels.E4Fun τ - (1 + 240 * Work.Kernels.qParamFun τ
            + 2160 * Work.Kernels.qParamFun τ ^ 2 + 6720 * Work.Kernels.qParamFun τ ^ 3)‖
      ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
    refine le_trans h' (mul_le_mul_of_nonneg_left ?_ hC.le)
    exact pow_le_pow_of_le_one hq0 hq1 (by norm_num)
  have hq3 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ 3 := by positivity
  calc ‖(Work.Kernels.E4Fun τ - (1 + 240 * Work.Kernels.qParamFun τ
            + 2160 * Work.Kernels.qParamFun τ ^ 2 + 6720 * Work.Kernels.qParamFun τ ^ 3))
        + 6720 * Work.Kernels.qParamFun τ ^ 3‖
      ≤ ‖Work.Kernels.E4Fun τ - (1 + 240 * Work.Kernels.qParamFun τ
            + 2160 * Work.Kernels.qParamFun τ ^ 2 + 6720 * Work.Kernels.qParamFun τ ^ 3)‖
        + ‖(6720 : ℂ) * Work.Kernels.qParamFun τ ^ 3‖ := norm_add_le _ _
    _ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 + 6720 * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
        rw [h4]; exact add_le_add hb1 le_rfl
    _ ≤ (C + 6720 + 1) * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by nlinarith [hq3]

/-- `E₆ = 1 - 504 q - 16632 q² + O(‖q‖³)` on `{Im τ ≥ 1}`. -/
private lemma E6_three_term :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.E6Fun τ - (1 - 504 * Work.Kernels.qParamFun τ
          - 16632 * Work.Kernels.qParamFun τ ^ 2)‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  have hper : Function.Periodic (Work.Kernels.E6Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E6Fun := ModularForm.holo' ModularForm.E₆
  have hbdd : IsBoundedAtImInfty Work.Kernels.E6Fun := ModularFormClass.bdd_at_infty ModularForm.E₆
  obtain ⟨C, hC, h⟩ := qExp_tail 4 hper hhol hbdd 504 6 (by norm_num) E6_coeff_bound3
  refine ⟨C + 122976 + 1, by positivity, fun τ hτ => ?_⟩
  have h' := h τ hτ
  have hq1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := Work.Asymptotics.norm_qParamFun_le_one τ hτ
  have hq0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hsum : (∑ m ∈ Finset.range 4,
        (PowerSeries.coeff m) (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun)
          * Work.Kernels.qParamFun τ ^ m)
      = 1 - 504 * Work.Kernels.qParamFun τ - 16632 * Work.Kernels.qParamFun τ ^ 2
        - 122976 * Work.Kernels.qParamFun τ ^ 3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : (PowerSeries.coeff 0) (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun) = 1 := by
      rw [show Work.Kernels.E6Fun = Work.Modular.E6 from rfl, Work.Modular.E6_qExpansion_coeff]
      simp
    have h1 : (PowerSeries.coeff 1) (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun) = -504 := by
      rw [show Work.Kernels.E6Fun = Work.Modular.E6 from rfl,
        Work.Modular.E6_qExpansion_coeff 1, if_neg (by norm_num : (1:ℕ) ≠ 0)]
      norm_num [ArithmeticFunction.sigma]
    have h2 : (PowerSeries.coeff 2) (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun) = -16632 := by
      rw [show Work.Kernels.E6Fun = Work.Modular.E6 from rfl,
        Work.Modular.E6_qExpansion_coeff 2, if_neg (by norm_num : (2:ℕ) ≠ 0)]
      norm_num [ArithmeticFunction.sigma]
    have h3 : (PowerSeries.coeff 3) (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun) = -122976 := by
      rw [show Work.Kernels.E6Fun = Work.Modular.E6 from rfl,
        Work.Modular.E6_qExpansion_coeff 3, if_neg (by norm_num : (3:ℕ) ≠ 0)]
      norm_num [ArithmeticFunction.sigma]
    rw [h0, h1, h2, h3]; ring
  rw [hsum] at h'
  have hsplit : Work.Kernels.E6Fun τ - (1 - 504 * Work.Kernels.qParamFun τ
        - 16632 * Work.Kernels.qParamFun τ ^ 2)
      = (Work.Kernels.E6Fun τ - (1 - 504 * Work.Kernels.qParamFun τ
            - 16632 * Work.Kernels.qParamFun τ ^ 2 - 122976 * Work.Kernels.qParamFun τ ^ 3))
        + (-122976) * Work.Kernels.qParamFun τ ^ 3 := by ring
  rw [hsplit]
  have h4 : ‖(-122976 : ℂ) * Work.Kernels.qParamFun τ ^ 3‖
      = 122976 * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
    rw [norm_mul, show ‖(-122976:ℂ)‖ = (122976:ℝ) from by norm_num, norm_pow]
  have hb1 : ‖Work.Kernels.E6Fun τ - (1 - 504 * Work.Kernels.qParamFun τ
            - 16632 * Work.Kernels.qParamFun τ ^ 2 - 122976 * Work.Kernels.qParamFun τ ^ 3)‖
      ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
    refine le_trans h' (mul_le_mul_of_nonneg_left ?_ hC.le)
    exact pow_le_pow_of_le_one hq0 hq1 (by norm_num)
  have hq3 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ 3 := by positivity
  calc ‖(Work.Kernels.E6Fun τ - (1 - 504 * Work.Kernels.qParamFun τ
            - 16632 * Work.Kernels.qParamFun τ ^ 2 - 122976 * Work.Kernels.qParamFun τ ^ 3))
        + (-122976) * Work.Kernels.qParamFun τ ^ 3‖
      ≤ ‖Work.Kernels.E6Fun τ - (1 - 504 * Work.Kernels.qParamFun τ
            - 16632 * Work.Kernels.qParamFun τ ^ 2 - 122976 * Work.Kernels.qParamFun τ ^ 3)‖
        + ‖(-122976 : ℂ) * Work.Kernels.qParamFun τ ^ 3‖ := norm_add_le _ _
    _ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 + 122976 * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
        rw [h4]; exact add_le_add hb1 le_rfl
    _ ≤ (C + 122976 + 1) * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by nlinarith [hq3]

/-! ## The first- and second-order cusp expansions of `ψ₂`, `ψ₄` -/

private lemma rpow_le_rpow_of_one_le {sc : ℝ} (h1 : 1 ≤ sc) {a b : ℝ} (hab : a ≤ b) :
    sc ^ a ≤ sc ^ b := Real.rpow_le_rpow_of_exponent_le h1 hab

/-- Absorb a bound `C · sc^a · q^k` into `C · sc^N · q²`, for `a ≤ N`, `2 ≤ k`, `q ≤ 1`. -/
private lemma absorb {x : ℂ} {C sc q : ℝ} {a : ℝ} {k : ℕ} {N : ℝ}
    (hC : 0 ≤ C) (hsc : 1 ≤ sc) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (ha : a ≤ N)
    (hk : 2 ≤ k) (hN : 0 ≤ N)
    (h : ‖x‖ ≤ C * sc ^ a * q ^ k) : ‖x‖ ≤ C * sc ^ N * q ^ 2 := by
  have hqk : q ^ k ≤ q ^ 2 := pow_le_pow_of_le_one hq0 hq1 hk
  have hscN : sc ^ a ≤ sc ^ N := rpow_le_rpow_of_one_le hsc ha
  have hsq : (0:ℝ) ≤ sc ^ N := Real.rpow_nonneg (le_trans zero_le_one hsc) N
  have h1 : C * sc ^ a ≤ C * sc ^ N := mul_le_mul_of_nonneg_left hscN hC
  calc ‖x‖ ≤ C * sc ^ a * q ^ k := h
    _ = (C * sc ^ a) * q ^ k := by ring
    _ ≤ (C * sc ^ N) * q ^ 2 := mul_le_mul h1 hqk (by positivity) (by positivity)
    _ = C * sc ^ N * q ^ 2 := by ring

/-- Absorb a bound `C · sc^a · q³` into `C · sc^N · q³`, for `a ≤ N`. -/
private lemma absorb3 {x : ℂ} {C sc q : ℝ} {a : ℝ} {N : ℝ}
    (hC : 0 ≤ C) (hsc : 1 ≤ sc) (hq0 : 0 ≤ q) (ha : a ≤ N)
    (h : ‖x‖ ≤ C * sc ^ a * q ^ 3) : ‖x‖ ≤ C * sc ^ N * q ^ 3 := by
  have hscN : sc ^ a ≤ sc ^ N := rpow_le_rpow_of_one_le hsc ha
  calc ‖x‖ ≤ C * sc ^ a * q ^ 3 := h
    _ = (C * sc ^ a) * q ^ 3 := by ring
    _ ≤ (C * sc ^ N) * q ^ 3 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscN hC) (by positivity)
    _ = C * sc ^ N * q ^ 3 := by ring

/-- Absorb a bound `C · sc · q²` into `C · sc^N · q²`, for `N ≥ 1`. -/
private lemma absorb_sc {x : ℂ} {C sc q : ℝ} {N : ℝ}
    (hC : 0 ≤ C) (hsc : 1 ≤ sc) (hN : 1 ≤ N)
    (h : ‖x‖ ≤ C * sc * q ^ 2) : ‖x‖ ≤ C * sc ^ N * q ^ 2 := by
  have hle : sc ≤ sc ^ N := by
    calc sc = sc ^ (1:ℝ) := (Real.rpow_one sc).symm
      _ ≤ sc ^ N := rpow_le_rpow_of_one_le hsc hN
  calc ‖x‖ ≤ C * sc * q ^ 2 := h
    _ = (C * sc) * q ^ 2 := by ring
    _ ≤ (C * sc ^ N) * q ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hC) (by positivity)
    _ = C * sc ^ N * q ^ 2 := by ring

/-- `ψ₂ = 2Λ + (48Λ+408)q + O((scale)^N ‖q‖²)`, `ψ₄ = 2Λ - (288Λ+744)q + O((scale)^N ‖q‖²)`
and `ψ₄ - ψ₂ = (-336Λ-1152)q + (-1872Λ-28608)q² + O((scale)^N ‖q‖³)` on the funnel. -/
private lemma psi_expansions (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      (‖Work.Kernels.psi2 ℓ τ
          - (2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * Work.Kernels.qParamFun τ)‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 2
      ∧ ‖Work.Kernels.psi4 ℓ τ
          - (2 * Lam ℓ τ - (288 * Lam ℓ τ + 744) * Work.Kernels.qParamFun τ)‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 2
      ∧ ‖(Work.Kernels.psi4 ℓ τ - Work.Kernels.psi2 ℓ τ)
          - ((-336 * Lam ℓ τ - 1152) * Work.Kernels.qParamFun τ
              + (-1872 * Lam ℓ τ - 28608) * Work.Kernels.qParamFun τ ^ 2)‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 3) := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.KhatE1Core.psi_second_order ℓ
  refine ⟨(C + (48 * (Real.pi + 4) + 2636)) + (C + (1824 * (Real.pi + 4) + 25972))
      + (2 * C + 1), max N 1, by positivity, le_trans zero_le_one (le_max_right N 1),
      fun τ hτ => ?_⟩
  have hle1 : (1:ℝ) ≤ τ.im := Work.Asymptotics.Funnel.im_one hτ
  have hq1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := Work.Asymptotics.norm_qParamFun_le_one τ hle1
  have hq0 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hq2 : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ 2 := by positivity
  have hsc1 : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hNmax0 : (0:ℝ) ≤ max N 1 := le_trans zero_le_one (le_max_right N 1)
  have hNmax1 : (1:ℝ) ≤ max N 1 := le_max_right N 1
  have hNle : N ≤ max N 1 := le_max_left N 1
  have hA' : ‖Work.Kernels.psi2 ℓ τ - 2 * Lam ℓ τ
        - (48 * Lam ℓ τ + 408) * Work.Kernels.qParamFun τ
        - (48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2‖
      ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
    simpa only [Lam] using (h τ hτ).1
  have hB' : ‖Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ
        + (288 * Lam ℓ τ + 744) * Work.Kernels.qParamFun τ
        + (1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2‖
      ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
    simpa only [Lam] using (h τ hτ).2
  have hlam := norm_Lam_le ℓ τ
  -- the two `Λ`-linear second-order terms
  have hΛ2 : ‖(48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2‖
      ≤ (48 * (Real.pi + 4) + 2636) * (Work.Kernels.scale τ) ^ (max N 1)
          * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    have h1 : ‖(48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2‖
        ≤ (48 * ‖Lam ℓ τ‖ + 2636) * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
      have ha : ‖(48 * Lam ℓ τ + 2636)‖ ≤ 48 * ‖Lam ℓ τ‖ + 2636 := by
        calc ‖(48 * Lam ℓ τ + 2636)‖ ≤ ‖(48:ℂ) * Lam ℓ τ‖ + ‖(2636:ℂ)‖ := norm_add_le _ _
          _ = 48 * ‖Lam ℓ τ‖ + 2636 := by rw [norm_mul, Complex.norm_ofNat]; norm_num
      rw [norm_mul, norm_pow]
      exact mul_le_mul ha le_rfl (by positivity) (by positivity)
    have h2 : (48 * ‖Lam ℓ τ‖ + 2636) * ‖Work.Kernels.qParamFun τ‖ ^ 2
        ≤ (48 * (Real.pi + 4) + 2636) * Work.Kernels.scale τ
            * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
      have h3 : (48 * ‖Lam ℓ τ‖ + 2636) * ‖Work.Kernels.qParamFun τ‖ ^ 2
          ≤ (48 * ((Real.pi + 4) * Work.Kernels.scale τ) + 2636)
              * ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [hlam]) hq2
      nlinarith [h3, hsc1, hq2]
    exact absorb_sc (by positivity) hsc1 hNmax1 (le_trans h1 h2)
  have hΛ4 : ‖(1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2‖
      ≤ (1824 * (Real.pi + 4) + 25972) * (Work.Kernels.scale τ) ^ (max N 1)
          * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    have h1 : ‖(1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2‖
        ≤ (1824 * ‖Lam ℓ τ‖ + 25972) * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
      have ha : ‖(1824 * Lam ℓ τ + 25972)‖ ≤ 1824 * ‖Lam ℓ τ‖ + 25972 := by
        calc ‖(1824 * Lam ℓ τ + 25972)‖ ≤ ‖(1824:ℂ) * Lam ℓ τ‖ + ‖(25972:ℂ)‖ := norm_add_le _ _
          _ = 1824 * ‖Lam ℓ τ‖ + 25972 := by rw [norm_mul, Complex.norm_ofNat]; norm_num
      rw [norm_mul, norm_pow]
      exact mul_le_mul ha le_rfl (by positivity) (by positivity)
    have h2 : (1824 * ‖Lam ℓ τ‖ + 25972) * ‖Work.Kernels.qParamFun τ‖ ^ 2
        ≤ (1824 * (Real.pi + 4) + 25972) * Work.Kernels.scale τ
            * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
      have h3 : (1824 * ‖Lam ℓ τ‖ + 25972) * ‖Work.Kernels.qParamFun τ‖ ^ 2
          ≤ (1824 * ((Real.pi + 4) * Work.Kernels.scale τ) + 25972)
              * ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith [hlam]) hq2
      nlinarith [h3, hsc1, hq2]
    exact absorb_sc (by positivity) hsc1 hNmax1 (le_trans h1 h2)
  -- assembly
  have hscN0 : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ (max N 1) :=
    Real.rpow_nonneg (le_trans zero_le_one hsc1) _
  have hq32 : ‖Work.Kernels.qParamFun τ‖ ^ 3 ≤ ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
    pow_le_pow_of_le_one hq0 hq1 (by norm_num)
  have tA : ‖Work.Kernels.psi2 ℓ τ - 2 * Lam ℓ τ - (48 * Lam ℓ τ + 408) * Work.Kernels.qParamFun τ - (48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2‖
      ≤ C * (Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
    absorb hC.le hsc1 hq0 hq1 hNle (by norm_num) hNmax0 hA'
  have tB : ‖Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * Work.Kernels.qParamFun τ + (1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2‖
      ≤ C * (Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
    absorb hC.le hsc1 hq0 hq1 hNle (by norm_num) hNmax0 hB'
  have hG2 : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2 := mul_nonneg hscN0 hq2
  have hG3 : (0:ℝ) ≤ (Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 3 :=
    mul_nonneg hscN0 (by positivity)
  have hcb1 : C + (48 * (Real.pi + 4) + 2636) ≤ (C + (48 * (Real.pi + 4) + 2636)) + (C + (1824 * (Real.pi + 4) + 25972)) + (2 * C + 1) := by nlinarith [Real.pi_pos]
  have hcb2 : C + (1824 * (Real.pi + 4) + 25972) ≤ (C + (48 * (Real.pi + 4) + 2636)) + (C + (1824 * (Real.pi + 4) + 25972)) + (2 * C + 1) := by nlinarith [Real.pi_pos]
  have hcb3 : 2 * C + 1 ≤ (C + (48 * (Real.pi + 4) + 2636)) + (C + (1824 * (Real.pi + 4) + 25972)) + (2 * C + 1) := by nlinarith [Real.pi_pos]
  have tA3 : ‖Work.Kernels.psi2 ℓ τ - 2 * Lam ℓ τ - (48 * Lam ℓ τ + 408) * Work.Kernels.qParamFun τ - (48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2‖ ≤ C * (Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 3 :=
    absorb3 hC.le hsc1 hq0 hNle hA'
  have tB3 : ‖Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * Work.Kernels.qParamFun τ + (1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2‖ ≤ C * (Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 3 :=
    absorb3 hC.le hsc1 hq0 hNle hB'
  constructor
  · have hsplit : Work.Kernels.psi2 ℓ τ
          - (2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * Work.Kernels.qParamFun τ)
        = (Work.Kernels.psi2 ℓ τ - 2 * Lam ℓ τ - (48 * Lam ℓ τ + 408) * Work.Kernels.qParamFun τ - (48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2) + (48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2 := by ring
    rw [hsplit]
    have hstep : ‖(Work.Kernels.psi2 ℓ τ - 2 * Lam ℓ τ - (48 * Lam ℓ τ + 408) * Work.Kernels.qParamFun τ - (48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2) + (48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2‖
        ≤ (C + (48 * (Real.pi + 4) + 2636))
            * ((Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by
      calc ‖(Work.Kernels.psi2 ℓ τ - 2 * Lam ℓ τ - (48 * Lam ℓ τ + 408) * Work.Kernels.qParamFun τ - (48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2) + (48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2‖ ≤ ‖Work.Kernels.psi2 ℓ τ - 2 * Lam ℓ τ - (48 * Lam ℓ τ + 408) * Work.Kernels.qParamFun τ - (48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2‖ + ‖(48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2‖ := norm_add_le _ _
        _ ≤ C * (Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2 + (48 * (Real.pi + 4) + 2636) * (Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
            add_le_add tA hΛ2
        _ = (C + (48 * (Real.pi + 4) + 2636)) * ((Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by ring
    calc ‖(Work.Kernels.psi2 ℓ τ - 2 * Lam ℓ τ - (48 * Lam ℓ τ + 408) * Work.Kernels.qParamFun τ - (48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2) + (48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2‖
        ≤ (C + (48 * (Real.pi + 4) + 2636)) * ((Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2) := hstep
      _ ≤ ((C + (48 * (Real.pi + 4) + 2636)) + (C + (1824 * (Real.pi + 4) + 25972)) + (2 * C + 1)) * ((Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2) := mul_le_mul_of_nonneg_right hcb1 hG2
      _ = ((C + (48 * (Real.pi + 4) + 2636)) + (C + (1824 * (Real.pi + 4) + 25972)) + (2 * C + 1)) * (Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by ring
  · constructor
    · have hsplit : Work.Kernels.psi4 ℓ τ
            - (2 * Lam ℓ τ - (288 * Lam ℓ τ + 744) * Work.Kernels.qParamFun τ)
          = (Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * Work.Kernels.qParamFun τ + (1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2) - (1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2 := by ring
      rw [hsplit]
      have hstep : ‖(Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * Work.Kernels.qParamFun τ + (1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2) - (1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2‖
          ≤ (C + (1824 * (Real.pi + 4) + 25972))
              * ((Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by
        calc ‖(Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * Work.Kernels.qParamFun τ + (1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2) - (1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2‖ ≤ ‖Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * Work.Kernels.qParamFun τ + (1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2‖ + ‖(1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2‖ := norm_sub_le _ _
          _ ≤ C * (Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2
              + (1824 * (Real.pi + 4) + 25972) * (Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
              add_le_add tB hΛ4
          _ = (C + (1824 * (Real.pi + 4) + 25972)) * ((Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2) := by ring
      calc ‖(Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * Work.Kernels.qParamFun τ + (1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2) - (1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2‖
          ≤ (C + (1824 * (Real.pi + 4) + 25972)) * ((Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2) := hstep
        _ ≤ ((C + (48 * (Real.pi + 4) + 2636)) + (C + (1824 * (Real.pi + 4) + 25972)) + (2 * C + 1)) * ((Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2) := mul_le_mul_of_nonneg_right hcb2 hG2
        _ = ((C + (48 * (Real.pi + 4) + 2636)) + (C + (1824 * (Real.pi + 4) + 25972)) + (2 * C + 1)) * (Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by ring
    · have hsplit : (Work.Kernels.psi4 ℓ τ - Work.Kernels.psi2 ℓ τ)
            - ((-336 * Lam ℓ τ - 1152) * Work.Kernels.qParamFun τ
                + (-1872 * Lam ℓ τ - 28608) * Work.Kernels.qParamFun τ ^ 2)
          = (Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * Work.Kernels.qParamFun τ + (1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2) - (Work.Kernels.psi2 ℓ τ - 2 * Lam ℓ τ - (48 * Lam ℓ τ + 408) * Work.Kernels.qParamFun τ - (48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2) := by ring
      rw [hsplit]
      have hstep : ‖(Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * Work.Kernels.qParamFun τ + (1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2) - (Work.Kernels.psi2 ℓ τ - 2 * Lam ℓ τ - (48 * Lam ℓ τ + 408) * Work.Kernels.qParamFun τ - (48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2)‖
          ≤ (2 * C + 1) * ((Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 3) := by
        calc ‖(Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * Work.Kernels.qParamFun τ + (1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2) - (Work.Kernels.psi2 ℓ τ - 2 * Lam ℓ τ - (48 * Lam ℓ τ + 408) * Work.Kernels.qParamFun τ - (48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2)‖ ≤ ‖Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * Work.Kernels.qParamFun τ + (1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2‖ + ‖Work.Kernels.psi2 ℓ τ - 2 * Lam ℓ τ - (48 * Lam ℓ τ + 408) * Work.Kernels.qParamFun τ - (48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2‖ := norm_sub_le _ _
          _ ≤ C * (Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 3 + C * (Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 3 :=
              add_le_add tB3 tA3
          _ = (2 * C) * ((Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 3) := by ring
          _ ≤ (2 * C + 1) * ((Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 3) :=
              mul_le_mul_of_nonneg_right (by linarith) hG3
      calc ‖(Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * Work.Kernels.qParamFun τ + (1824 * Lam ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2) - (Work.Kernels.psi2 ℓ τ - 2 * Lam ℓ τ - (48 * Lam ℓ τ + 408) * Work.Kernels.qParamFun τ - (48 * Lam ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2)‖
          ≤ (2 * C + 1) * ((Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 3) := hstep
        _ ≤ ((C + (48 * (Real.pi + 4) + 2636)) + (C + (1824 * (Real.pi + 4) + 25972)) + (2 * C + 1)) * ((Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 3) := mul_le_mul_of_nonneg_right hcb3 hG3
        _ = ((C + (48 * (Real.pi + 4) + 2636)) + (C + (1824 * (Real.pi + 4) + 25972)) + (2 * C + 1)) * (Work.Kernels.scale τ) ^ (max N 1) * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by ring

/-! ## The ratio `E₆/E₄` -/

/-- `E₆/E₄ = 1 - 744 q + 159768 q² + O(‖q‖³)` on `{Im τ ≥ 2}`. -/
private lemma E6DivE4SecondOrder :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 2 ≤ τ.im →
      ‖Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ
          - (1 - 744 * Work.Kernels.qParamFun τ + 159768 * Work.Kernels.qParamFun τ ^ 2)‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  obtain ⟨C4, hC4, hE4⟩ := E4_three_term
  obtain ⟨C6, hC6, hE6⟩ := E6_three_term
  refine ⟨2 * (C6 + 160513 * C4 + 381836160) + 1, by positivity, fun τ hτ => ?_⟩
  have hτ1 : 1 ≤ τ.im := by linarith
  set q : ℂ := Work.Kernels.qParamFun τ with hq
  have hq1 : ‖q‖ ≤ 1 := Work.Asymptotics.norm_qParamFun_le_one τ hτ1
  have hq0 : (0:ℝ) ≤ ‖q‖ := norm_nonneg _
  have hq3 : (0:ℝ) ≤ ‖q‖ ^ 3 := by positivity
  have hE4low : (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun τ‖ := by
    have hle := Work.FunnelNumerics.E4_sub_one_le τ hτ
    have h4 : (1 : ℝ) ≤ ‖Work.Kernels.E4Fun τ‖ + ‖Work.Kernels.E4Fun τ - 1‖ := by
      have h := norm_sub_le (Work.Kernels.E4Fun τ) (Work.Kernels.E4Fun τ - 1)
      rw [show Work.Kernels.E4Fun τ - (Work.Kernels.E4Fun τ - 1) = 1 by ring, norm_one] at h
      exact h
    linarith
  have hE4ne : Work.Kernels.E4Fun τ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hE4low
    norm_num at hE4low
  set R : ℂ := 1 - 744 * q + 159768 * q ^ 2 with hR
  -- the three pieces
  have h1 : ‖Work.Kernels.E6Fun τ - (1 - 504 * q - 16632 * q ^ 2)‖ ≤ C6 * ‖q‖ ^ 3 := by
    have := hE6 τ hτ1; rwa [← hq] at this
  have h2 : ‖Work.Kernels.E4Fun τ - (1 + 240 * q + 2160 * q ^ 2)‖ ≤ C4 * ‖q‖ ^ 3 := by
    have := hE4 τ hτ1; rwa [← hq] at this
  have h3 : ‖R‖ ≤ 160513 := by
    have h2' : ‖(1:ℂ) - 744 * q‖ ≤ 1 + 744 * ‖q‖ := by
      calc ‖(1:ℂ) - 744 * q‖ ≤ ‖(1:ℂ)‖ + ‖(744 : ℂ) * q‖ := norm_sub_le _ _
        _ = 1 + 744 * ‖q‖ := by rw [norm_one, norm_mul, Complex.norm_ofNat]
    have h4' : ‖(159768 : ℂ) * q ^ 2‖ = 159768 * ‖q‖ ^ 2 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]
    have h5' : ‖(1:ℂ) - 744 * q + 159768 * q ^ 2‖ ≤ 1 + 744 * ‖q‖ + 159768 * ‖q‖ ^ 2 := by
      have := norm_add_le ((1:ℂ) - 744 * q) ((159768 : ℂ) * q ^ 2)
      rw [h4'] at this; linarith
    rw [hR]
    have h6' : ‖q‖ ^ 2 ≤ 1 := pow_le_one₀ hq0 hq1
    nlinarith [h5']
  have hpoly : ‖(-36737280 : ℂ) * q ^ 3 - 345098880 * q ^ 4‖ ≤ 381836160 * ‖q‖ ^ 3 := by
    have hA : ‖(-36737280 : ℂ) * q ^ 3‖ = 36737280 * ‖q‖ ^ 3 := by
      rw [norm_mul, show ‖(-36737280:ℂ)‖ = (36737280:ℝ) from by norm_num, norm_pow]
    have hB : ‖(345098880 : ℂ) * q ^ 4‖ ≤ 345098880 * ‖q‖ ^ 3 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]
      have : ‖q‖ ^ 4 ≤ ‖q‖ ^ 3 := pow_le_pow_of_le_one hq0 hq1 (by norm_num)
      nlinarith
    have h := norm_sub_le ((-36737280 : ℂ) * q ^ 3) ((345098880 : ℂ) * q ^ 4)
    rw [hA] at h
    linarith
  -- the algebraic identity
  have key : Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ - R
      = ((Work.Kernels.E6Fun τ - (1 - 504 * q - 16632 * q ^ 2))
          - R * (Work.Kernels.E4Fun τ - (1 + 240 * q + 2160 * q ^ 2))
          + (-36737280 * q ^ 3 - 345098880 * q ^ 4)) / Work.Kernels.E4Fun τ := by
    rw [eq_div_iff hE4ne, hR]
    field_simp
    ring
  rw [key, norm_div]
  have hnum : ‖(Work.Kernels.E6Fun τ - (1 - 504 * q - 16632 * q ^ 2))
        - R * (Work.Kernels.E4Fun τ - (1 + 240 * q + 2160 * q ^ 2))
        + (-36737280 * q ^ 3 - 345098880 * q ^ 4)‖
      ≤ (C6 + 160513 * C4 + 381836160) * ‖q‖ ^ 3 := by
    have hRmul : ‖R * (Work.Kernels.E4Fun τ - (1 + 240 * q + 2160 * q ^ 2))‖
        ≤ 160513 * (C4 * ‖q‖ ^ 3) := by
      rw [norm_mul]
      exact mul_le_mul h3 h2 (norm_nonneg _) (by positivity)
    have h12 : ‖(Work.Kernels.E6Fun τ - (1 - 504 * q - 16632 * q ^ 2))
          - R * (Work.Kernels.E4Fun τ - (1 + 240 * q + 2160 * q ^ 2))‖
        ≤ C6 * ‖q‖ ^ 3 + 160513 * (C4 * ‖q‖ ^ 3) := by
      have h := norm_sub_le (Work.Kernels.E6Fun τ - (1 - 504 * q - 16632 * q ^ 2))
        (R * (Work.Kernels.E4Fun τ - (1 + 240 * q + 2160 * q ^ 2)))
      linarith [h, h1, hRmul]
    have h13 := norm_add_le ((Work.Kernels.E6Fun τ - (1 - 504 * q - 16632 * q ^ 2))
          - R * (Work.Kernels.E4Fun τ - (1 + 240 * q + 2160 * q ^ 2)))
      ((-36737280 : ℂ) * q ^ 3 - 345098880 * q ^ 4)
    nlinarith [h13, h12, hpoly, hq3, hC4.le]
  have hfinal : ‖(Work.Kernels.E6Fun τ - (1 - 504 * q - 16632 * q ^ 2))
        - R * (Work.Kernels.E4Fun τ - (1 + 240 * q + 2160 * q ^ 2))
        + (-36737280 * q ^ 3 - 345098880 * q ^ 4)‖ / ‖Work.Kernels.E4Fun τ‖
      ≤ (2 * (C6 + 160513 * C4 + 381836160) + 1) * ‖q‖ ^ 3 := by
    have hden : ‖Work.Kernels.E4Fun τ‖ ≥ 1/2 := hE4low
    have hnum0 : (0:ℝ) ≤ (C6 + 160513 * C4 + 381836160) * ‖q‖ ^ 3 := by positivity
    rw [div_le_iff₀ (by linarith : (0:ℝ) < ‖Work.Kernels.E4Fun τ‖)]
    nlinarith [hnum, hden, hnum0]
  exact hfinal

/-! ## The `ψ₂·(1 - E₆/E₄)` term -/

/-- `ψ₂·(1 - E₆/E₄) = 1488 Λ q + (-283824 Λ + 303552) q² + O((scale)^N ‖q‖³)` on the funnel. -/
private lemma psi2_one_minus_ratio (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Kernels.psi2 ℓ τ * (1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ)
          - (1488 * Lam ℓ τ * Work.Kernels.qParamFun τ
              + (-283824 * Lam ℓ τ + 303552) * Work.Kernels.qParamFun τ ^ 2)‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  obtain ⟨Cψ, Nψ, hCψ, hNψ, hψ⟩ := psi_expansions ℓ
  obtain ⟨Cr, hCr, hr⟩ := E6DivE4SecondOrder
  refine ⟨Cψ * (744 + 159768 + Cr) + (48 * (Real.pi + 4) + 408) * 159768
      + (2 * (Real.pi + 4) + 48 * (Real.pi + 4) + 408) * Cr + 1, max Nψ 1, by positivity,
      le_trans zero_le_one (le_max_right Nψ 1), fun τ hτ => ?_⟩
  have hτ2 : 2 ≤ τ.im := Work.Asymptotics.Funnel.im_two hτ
  have hτ1 : 1 ≤ τ.im := by linarith
  set q : ℂ := Work.Kernels.qParamFun τ with hq
  set sc : ℝ := Work.Kernels.scale τ with hsc
  set K : ℝ := Real.pi + 4 with hK
  have hq1 : ‖q‖ ≤ 1 := by rw [hq]; exact Work.Asymptotics.norm_qParamFun_le_one τ hτ1
  have hq0 : (0:ℝ) ≤ ‖q‖ := norm_nonneg _
  have hsc1 : (1:ℝ) ≤ sc := by rw [hsc]; exact Work.Kernels.one_le_scale τ
  have hK0 : (0:ℝ) ≤ K := by rw [hK]; positivity
  have hlam : ‖Lam ℓ τ‖ ≤ K * sc := by rw [hK, hsc]; exact norm_Lam_le ℓ τ
  have hN'0 : (0:ℝ) ≤ max Nψ 1 := le_trans zero_le_one (le_max_right Nψ 1)
  have hsc_le : sc ≤ sc ^ (max Nψ 1) := by
    calc sc = sc ^ (1:ℝ) := (Real.rpow_one sc).symm
      _ ≤ sc ^ (max Nψ 1) := rpow_le_rpow_of_one_le hsc1 (le_max_right Nψ 1)
  have hψ2 : ‖Work.Kernels.psi2 ℓ τ - (2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * q)‖
      ≤ Cψ * sc ^ (max Nψ 1) * ‖q‖ ^ 2 := by
    have h := (hψ τ hτ).1
    rw [← hq] at h
    exact le_trans h (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (rpow_le_rpow_of_one_le hsc1 (le_max_left Nψ 1)) hCψ.le)
      (by positivity))
  have hR : ‖(1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ) - (744 * q - 159768 * q ^ 2)‖
      ≤ Cr * ‖q‖ ^ 3 := by
    have h := hr τ hτ2
    rw [← hq] at h
    have heq : (1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ) - (744 * q - 159768 * q ^ 2)
        = -(Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ
            - (1 - 744 * q + 159768 * q ^ 2)) := by ring
    rw [heq, norm_neg]
    exact h
  have honeR : ‖1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ‖ ≤ (744 + 159768 + Cr) * ‖q‖ := by
    have h1 : ‖(1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ) - (744 * q - 159768 * q ^ 2)‖
        + ‖744 * q - 159768 * q ^ 2‖
        ≥ ‖1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ‖ := by
      have h := norm_add_le ((1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ)
          - (744 * q - 159768 * q ^ 2)) (744 * q - 159768 * q ^ 2)
      have he : ((1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ) - (744 * q - 159768 * q ^ 2))
          + (744 * q - 159768 * q ^ 2) = 1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ := by ring
      rw [he] at h; exact h
    have h2 : ‖744 * q - 159768 * q ^ 2‖ ≤ (744 + 159768) * ‖q‖ := by
      have h2a : ‖(744:ℂ) * q‖ = 744 * ‖q‖ := by rw [norm_mul, Complex.norm_ofNat]
      have h2b : ‖(159768:ℂ) * q ^ 2‖ ≤ 159768 * ‖q‖ := by
        rw [norm_mul, Complex.norm_ofNat, norm_pow]
        nlinarith [hq0, hq1, pow_le_one₀ (n := 2) hq0 hq1]
      have h := norm_sub_le ((744:ℂ) * q) ((159768:ℂ) * q ^ 2)
      rw [h2a] at h
      linarith [h, h2b]
    have hq3le : ‖q‖ ^ 3 ≤ ‖q‖ := by
      have := pow_le_pow_of_le_one hq0 hq1 (by norm_num : 1 ≤ 3)
      simpa using this
    nlinarith [h1, hR, h2, hq3le, hq0, hCr.le]
  have hmain : Work.Kernels.psi2 ℓ τ * (1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ)
      - (1488 * Lam ℓ τ * q + (-283824 * Lam ℓ τ + 303552) * q ^ 2)
      = (Work.Kernels.psi2 ℓ τ - (2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * q))
          * (1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ)
        + (2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * q)
            * ((1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ) - (744 * q - 159768 * q ^ 2))
        + (48 * Lam ℓ τ + 408) * (-159768) * q ^ 3 := by ring
  rw [hmain]
  have hb1 : ‖(Work.Kernels.psi2 ℓ τ - (2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * q))
        * (1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ)‖
      ≤ Cψ * (744 + 159768 + Cr) * sc ^ (max Nψ 1) * ‖q‖ ^ 3 := by
    rw [norm_mul]
    have h := mul_le_mul hψ2 honeR (norm_nonneg _) (by positivity)
    calc ‖Work.Kernels.psi2 ℓ τ - (2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * q)‖
          * ‖1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ‖
        ≤ (Cψ * sc ^ (max Nψ 1) * ‖q‖ ^ 2) * ((744 + 159768 + Cr) * ‖q‖) := h
      _ = Cψ * (744 + 159768 + Cr) * sc ^ (max Nψ 1) * ‖q‖ ^ 3 := by ring
  have hb2 : ‖(48 * Lam ℓ τ + 408) * (-159768) * q ^ 3‖
      ≤ (48 * K + 408) * 159768 * sc ^ (max Nψ 1) * ‖q‖ ^ 3 := by
    have h1 : ‖(48 * Lam ℓ τ + 408)‖ ≤ (48 * K + 408) * sc := by
      have ha : ‖(48 * Lam ℓ τ + 408)‖ ≤ 48 * ‖Lam ℓ τ‖ + 408 := by
        calc ‖(48 * Lam ℓ τ + 408)‖ ≤ ‖(48:ℂ) * Lam ℓ τ‖ + ‖(408:ℂ)‖ := norm_add_le _ _
          _ = 48 * ‖Lam ℓ τ‖ + 408 := by rw [norm_mul, Complex.norm_ofNat]; norm_num
      have hb : 48 * ‖Lam ℓ τ‖ + 408 ≤ 48 * (K * sc) + 408 := by linarith [hlam]
      have hc : 48 * (K * sc) + 408 ≤ (48 * K + 408) * sc := by nlinarith [hsc1, hK0]
      linarith
    rw [norm_mul, norm_mul, norm_pow, show ‖(-159768 : ℂ)‖ = (159768:ℝ) from by norm_num]
    have h3 : (48 * K + 408) * sc * 159768 * ‖q‖ ^ 3
        ≤ (48 * K + 408) * 159768 * sc ^ (max Nψ 1) * ‖q‖ ^ 3 := by
      have : (48 * K + 408) * sc ≤ (48 * K + 408) * sc ^ (max Nψ 1) :=
        mul_le_mul_of_nonneg_left hsc_le (by positivity)
      nlinarith [this, pow_nonneg hq0 3]
    calc ‖(48 * Lam ℓ τ + 408)‖ * 159768 * ‖q‖ ^ 3
        ≤ ((48 * K + 408) * sc) * 159768 * ‖q‖ ^ 3 := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by norm_num)) (by positivity)
      _ ≤ (48 * K + 408) * 159768 * sc ^ (max Nψ 1) * ‖q‖ ^ 3 := h3
  have hb3 : ‖(2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * q)
        * ((1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ) - (744 * q - 159768 * q ^ 2))‖
      ≤ (2 * K + 48 * K + 408) * Cr * sc ^ (max Nψ 1) * ‖q‖ ^ 3 := by
    rw [norm_mul]
    have hfac : ‖2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * q‖ ≤ (2 * K + 48 * K + 408) * sc := by
      have ha : ‖2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * q‖
          ≤ 2 * ‖Lam ℓ τ‖ + ‖(48 * Lam ℓ τ + 408)‖ * ‖q‖ := by
        calc ‖2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * q‖
            ≤ ‖2 * Lam ℓ τ‖ + ‖(48 * Lam ℓ τ + 408) * q‖ := norm_add_le _ _
          _ = 2 * ‖Lam ℓ τ‖ + ‖(48 * Lam ℓ τ + 408)‖ * ‖q‖ := by
              rw [norm_mul, norm_mul, Complex.norm_ofNat]
      have hb : ‖(48 * Lam ℓ τ + 408)‖ ≤ (48 * K + 408) * sc := by
        have ha2 : ‖(48 * Lam ℓ τ + 408)‖ ≤ 48 * ‖Lam ℓ τ‖ + 408 := by
          calc ‖(48 * Lam ℓ τ + 408)‖ ≤ ‖(48:ℂ) * Lam ℓ τ‖ + ‖(408:ℂ)‖ := norm_add_le _ _
            _ = 48 * ‖Lam ℓ τ‖ + 408 := by rw [norm_mul, Complex.norm_ofNat]; norm_num
        have hb2 : 48 * ‖Lam ℓ τ‖ + 408 ≤ 48 * (K * sc) + 408 := by linarith [hlam]
        have hc2 : 48 * (K * sc) + 408 ≤ (48 * K + 408) * sc := by nlinarith [hsc1, hK0]
        linarith
      have hc : ‖(48 * Lam ℓ τ + 408)‖ * ‖q‖ ≤ (48 * K + 408) * sc := by
        calc ‖(48 * Lam ℓ τ + 408)‖ * ‖q‖ ≤ ((48 * K + 408) * sc) * 1 :=
              mul_le_mul hb hq1 hq0 (by positivity)
          _ = (48 * K + 408) * sc := by ring
      have hd : 2 * ‖Lam ℓ τ‖ ≤ 2 * (K * sc) := by linarith [hlam]
      linarith [ha, hc, hd, hsc1]
    have h := mul_le_mul hfac hR (norm_nonneg _) (by positivity)
    calc ‖2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * q‖
          * ‖(1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ) - (744 * q - 159768 * q ^ 2)‖
        ≤ ((2 * K + 48 * K + 408) * sc) * (Cr * ‖q‖ ^ 3) := h
      _ ≤ (2 * K + 48 * K + 408) * Cr * sc ^ (max Nψ 1) * ‖q‖ ^ 3 := by
          have hc : (2 * K + 48 * K + 408) * sc * (Cr * ‖q‖ ^ 3)
              ≤ (2 * K + 48 * K + 408) * Cr * sc ^ (max Nψ 1) * ‖q‖ ^ 3 := by
            have hsc' : (2 * K + 48 * K + 408) * sc ≤ (2 * K + 48 * K + 408) * sc ^ (max Nψ 1) :=
              mul_le_mul_of_nonneg_left hsc_le (by positivity)
            have hC2 : (0:ℝ) ≤ Cr * ‖q‖ ^ 3 := by positivity
            nlinarith [hsc', hC2, hq0, hCr.le, pow_nonneg hq0 3]
          linarith [hc]
  have hsum := norm_add_le ((Work.Kernels.psi2 ℓ τ - (2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * q))
          * (1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ)
        + (2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * q)
            * ((1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ) - (744 * q - 159768 * q ^ 2)))
    ((48 * Lam ℓ τ + 408) * (-159768) * q ^ 3)
  have hG : (0:ℝ) ≤ sc ^ (max Nψ 1) * ‖q‖ ^ 3 := mul_nonneg (by positivity) (by positivity)
  rw [show Cψ * (744 + 159768 + Cr) + (48 * (Real.pi + 4) + 408) * 159768
      + (2 * (Real.pi + 4) + 48 * (Real.pi + 4) + 408) * Cr + 1
      = (Cψ * (744 + 159768 + Cr) + (48 * K + 408) * 159768
          + (2 * K + 48 * K + 408) * Cr) + 1 from by rw [hK]]
  have hb1' : Cψ * (744 + 159768 + Cr) * sc ^ (max Nψ 1) * ‖q‖ ^ 3
      = Cψ * (744 + 159768 + Cr) * (sc ^ (max Nψ 1) * ‖q‖ ^ 3) := by ring
  have hb2' : (48 * K + 408) * 159768 * sc ^ (max Nψ 1) * ‖q‖ ^ 3
      = (48 * K + 408) * 159768 * (sc ^ (max Nψ 1) * ‖q‖ ^ 3) := by ring
  have hb3' : (2 * K + 48 * K + 408) * Cr * sc ^ (max Nψ 1) * ‖q‖ ^ 3
      = (2 * K + 48 * K + 408) * Cr * (sc ^ (max Nψ 1) * ‖q‖ ^ 3) := by ring
  calc ‖(Work.Kernels.psi2 ℓ τ - (2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * q))
          * (1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ)
        + (2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * q)
            * ((1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ) - (744 * q - 159768 * q ^ 2))
        + (48 * Lam ℓ τ + 408) * (-159768) * q ^ 3‖
      ≤ ‖(Work.Kernels.psi2 ℓ τ - (2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * q))
          * (1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ)
        + (2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * q)
            * ((1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ) - (744 * q - 159768 * q ^ 2))‖
        + ‖(48 * Lam ℓ τ + 408) * (-159768) * q ^ 3‖ := hsum
    _ ≤ (Cψ * (744 + 159768 + Cr) * sc ^ (max Nψ 1) * ‖q‖ ^ 3
          + (2 * K + 48 * K + 408) * Cr * sc ^ (max Nψ 1) * ‖q‖ ^ 3)
        + (48 * K + 408) * 159768 * sc ^ (max Nψ 1) * ‖q‖ ^ 3 := by
        have h := norm_add_le ((Work.Kernels.psi2 ℓ τ - (2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * q))
              * (1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ))
          ((2 * Lam ℓ τ + (48 * Lam ℓ τ + 408) * q)
              * ((1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ) - (744 * q - 159768 * q ^ 2)))
        linarith [h, hb1, hb2, hb3]
    _ ≤ (Cψ * (744 + 159768 + Cr) + (48 * K + 408) * 159768
          + (2 * K + 48 * K + 408) * Cr + 1) * (sc ^ (max Nψ 1) * ‖q‖ ^ 3) := by
        rw [hb1', hb2', hb3']
        nlinarith [hG]
    _ = (Cψ * (744 + 159768 + Cr) + (48 * K + 408) * 159768
          + (2 * K + 48 * K + 408) * Cr + 1) * sc ^ (max Nψ 1) * ‖q‖ ^ 3 := by ring

/-! ## The model of `ψ₄ - ψ₂·E₆/E₄` -/

/-- `ψ₄ - ψ₂·E₆/E₄ = (1152 Λ - 1152) q + (-285696 Λ + 274944) q² + O((scale)^N ‖q‖³)`. -/
private lemma D_model (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖(Work.Kernels.psi4 ℓ τ - Work.Kernels.psi2 ℓ τ * Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ)
          - ((1152 * Lam ℓ τ - 1152) * Work.Kernels.qParamFun τ
              + (-285696 * Lam ℓ τ + 274944) * Work.Kernels.qParamFun τ ^ 2)‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  obtain ⟨Cψ, Nψ, hCψ, hNψ, hψ⟩ := psi_expansions ℓ
  obtain ⟨C2, N2, hC2, hN2, h2⟩ := psi2_one_minus_ratio ℓ
  refine ⟨Cψ + C2 + 1, max Nψ N2, by positivity, le_trans hNψ (le_max_left Nψ N2),
      fun τ hτ => ?_⟩
  set q : ℂ := Work.Kernels.qParamFun τ with hq
  set sc : ℝ := Work.Kernels.scale τ with hsc
  have hq1 : ‖q‖ ≤ 1 := by
    rw [hq]; exact Work.Asymptotics.norm_qParamFun_le_one τ (Work.Asymptotics.Funnel.im_one hτ)
  have hq0 : (0:ℝ) ≤ ‖q‖ := norm_nonneg _
  have hsc1 : (1:ℝ) ≤ sc := by rw [hsc]; exact Work.Kernels.one_le_scale τ
  have hscN1 : sc ^ Nψ ≤ sc ^ (max Nψ N2) := rpow_le_rpow_of_one_le hsc1 (le_max_left Nψ N2)
  have hscN2 : sc ^ N2 ≤ sc ^ (max Nψ N2) := rpow_le_rpow_of_one_le hsc1 (le_max_right Nψ N2)
  have hA : ‖(Work.Kernels.psi4 ℓ τ - Work.Kernels.psi2 ℓ τ)
      - ((-336 * Lam ℓ τ - 1152) * q + (-1872 * Lam ℓ τ - 28608) * q ^ 2)‖
      ≤ Cψ * sc ^ (max Nψ N2) * ‖q‖ ^ 3 := by
    have h := (hψ τ hτ).2.2
    rw [← hq] at h
    exact le_trans h (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscN1 hCψ.le) (by positivity))
  have hB : ‖Work.Kernels.psi2 ℓ τ * (1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ)
      - (1488 * Lam ℓ τ * q + (-283824 * Lam ℓ τ + 303552) * q ^ 2)‖
      ≤ C2 * sc ^ (max Nψ N2) * ‖q‖ ^ 3 := by
    have h := h2 τ hτ
    rw [← hq] at h
    exact le_trans h (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscN2 hC2.le) (by positivity))
  rw [show Work.Kernels.psi4 ℓ τ - Work.Kernels.psi2 ℓ τ * Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ
        - ((1152 * Lam ℓ τ - 1152) * q + (-285696 * Lam ℓ τ + 274944) * q ^ 2)
      = ((Work.Kernels.psi4 ℓ τ - Work.Kernels.psi2 ℓ τ)
          - ((-336 * Lam ℓ τ - 1152) * q + (-1872 * Lam ℓ τ - 28608) * q ^ 2))
        + (Work.Kernels.psi2 ℓ τ * (1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ)
          - (1488 * Lam ℓ τ * q + (-283824 * Lam ℓ τ + 303552) * q ^ 2)) from by ring]
  have hsum := norm_add_le ((Work.Kernels.psi4 ℓ τ - Work.Kernels.psi2 ℓ τ)
          - ((-336 * Lam ℓ τ - 1152) * q + (-1872 * Lam ℓ τ - 28608) * q ^ 2))
    (Work.Kernels.psi2 ℓ τ * (1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ)
          - (1488 * Lam ℓ τ * q + (-283824 * Lam ℓ τ + 303552) * q ^ 2))
  have hq3 : (0:ℝ) ≤ ‖q‖ ^ 3 := by positivity
  have hG : (0:ℝ) ≤ sc ^ (max Nψ N2) * ‖q‖ ^ 3 := mul_nonneg (by positivity) hq3
  have hb1 : Cψ * sc ^ (max Nψ N2) * ‖q‖ ^ 3
      = Cψ * (sc ^ (max Nψ N2) * ‖q‖ ^ 3) := by ring
  have hb2 : C2 * sc ^ (max Nψ N2) * ‖q‖ ^ 3
      = C2 * (sc ^ (max Nψ N2) * ‖q‖ ^ 3) := by ring
  calc ‖((Work.Kernels.psi4 ℓ τ - Work.Kernels.psi2 ℓ τ)
          - ((-336 * Lam ℓ τ - 1152) * q + (-1872 * Lam ℓ τ - 28608) * q ^ 2))
        + (Work.Kernels.psi2 ℓ τ * (1 - Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ)
          - (1488 * Lam ℓ τ * q + (-283824 * Lam ℓ τ + 303552) * q ^ 2))‖
      ≤ Cψ * sc ^ (max Nψ N2) * ‖q‖ ^ 3 + C2 * sc ^ (max Nψ N2) * ‖q‖ ^ 3 := by
        linarith [hsum, hA, hB]
    _ = (Cψ + C2) * (sc ^ (max Nψ N2) * ‖q‖ ^ 3) := by rw [hb1, hb2]; ring
    _ ≤ (Cψ + C2 + 1) * (sc ^ (max Nψ N2) * ‖q‖ ^ 3) := by
        have : Cψ + C2 ≤ Cψ + C2 + 1 := by linarith
        exact mul_le_mul_of_nonneg_right this hG
    _ = (Cψ + C2 + 1) * sc ^ (max Nψ N2) * ‖q‖ ^ 3 := by ring

/-! ## The main theorem -/

theorem E1combo8FirstOrderBound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Asymptotics.E1combo8 ℓ τ
          - ((737280 : ℂ) * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
                + Work.Asymptotics.Compact.cuspC ℓ) + 122880) * Work.Kernels.qParamFun τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
  obtain ⟨Cj, hCj, hj⟩ := jFunnelBound
  obtain ⟨Cψ, Nψ, hCψ, hNψ, hψ⟩ := psi_expansions ℓ
  obtain ⟨CD, ND, hCD, hND, hD⟩ := D_model ℓ
  obtain ⟨CE4, hCE4, hE4two⟩ := Work.Asymptotics.E4Fun_two_term
  refine ⟨ Cj * ((1152 * (Real.pi + 4) + 1152) + (285696 * (Real.pi + 4) + 274944) + CD)
      + CD + 744 * CD + 744 * (285696 * (Real.pi + 4) + 274944)
      + 576 * (2 * CE4 + Cψ + 1) + 1,
    max (max Nψ ND) 1, by positivity, le_trans zero_le_one (le_max_right _ _), fun τ hτ => ?_⟩
  set q : ℂ := Work.Kernels.qParamFun τ with hq
  set sc : ℝ := Work.Kernels.scale τ with hsc
  set Nbig : ℝ := max (max Nψ ND) 1 with hNbig
  have hNbig1 : (1:ℝ) ≤ Nbig := by rw [hNbig]; exact le_max_right _ _
  have hNbig0 : (0:ℝ) ≤ Nbig := le_trans zero_le_one hNbig1
  have hNψle : Nψ ≤ Nbig := by
    rw [hNbig]; exact le_trans (le_max_left Nψ ND) (le_max_left _ _)
  have hNDle : ND ≤ Nbig := by
    rw [hNbig]; exact le_trans (le_max_right Nψ ND) (le_max_left _ _)
  have hq1 : ‖q‖ ≤ 1 := by
    rw [hq]; exact Work.Asymptotics.norm_qParamFun_le_one τ (Work.Asymptotics.Funnel.im_one hτ)
  have hq0 : (0:ℝ) ≤ ‖q‖ := norm_nonneg _
  have hsc1 : (1:ℝ) ≤ sc := by rw [hsc]; exact Work.Kernels.one_le_scale τ
  have hsc_le : sc ≤ sc ^ Nbig := by
    calc sc = sc ^ (1:ℝ) := (Real.rpow_one sc).symm
      _ ≤ sc ^ Nbig := rpow_le_rpow_of_one_le hsc1 hNbig1
  have hscpow1 : (1:ℝ) ≤ sc ^ Nbig := Real.one_le_rpow hsc1 hNbig0
  have hscNψ : sc ^ Nψ ≤ sc ^ Nbig := rpow_le_rpow_of_one_le hsc1 hNψle
  have hscND : sc ^ ND ≤ sc ^ Nbig := rpow_le_rpow_of_one_le hsc1 hNDle
  have hlam : ‖Lam ℓ τ‖ ≤ (Real.pi + 4) * sc := by rw [hsc]; exact norm_Lam_le ℓ τ
  have hqne : q ≠ 0 := by rw [hq]; exact Work.Asymptotics.qParamFun_ne_zero' τ
  have hqn : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hqne
  have hE4ne : Work.Kernels.E4Fun τ ≠ 0 := by
    intro h0
    have h4 := Work.FunnelNumerics.E4_sub_one_le τ (Work.Asymptotics.Funnel.im_two hτ)
    rw [h0, zero_sub, norm_neg, norm_one] at h4
    norm_num at h4
  have hJ : ‖Work.Kernels.jInvariantFun τ - (q⁻¹ + 744)‖ ≤ Cj * ‖q‖ := by
    have h := hj τ hτ
    rw [← hq] at h
    have he : Work.Kernels.jInvariantFun τ - (q⁻¹ + 744)
        = Work.Kernels.jInvariantFun τ - q⁻¹ - 744 := by ring
    rw [he]; exact h
  have hψ4 : ‖Work.Kernels.psi4 ℓ τ - (2 * Lam ℓ τ - (288 * Lam ℓ τ + 744) * q)‖
      ≤ Cψ * sc ^ Nbig * ‖q‖ ^ 2 := by
    have h := (hψ τ hτ).2.1
    rw [← hq] at h
    exact absorb hCψ.le hsc1 hq0 hq1 hNψle (by norm_num) hNbig0 h
  have hE4t : ‖Work.Kernels.E4Fun τ - 1 - 240 * q‖ ≤ CE4 * ‖q‖ ^ 2 := by
    have h := hE4two τ (Work.Asymptotics.Funnel.im_one hτ)
    rw [← hq] at h; exact h
  set D : ℂ := Work.Kernels.psi4 ℓ τ
      - Work.Kernels.psi2 ℓ τ * Work.Kernels.E6Fun τ / Work.Kernels.E4Fun τ with hDdef
  set rD : ℂ := D - ((1152 * Lam ℓ τ - 1152) * q
      + (-285696 * Lam ℓ τ + 274944) * q ^ 2) with hrDdef
  have hDm' : ‖rD‖ ≤ CD * sc ^ Nbig * ‖q‖ ^ 3 := by
    have h := hD τ hτ
    rw [← hq] at h
    refine le_trans h ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscND hCD.le) (by positivity)
  have hE1 : Work.Asymptotics.E1combo8 ℓ τ
      = Work.Kernels.jInvariantFun τ * D + 576 * (2 * Work.Kernels.E4Fun τ - Work.Kernels.psi4 ℓ τ) := by
    rw [Work.Asymptotics.E1combo8]
  have hkey : Work.Asymptotics.E1combo8 ℓ τ - ((737280 : ℂ) * Lam ℓ τ + 122880) * q
      = (Work.Kernels.jInvariantFun τ - (q⁻¹ + 744)) * D + q⁻¹ * rD + 744 * rD
        + 744 * (-285696 * Lam ℓ τ + 274944) * q ^ 2
        + 576 * (2 * (Work.Kernels.E4Fun τ - 1 - 240 * q)
            - (Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * q)) := by
    rw [hE1, hrDdef]
    field_simp
    ring
  rw [show Work.Asymptotics.E1combo8 ℓ τ
        - ((737280 : ℂ) * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
              + Work.Asymptotics.Compact.cuspC ℓ) + 122880) * Work.Kernels.qParamFun τ
      = Work.Asymptotics.E1combo8 ℓ τ - ((737280 : ℂ) * Lam ℓ τ + 122880) * q from by
        simp only [Lam, hq]]
  rw [hkey]
  set T1 : ℂ := (Work.Kernels.jInvariantFun τ - (q⁻¹ + 744)) * D with hT1def
  set T2 : ℂ := q⁻¹ * rD with hT2def
  set T3 : ℂ := 744 * rD with hT3def
  set T4 : ℂ := 744 * (-285696 * Lam ℓ τ + 274944) * q ^ 2 with hT4def
  set T5 : ℂ := 576 * (2 * (Work.Kernels.E4Fun τ - 1 - 240 * q)
      - (Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * q)) with hT5def
  have hgroup : (Work.Kernels.jInvariantFun τ - (q⁻¹ + 744)) * D + q⁻¹ * rD + 744 * rD
        + 744 * (-285696 * Lam ℓ τ + 274944) * q ^ 2
        + 576 * (2 * (Work.Kernels.E4Fun τ - 1 - 240 * q)
            - (Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * q))
      = T1 + T2 + T3 + T4 + T5 := by rw [hT1def, hT2def, hT3def, hT4def, hT5def]
  rw [hgroup]
  have hmodel : ‖(1152 * Lam ℓ τ - 1152) * q + (-285696 * Lam ℓ τ + 274944) * q ^ 2‖
      ≤ ((1152 * (Real.pi + 4) + 1152) + (285696 * (Real.pi + 4) + 274944)) * (sc ^ Nbig * ‖q‖) := by
    have h1 : ‖(1152 * Lam ℓ τ - 1152) * q‖ ≤ (1152 * (Real.pi + 4) + 1152) * (sc ^ Nbig * ‖q‖) := by
      have ha : ‖(1152 * Lam ℓ τ - 1152)‖ ≤ 1152 * ((Real.pi + 4) * sc) + 1152 := by
        calc ‖(1152:ℂ) * Lam ℓ τ - 1152‖ ≤ ‖(1152:ℂ) * Lam ℓ τ‖ + ‖(1152:ℂ)‖ := norm_sub_le _ _
          _ = 1152 * ‖Lam ℓ τ‖ + 1152 := by rw [norm_mul, Complex.norm_ofNat]
          _ ≤ 1152 * ((Real.pi + 4) * sc) + 1152 := by linarith [hlam]
      rw [norm_mul]
      calc ‖(1152 * Lam ℓ τ - 1152)‖ * ‖q‖ ≤ (1152 * ((Real.pi + 4) * sc) + 1152) * ‖q‖ :=
            mul_le_mul_of_nonneg_right ha hq0
        _ ≤ (1152 * (Real.pi + 4) + 1152) * (sc ^ Nbig * ‖q‖) := by
            have hA : 1152 * ((Real.pi + 4) * sc) + 1152
                ≤ (1152 * (Real.pi + 4) + 1152) * sc ^ Nbig := by
              nlinarith [hsc_le, hscpow1, Real.pi_pos]
            calc (1152 * ((Real.pi + 4) * sc) + 1152) * ‖q‖
                ≤ ((1152 * (Real.pi + 4) + 1152) * sc ^ Nbig) * ‖q‖ :=
                  mul_le_mul_of_nonneg_right hA hq0
              _ = (1152 * (Real.pi + 4) + 1152) * (sc ^ Nbig * ‖q‖) := by ring
    have h2 : ‖(-285696 * Lam ℓ τ + 274944) * q ^ 2‖
        ≤ (285696 * (Real.pi + 4) + 274944) * (sc ^ Nbig * ‖q‖) := by
      have ha : ‖(-285696 * Lam ℓ τ + 274944)‖ ≤ 285696 * ((Real.pi + 4) * sc) + 274944 := by
        calc ‖(-285696:ℂ) * Lam ℓ τ + 274944‖ ≤ ‖(-285696:ℂ) * Lam ℓ τ‖ + ‖(274944:ℂ)‖ := norm_add_le _ _
          _ = 285696 * ‖Lam ℓ τ‖ + 274944 := by
              rw [norm_mul, show ‖(-285696:ℂ)‖ = (285696:ℝ) from by norm_num]; norm_num
          _ ≤ 285696 * ((Real.pi + 4) * sc) + 274944 := by linarith [hlam]
      have hq2 : ‖q ^ 2‖ ≤ ‖q‖ := by
        rw [norm_pow]
        simpa using pow_le_pow_of_le_one hq0 hq1 (by norm_num : (1:ℕ) ≤ 2)
      rw [norm_mul]
      calc ‖(-285696 * Lam ℓ τ + 274944)‖ * ‖q ^ 2‖
          ≤ (285696 * ((Real.pi + 4) * sc) + 274944) * ‖q‖ := by
            refine mul_le_mul ha hq2 (by positivity) (by positivity)
        _ ≤ (285696 * (Real.pi + 4) + 274944) * (sc ^ Nbig * ‖q‖) := by
            have hA : 285696 * ((Real.pi + 4) * sc) + 274944
                ≤ (285696 * (Real.pi + 4) + 274944) * sc ^ Nbig := by
              nlinarith [hsc_le, hscpow1, Real.pi_pos]
            calc (285696 * ((Real.pi + 4) * sc) + 274944) * ‖q‖
                ≤ ((285696 * (Real.pi + 4) + 274944) * sc ^ Nbig) * ‖q‖ :=
                  mul_le_mul_of_nonneg_right hA hq0
              _ = (285696 * (Real.pi + 4) + 274944) * (sc ^ Nbig * ‖q‖) := by ring
    have hsum := norm_add_le ((1152 * Lam ℓ τ - 1152) * q)
      ((-285696 * Lam ℓ τ + 274944) * q ^ 2)
    have hG : (0:ℝ) ≤ sc ^ Nbig * ‖q‖ := mul_nonneg (by positivity) hq0
    nlinarith [hsum, h1, h2, hG]
  have hDb : ‖D‖ ≤ ((1152 * (Real.pi + 4) + 1152) + (285696 * (Real.pi + 4) + 274944) + CD)
      * (sc ^ Nbig * ‖q‖) := by
    have hDsplit : D = ((1152 * Lam ℓ τ - 1152) * q + (-285696 * Lam ℓ τ + 274944) * q ^ 2) + rD := by
      rw [hrDdef]; ring
    rw [hDsplit]
    have hrDb : ‖rD‖ ≤ CD * (sc ^ Nbig * ‖q‖) := by
      have hle : ‖q‖ ^ 3 ≤ ‖q‖ := by
        have := pow_le_pow_of_le_one hq0 hq1 (show 1 ≤ 3 by norm_num); simpa using this
      calc ‖rD‖ ≤ CD * sc ^ Nbig * ‖q‖ ^ 3 := hDm'
        _ = CD * (sc ^ Nbig * ‖q‖ ^ 3) := by ring
        _ ≤ CD * (sc ^ Nbig * ‖q‖) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (by positivity)) (by positivity)
        _ = CD * (sc ^ Nbig * ‖q‖) := by ring
    have hsum := norm_add_le ((1152 * Lam ℓ τ - 1152) * q + (-285696 * Lam ℓ τ + 274944) * q ^ 2) rD
    have hG : (0:ℝ) ≤ sc ^ Nbig * ‖q‖ := mul_nonneg (by positivity) hq0
    nlinarith [hsum, hmodel, hrDb, hG]
  have b1 : ‖T1‖ ≤ Cj * ((1152 * (Real.pi + 4) + 1152) + (285696 * (Real.pi + 4) + 274944) + CD)
      * (sc ^ Nbig * ‖q‖ ^ 2) := by
    rw [hT1def, norm_mul]
    have h := mul_le_mul hJ hDb (norm_nonneg _) (by positivity)
    calc ‖Work.Kernels.jInvariantFun τ - (q⁻¹ + 744)‖ * ‖D‖
        ≤ (Cj * ‖q‖) * (((1152 * (Real.pi + 4) + 1152) + (285696 * (Real.pi + 4) + 274944) + CD)
            * (sc ^ Nbig * ‖q‖)) := h
      _ = Cj * ((1152 * (Real.pi + 4) + 1152) + (285696 * (Real.pi + 4) + 274944) + CD)
            * (sc ^ Nbig * ‖q‖ ^ 2) := by ring
  have b2 : ‖T2‖ ≤ CD * (sc ^ Nbig * ‖q‖ ^ 2) := by
    rw [hT2def, norm_mul, norm_inv]
    have h : ‖q‖⁻¹ * ‖rD‖ ≤ ‖q‖⁻¹ * (CD * sc ^ Nbig * ‖q‖ ^ 3) :=
      mul_le_mul_of_nonneg_left hDm' (by positivity)
    calc ‖q‖⁻¹ * ‖rD‖ ≤ ‖q‖⁻¹ * (CD * sc ^ Nbig * ‖q‖ ^ 3) := h
      _ = CD * (sc ^ Nbig * ‖q‖ ^ 2) := by
          rw [show ‖q‖⁻¹ * (CD * sc ^ Nbig * ‖q‖ ^ 3)
              = CD * sc ^ Nbig * (‖q‖⁻¹ * ‖q‖ ^ 3) by ring]
          rw [show ‖q‖⁻¹ * ‖q‖ ^ 3 = ‖q‖ ^ 2 by
              rw [show ‖q‖ ^ 3 = ‖q‖ * ‖q‖ ^ 2 by ring, ← mul_assoc,
                inv_mul_cancel₀ hqn, one_mul]]
          ring
  have b3 : ‖T3‖ ≤ 744 * CD * (sc ^ Nbig * ‖q‖ ^ 2) := by
    rw [hT3def, norm_mul, show ‖(744:ℂ)‖ = (744:ℝ) from by norm_num]
    have hle : ‖q‖ ^ 3 ≤ ‖q‖ ^ 2 :=
      pow_le_pow_of_le_one hq0 hq1 (by norm_num)
    calc (744:ℝ) * ‖rD‖ ≤ 744 * (CD * sc ^ Nbig * ‖q‖ ^ 3) := by
          exact mul_le_mul_of_nonneg_left hDm' (by norm_num)
      _ = 744 * CD * (sc ^ Nbig * ‖q‖ ^ 3) := by ring
      _ ≤ 744 * CD * (sc ^ Nbig * ‖q‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hle (by positivity)) (by positivity)
      _ = 744 * CD * (sc ^ Nbig * ‖q‖ ^ 2) := by ring
  have b4 : ‖T4‖ ≤ 744 * (285696 * (Real.pi + 4) + 274944) * (sc ^ Nbig * ‖q‖ ^ 2) := by
    rw [hT4def, norm_mul, norm_mul, norm_pow,
      show ‖(744:ℂ)‖ = (744:ℝ) from by norm_num]
    have ha : ‖(-285696 * Lam ℓ τ + 274944)‖ ≤ 285696 * ((Real.pi + 4) * sc) + 274944 := by
      calc ‖(-285696:ℂ) * Lam ℓ τ + 274944‖ ≤ ‖(-285696:ℂ) * Lam ℓ τ‖ + ‖(274944:ℂ)‖ := norm_add_le _ _
        _ = 285696 * ‖Lam ℓ τ‖ + 274944 := by
            rw [norm_mul, show ‖(-285696:ℂ)‖ = (285696:ℝ) from by norm_num]; norm_num
        _ ≤ 285696 * ((Real.pi + 4) * sc) + 274944 := by linarith [hlam]
    have hb : 285696 * ((Real.pi + 4) * sc) + 274944 ≤ (285696 * (Real.pi + 4) + 274944) * sc ^ Nbig := by
      nlinarith [hsc_le, hscpow1, Real.pi_pos]
    have hq2 : (0:ℝ) ≤ ‖q‖ ^ 2 := by positivity
    calc 744 * ‖(-285696 * Lam ℓ τ + 274944)‖ * ‖q‖ ^ 2
        ≤ 744 * (285696 * ((Real.pi + 4) * sc) + 274944) * ‖q‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha (by norm_num)) hq2
      _ ≤ 744 * ((285696 * (Real.pi + 4) + 274944) * sc ^ Nbig) * ‖q‖ ^ 2 := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) hq2
      _ = 744 * (285696 * (Real.pi + 4) + 274944) * (sc ^ Nbig * ‖q‖ ^ 2) := by ring
  have b5 : ‖T5‖ ≤ 576 * (2 * CE4 + Cψ + 1) * (sc ^ Nbig * ‖q‖ ^ 2) := by
    rw [hT5def, norm_mul, show ‖(576:ℂ)‖ = (576:ℝ) from by norm_num]
    have hinner : ‖2 * (Work.Kernels.E4Fun τ - 1 - 240 * q)
        - (Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * q)‖
        ≤ (2 * CE4 + Cψ) * (sc ^ Nbig * ‖q‖ ^ 2) := by
      have h2E : ‖2 * (Work.Kernels.E4Fun τ - 1 - 240 * q)‖ ≤ 2 * CE4 * ‖q‖ ^ 2 := by
        rw [norm_mul, show ‖(2:ℂ)‖ = (2:ℝ) from by norm_num]
        calc 2 * ‖Work.Kernels.E4Fun τ - 1 - 240 * q‖ ≤ 2 * (CE4 * ‖q‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hE4t (by norm_num)
          _ = 2 * CE4 * ‖q‖ ^ 2 := by ring
      have hψ4' : ‖Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * q‖
          ≤ Cψ * sc ^ Nbig * ‖q‖ ^ 2 := by
        have he : Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * q
            = Work.Kernels.psi4 ℓ τ - (2 * Lam ℓ τ - (288 * Lam ℓ τ + 744) * q) := by ring
        rw [he]; exact hψ4
      have hsum := norm_sub_le (2 * (Work.Kernels.E4Fun τ - 1 - 240 * q))
        (Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * q)
      have hG : (0:ℝ) ≤ sc ^ Nbig * ‖q‖ ^ 2 := mul_nonneg (by positivity) (by positivity)
      have h1 : 2 * CE4 * ‖q‖ ^ 2 ≤ 2 * CE4 * (sc ^ Nbig * ‖q‖ ^ 2) := by
        have hc : (0:ℝ) ≤ 2 * CE4 := by positivity
        calc 2 * CE4 * ‖q‖ ^ 2 = (2 * CE4) * ‖q‖ ^ 2 := by ring
          _ ≤ (2 * CE4) * (sc ^ Nbig * ‖q‖ ^ 2) := by
              refine mul_le_mul_of_nonneg_left ?_ hc
              nlinarith [hscpow1, pow_nonneg hq0 2]
          _ = 2 * CE4 * (sc ^ Nbig * ‖q‖ ^ 2) := by ring
      calc ‖2 * (Work.Kernels.E4Fun τ - 1 - 240 * q)
            - (Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * q)‖
          ≤ ‖2 * (Work.Kernels.E4Fun τ - 1 - 240 * q)‖
              + ‖Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * q‖ := hsum
        _ ≤ 2 * CE4 * ‖q‖ ^ 2 + Cψ * sc ^ Nbig * ‖q‖ ^ 2 := add_le_add h2E hψ4'
        _ ≤ 2 * CE4 * (sc ^ Nbig * ‖q‖ ^ 2) + Cψ * (sc ^ Nbig * ‖q‖ ^ 2) := by
              have h2 : Cψ * sc ^ Nbig * ‖q‖ ^ 2 = Cψ * (sc ^ Nbig * ‖q‖ ^ 2) := by ring
              rw [h2]; exact add_le_add h1 le_rfl
        _ = (2 * CE4 + Cψ) * (sc ^ Nbig * ‖q‖ ^ 2) := by ring
    calc (576:ℝ) * ‖2 * (Work.Kernels.E4Fun τ - 1 - 240 * q)
          - (Work.Kernels.psi4 ℓ τ - 2 * Lam ℓ τ + (288 * Lam ℓ τ + 744) * q)‖
        ≤ 576 * ((2 * CE4 + Cψ) * (sc ^ Nbig * ‖q‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hinner (by norm_num)
      _ ≤ 576 * (2 * CE4 + Cψ + 1) * (sc ^ Nbig * ‖q‖ ^ 2) := by
          have hG : (0:ℝ) ≤ sc ^ Nbig * ‖q‖ ^ 2 := mul_nonneg (by positivity) (by positivity)
          nlinarith [hG]
  have hsum : ‖T1 + T2 + T3 + T4 + T5‖ ≤ ‖T1‖ + ‖T2‖ + ‖T3‖ + ‖T4‖ + ‖T5‖ := by
    have h1 := norm_add_le (T1 + T2 + T3 + T4) T5
    have h2 := norm_add_le (T1 + T2 + T3) T4
    have h3 := norm_add_le (T1 + T2) T3
    have h4 := norm_add_le T1 T2
    linarith
  have hG2 : (0:ℝ) ≤ sc ^ Nbig * ‖q‖ ^ 2 := mul_nonneg (by positivity) (by positivity)
  have hfinal : ‖T1‖ + ‖T2‖ + ‖T3‖ + ‖T4‖ + ‖T5‖
      ≤ (Cj * ((1152 * (Real.pi + 4) + 1152) + (285696 * (Real.pi + 4) + 274944) + CD)
          + CD + 744 * CD + 744 * (285696 * (Real.pi + 4) + 274944)
          + 576 * (2 * CE4 + Cψ + 1) + 1) * (sc ^ Nbig * ‖q‖ ^ 2) := by
    nlinarith [b1, b2, b3, b4, b5, hG2]
  calc ‖T1 + T2 + T3 + T4 + T5‖ ≤ ‖T1‖ + ‖T2‖ + ‖T3‖ + ‖T4‖ + ‖T5‖ := hsum
    _ ≤ (Cj * ((1152 * (Real.pi + 4) + 1152) + (285696 * (Real.pi + 4) + 274944) + CD)
          + CD + 744 * CD + 744 * (285696 * (Real.pi + 4) + 274944)
          + 576 * (2 * CE4 + Cψ + 1) + 1) * (sc ^ Nbig * ‖q‖ ^ 2) := hfinal
    _ = (Cj * ((1152 * (Real.pi + 4) + 1152) + (285696 * (Real.pi + 4) + 274944) + CD)
          + CD + 744 * CD + 744 * (285696 * (Real.pi + 4) + 274944)
          + 576 * (2 * CE4 + Cψ + 1) + 1) * sc ^ Nbig * ‖q‖ ^ 2 := by ring

end

end Work.Asymptotics.KhatE1

import Mathlib
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Residues.QExpansionTail
import Submission.Work.Residues.E4FunSecondOrder
import Submission.Work.Residues.E6FunSecondOrder
import Submission.Work.Residues.DeltaExpansion
import Submission.Work.Residues.NormCubeSubSqSharp
import Submission.Work.Modular.E2_qExpansion_coeff
import Submission.Work.Modular.E4_qExpansion_coeff
import Submission.Work.Modular.E6_qExpansion_coeff

namespace Work.Asymptotics.ZAtomsThird

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm _root_.Modular Manifold Bundle

noncomputable section

/-!
# First-order cusp expansions on `{Im τ ≥ 1/3}`

The four building blocks `E₂, E₄, E₆, Δ` of the kernels equal `1, 1, 1, 0` plus an
explicit multiple of `q = exp (2 π i τ)` up to `O(q²)`.  The results in
`Work.Asymptotics.KPlusXiDefs` are stated on the smaller region `{Im τ ≥ 1}`; the
applications to the third-generation atoms use the larger region `{Im τ ≥ 1/3}`, so we
re-derive the expansions here.

The only new ingredient is the `q`-expansion tail bound on `{Im τ ≥ 1/3}`, obtained by
repeating the proof of `Work.Residues.qExpansion_tail_bound` with the geometric ratio
`ρ = exp (-(2 π / 3))` instead of `exp (-(2 π))`; every other step of the argument uses
only `‖q‖ ≤ ρ` and `ρ < 1`.
-/

/-- **Tail bound for `q`-expansions on `{Im τ ≥ 1/3}`.**  If `f` is periodic of period
one, holomorphic and bounded at the cusp, and the coefficients of its `q`-expansion of
index `≥ r` grow at most like `M · m ^ K`, then `f` differs from the polynomial part
`∑_{m < r} c_m q^m` by `O(‖q‖ ^ r)` on `{τ : 1/3 ≤ Im τ}`. -/
theorem qExpansion_tail_bound_third (r : ℕ) {f : ℍ → ℂ}
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1)
    (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f)
    (M : ℝ) (K : ℕ) (hM : 0 ≤ M)
    (ha : ∀ m : ℕ, r ≤ m → ‖(UpperHalfPlane.qExpansion 1 f).coeff m‖ ≤ M * (m : ℝ) ^ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 / 3 ≤ τ.im →
      ‖f τ - ∑ m ∈ Finset.range r,
          (UpperHalfPlane.qExpansion 1 f).coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m‖
        ≤ C * ‖Function.Periodic.qParam 1 (τ : ℂ)‖ ^ r := by
  set ρ : ℝ := Real.exp (-(2 * Real.pi / 3)) with hρdef
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ < 1 := by
    rw [hρdef]; exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hSsum : Summable (fun m : ℕ => ((m : ℝ) + 1) ^ K * ρ ^ m) :=
    Work.Residues.summable_succ_pow_mul_geometric K hρ0 hρ1
  set S : ℝ := ∑' m : ℕ, ((m : ℝ) + 1) ^ K * ρ ^ m with hSdef
  have hSnonneg : 0 ≤ S := tsum_nonneg (fun m => by positivity)
  refine ⟨M * (max 1 (r : ℝ)) ^ K * S + 1, by positivity, fun τ hτ => ?_⟩
  set q : ℂ := Function.Periodic.qParam 1 (τ : ℂ) with hqdef
  have hqnorm : ‖q‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [hqdef, Function.Periodic.norm_qParam, div_one, UpperHalfPlane.coe_im]
    congr 1; ring
  have hqle : ‖q‖ ≤ ρ := by
    rw [hqnorm, hρdef, Real.exp_le_exp]; nlinarith [Real.pi_pos, hτ]
  have hs := UpperHalfPlane.hasSum_qExpansion (h := 1) (f := f) one_pos hper hhol hbdd τ
  have hs' := (hasSum_nat_add_iff' r).mpr hs
  have h0 : (∑ i ∈ Finset.range r, (UpperHalfPlane.qExpansion 1 f).coeff i • q ^ i)
      = ∑ i ∈ Finset.range r, (UpperHalfPlane.qExpansion 1 f).coeff i * q ^ i :=
    Finset.sum_congr rfl (fun i _ => smul_eq_mul ..)
  have htsum : (∑' n : ℕ, (UpperHalfPlane.qExpansion 1 f).coeff (n + r) • q ^ (n + r))
      = f τ - ∑ i ∈ Finset.range r, (UpperHalfPlane.qExpansion 1 f).coeff i * q ^ i := by
    rw [← h0]; exact hs'.tsum_eq
  rw [← htsum]
  -- termwise bound
  have hstep : ∀ n : ℕ, ((n : ℝ) + r) ^ K ≤ (max 1 (r : ℝ)) ^ K * ((n : ℝ) + 1) ^ K := by
    intro n
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hnr : ((n : ℝ) + r) ≤ (max 1 (r : ℝ)) * ((n : ℝ) + 1) := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; simp
      · have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
        rw [max_eq_right hr1]
        nlinarith
    calc ((n : ℝ) + r) ^ K ≤ ((max 1 (r : ℝ)) * ((n : ℝ) + 1)) ^ K :=
          pow_le_pow_left₀ (by positivity) hnr K
      _ = (max 1 (r : ℝ)) ^ K * ((n : ℝ) + 1) ^ K := mul_pow _ _ _
  have hterm : ∀ n : ℕ,
      ‖(UpperHalfPlane.qExpansion 1 f).coeff (n + r) • q ^ (n + r)‖
        ≤ (M * (max 1 (r : ℝ)) ^ K * ‖q‖ ^ r) * (((n : ℝ) + 1) ^ K * ρ ^ n) := by
    intro n
    have hcoe : ‖(UpperHalfPlane.qExpansion 1 f).coeff (n + r)‖ ≤ M * ((n : ℝ) + r) ^ K := by
      have h := ha (n + r) (Nat.le_add_left r n)
      simpa [Nat.cast_add] using h
    have hpow : ‖q ^ (n + r)‖ ≤ ‖q‖ ^ r * ρ ^ n := by
      rw [norm_pow, pow_add, mul_comm (‖q‖ ^ n)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg q) hqle n) (by positivity)
    rw [smul_eq_mul, norm_mul]
    calc ‖(UpperHalfPlane.qExpansion 1 f).coeff (n + r)‖ * ‖q ^ (n + r)‖
        ≤ (M * ((n : ℝ) + r) ^ K) * (‖q‖ ^ r * ρ ^ n) :=
          mul_le_mul hcoe hpow (norm_nonneg _) (by positivity)
      _ ≤ (M * ((max 1 (r : ℝ)) ^ K * ((n : ℝ) + 1) ^ K)) * (‖q‖ ^ r * ρ ^ n) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (hstep n) hM
      _ = (M * (max 1 (r : ℝ)) ^ K * ‖q‖ ^ r) * (((n : ℝ) + 1) ^ K * ρ ^ n) := by ring
  have hsumm : Summable (fun n : ℕ =>
      ‖(UpperHalfPlane.qExpansion 1 f).coeff (n + r) • q ^ (n + r)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm (hSsum.mul_left _)
  calc ‖∑' n : ℕ, (UpperHalfPlane.qExpansion 1 f).coeff (n + r) • q ^ (n + r)‖
      ≤ ∑' n : ℕ, ‖(UpperHalfPlane.qExpansion 1 f).coeff (n + r) • q ^ (n + r)‖ :=
        norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' n : ℕ, (M * (max 1 (r : ℝ)) ^ K * ‖q‖ ^ r) * (((n : ℝ) + 1) ^ K * ρ ^ n) :=
        Summable.tsum_le_tsum hterm hsumm (hSsum.mul_left _)
    _ = (M * (max 1 (r : ℝ)) ^ K * ‖q‖ ^ r) * S := tsum_mul_left
    _ ≤ (M * (max 1 (r : ℝ)) ^ K * S + 1) * ‖q‖ ^ r := by
        have h1 : (0:ℝ) ≤ ‖q‖ ^ r := by positivity
        nlinarith [h1, hSnonneg, hM, pow_nonneg (by positivity : (0:ℝ) ≤ max 1 (r:ℝ)) K]

/-! ## The coefficient bounds -/

private lemma E2_coeff_bound_third (m : ℕ) (hm : 2 ≤ m) :
    ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E2Fun).coeff m‖ ≤ 24 * (m : ℝ) ^ 2 := by
  rw [show (UpperHalfPlane.qExpansion 1 Work.Kernels.E2Fun)
      = (UpperHalfPlane.qExpansion 1 Work.Modular.E2) from rfl,
    Work.Modular.E2_qExpansion_coeff, if_neg (by omega : ¬ (m = 0)), norm_mul]
  have h24 : ‖(-24 : ℂ)‖ = (24 : ℝ) := by norm_num
  rw [h24, Complex.norm_natCast]
  have hσ : (ArithmeticFunction.sigma 1 m : ℝ) ≤ (m : ℝ) ^ 2 := by
    have h' : ArithmeticFunction.sigma 1 m ≤ m ^ 2 := by
      simpa using ArithmeticFunction.sigma_le_pow_succ 1 m
    exact_mod_cast h'
  nlinarith [hσ]

private lemma E4_coeff_bound_third (m : ℕ) (hm : 2 ≤ m) :
    ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff m‖ ≤ 240 * (m : ℝ) ^ 4 := by
  have hm0 : m ≠ 0 := by omega
  have hc : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff m
      = (240 : ℂ) * ((ArithmeticFunction.sigma 3 m : ℕ) : ℂ) := by
    rw [show (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun)
        = (UpperHalfPlane.qExpansion 1 Work.Modular.E4) from rfl,
      Work.Modular.E4_qExpansion_coeff m, if_neg hm0]
  have hsig : (ArithmeticFunction.sigma 3 m : ℝ) ≤ (m : ℝ) ^ 4 := by
    have h' : ArithmeticFunction.sigma 3 m ≤ m ^ 4 := by
      simpa using ArithmeticFunction.sigma_le_pow_succ 3 m
    exact_mod_cast h'
  rw [hc, norm_mul, Complex.norm_ofNat, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hsig (by norm_num)

private lemma E6_coeff_bound_third (m : ℕ) (hm : 2 ≤ m) :
    ‖(UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff m‖ ≤ 504 * (m : ℝ) ^ 6 := by
  have hm0 : m ≠ 0 := by omega
  have hc : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff m
      = (-504 : ℂ) * ((ArithmeticFunction.sigma 5 m : ℕ) : ℂ) := by
    rw [show (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun)
        = (UpperHalfPlane.qExpansion 1 Work.Modular.E6) from rfl,
      Work.Modular.E6_qExpansion_coeff m, if_neg hm0]
  have hsig : (ArithmeticFunction.sigma 5 m : ℝ) ≤ (m : ℝ) ^ 6 := by
    have h' : ArithmeticFunction.sigma 5 m ≤ m ^ 6 := by
      simpa using ArithmeticFunction.sigma_le_pow_succ 5 m
    exact_mod_cast h'
  rw [hc, norm_mul]
  have h504 : ‖(-504 : ℂ)‖ = (504 : ℝ) := by norm_num
  rw [h504, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hsig (by norm_num)

/-! ## The four first-order expansions on `{Im τ ≥ 1/3}` -/

/-- `E₂ = 1 - 24 q + O(q²)` on `{Im τ ≥ 1/3}`. -/
theorem E2Fun_two_term_third :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 / 3 ≤ τ.im →
      ‖Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ‖ ≤
        C * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
  have hper : Function.Periodic (Work.Kernels.E2Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    Work.Modular.E2_periodic_one
  have hhol : MDiff Work.Kernels.E2Fun := E2_mdifferentiable
  have hbdd : IsBoundedAtImInfty Work.Kernels.E2Fun := EisensteinSeries.isBoundedAtImInfty_E2
  obtain ⟨C, hC, hb⟩ := qExpansion_tail_bound_third 2 hper hhol hbdd 24 2 (by norm_num)
    E2_coeff_bound_third
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h := hb τ hτ
  have h0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E2Fun).coeff 0 = 1 := by
    rw [show Work.Kernels.E2Fun = Work.Modular.E2 from rfl, Work.Modular.E2_qExpansion_coeff]
    simp
  have h1 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E2Fun).coeff 1 = -24 := by
    rw [show Work.Kernels.E2Fun = Work.Modular.E2 from rfl, Work.Modular.E2_qExpansion_coeff]
    norm_num [ArithmeticFunction.sigma]
  rw [Finset.sum_range_succ, Finset.sum_range_one, h0, h1] at h
  rw [qParamFun_eq_qParam]
  convert h using 2
  ring

/-- `E₄ = 1 + 240 q + O(q²)` on `{Im τ ≥ 1/3}`. -/
theorem E4Fun_two_term_third :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 / 3 ≤ τ.im →
      ‖Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ‖ ≤
        C * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
  have hper : Function.Periodic (Work.Kernels.E4Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E4Fun := ModularForm.holo' ModularForm.E₄
  have hbdd : IsBoundedAtImInfty Work.Kernels.E4Fun :=
    ModularFormClass.bdd_at_infty ModularForm.E₄
  obtain ⟨C, hC, hb⟩ := qExpansion_tail_bound_third 2 hper hhol hbdd 240 4 (by norm_num)
    E4_coeff_bound_third
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h := hb τ hτ
  have h0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 0 = 1 := by
    rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl]
    simpa using Work.Modular.E4_qExpansion_coeff 0
  have h1 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 1 = 240 := by
    rw [show Work.Kernels.E4Fun = Work.Modular.E4 from rfl, Work.Modular.E4_qExpansion_coeff 1,
      if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  rw [Finset.sum_range_succ, Finset.sum_range_one, h0, h1] at h
  rw [qParamFun_eq_qParam]
  convert h using 2
  ring

/-- `E₆ = 1 - 504 q + O(q²)` on `{Im τ ≥ 1/3}`. -/
theorem E6Fun_two_term_third :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 / 3 ≤ τ.im →
      ‖Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ‖ ≤
        C * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
  have hper : Function.Periodic (Work.Kernels.E6Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E6Fun := ModularForm.holo' ModularForm.E₆
  have hbdd : IsBoundedAtImInfty Work.Kernels.E6Fun :=
    ModularFormClass.bdd_at_infty ModularForm.E₆
  obtain ⟨C, hC, hb⟩ := qExpansion_tail_bound_third 2 hper hhol hbdd 504 6 (by norm_num)
    E6_coeff_bound_third
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h := hb τ hτ
  have h0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 0 = 1 := by
    rw [show Work.Kernels.E6Fun = Work.Modular.E6 from rfl]
    simpa using Work.Modular.E6_qExpansion_coeff 0
  have h1 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 1 = -504 := by
    rw [show Work.Kernels.E6Fun = Work.Modular.E6 from rfl, Work.Modular.E6_qExpansion_coeff 1,
      if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  rw [Finset.sum_range_succ, Finset.sum_range_one, h0, h1] at h
  rw [qParamFun_eq_qParam]
  convert h using 2
  ring

/-- `Δ = q + O(q²)` on `{Im τ ≥ 1/3}`. -/
theorem DeltaFun_two_term_third :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 / 3 ≤ τ.im →
      ‖Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ‖ ≤
        C * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
  obtain ⟨A, hA0, hA⟩ := E4Fun_two_term_third
  obtain ⟨B, hB0, hB⟩ := E6Fun_two_term_third
  set ρ : ℝ := Real.exp (-(2 * Real.pi / 3)) with hρdef
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ1 : ρ ≤ 1 := by
    rw [hρdef]
    exact le_of_lt (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos]))
  set K : ℝ := 3 * A + 2 * B + 3 * (|(240:ℝ)| + A * ρ) ^ 2 + ρ * (|(240:ℝ)| + A * ρ) ^ 3
      + (|(-504:ℝ)| + B * ρ) ^ 2 with hKdef
  refine ⟨K / 1728 + 1, by positivity, fun τ hτ => ?_⟩
  have hqnorm : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) :=
    norm_qParamFun τ
  have hqle : ‖Work.Kernels.qParamFun τ‖ ≤ ρ := by
    rw [hqnorm, hρdef, Real.exp_le_exp]; nlinarith [Real.pi_pos, hτ]
  have hz : ‖Work.Kernels.E4Fun τ - 1 - (240:ℝ) * Work.Kernels.qParamFun τ‖
      ≤ A * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    convert hA τ hτ using 2 <;> norm_num
  have hw : ‖Work.Kernels.E6Fun τ - 1 - (-504:ℝ) * Work.Kernels.qParamFun τ‖
      ≤ B * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    convert hB τ hτ using 2 <;> push_cast <;> ring
  have hkey : ‖Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2
      - (1728:ℂ) * Work.Kernels.qParamFun τ‖ ≤ K * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
    have h1 := Work.Residues.NormCubeSubSqSharp hA0.le hB0.le hρ0 hρ1 hqle hz hw
    rw [hKdef]
    convert h1 using 3 <;> norm_num
  have hD : Work.Kernels.DeltaFun τ
      = (Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2) / 1728 := by
    have h1 : Work.Kernels.DeltaFun τ = ModularForm.discriminant τ := by
      rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant]
    rw [h1, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  have hΔ : Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ
      = (Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2
          - 1728 * Work.Kernels.qParamFun τ) / 1728 := by
    rw [hD]; ring
  rw [hΔ, norm_div, Complex.norm_ofNat]
  have hs : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ 2 := by positivity
  have h1 : ‖Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2
      - 1728 * Work.Kernels.qParamFun τ‖ / 1728
      ≤ K * ‖Work.Kernels.qParamFun τ‖ ^ 2 / 1728 :=
    div_le_div_of_nonneg_right hkey (by norm_num)
  have h2 : K * ‖Work.Kernels.qParamFun τ‖ ^ 2 / 1728
      ≤ (K / 1728 + 1) * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by nlinarith [hs]
  linarith [h1, h2]

/-! ## The first-order statement -/

theorem first_order :
    ∃ C : ℝ, 0 < C ∧
      (∀ z : UpperHalfPlane, 1 / 3 ≤ z.im → ‖Work.Kernels.E2Fun z - 1‖ ≤ C * ‖Work.Kernels.qParamFun z‖) ∧
      (∀ z : UpperHalfPlane, 1 / 3 ≤ z.im → ‖Work.Kernels.E4Fun z - 1‖ ≤ C * ‖Work.Kernels.qParamFun z‖) ∧
      (∀ z : UpperHalfPlane, 1 / 3 ≤ z.im → ‖Work.Kernels.E6Fun z - 1‖ ≤ C * ‖Work.Kernels.qParamFun z‖) ∧
      (∀ z : UpperHalfPlane, 1 / 3 ≤ z.im → ‖Work.Kernels.DeltaFun z - Work.Kernels.qParamFun z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 2) := by
  obtain ⟨C2, hC2, h2⟩ := E2Fun_two_term_third
  obtain ⟨C4, hC4, h4⟩ := E4Fun_two_term_third
  obtain ⟨C6, hC6, h6⟩ := E6Fun_two_term_third
  obtain ⟨Cd, hCd, hd⟩ := DeltaFun_two_term_third
  refine ⟨(C2 + 24) + (C4 + 240) + (C6 + 504) + Cd + 1, by positivity, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
      rw [norm_qParamFun]; rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hz]
    have hq2 : ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ ‖Work.Kernels.qParamFun z‖ := by
      nlinarith [norm_nonneg (Work.Kernels.qParamFun z)]
    have h := h2 z hz
    have hsplit : Work.Kernels.E2Fun z - 1
        = (Work.Kernels.E2Fun z - 1 + 24 * Work.Kernels.qParamFun z)
          - 24 * Work.Kernels.qParamFun z := by ring
    have hC := hC2
    rw [hsplit]
    calc ‖(Work.Kernels.E2Fun z - 1 + 24 * Work.Kernels.qParamFun z)
          - 24 * Work.Kernels.qParamFun z‖
        ≤ ‖Work.Kernels.E2Fun z - 1 + 24 * Work.Kernels.qParamFun z‖
          + ‖(24 : ℂ) * Work.Kernels.qParamFun z‖ := norm_sub_le _ _
      _ = ‖Work.Kernels.E2Fun z - 1 + 24 * Work.Kernels.qParamFun z‖
          + 24 * ‖Work.Kernels.qParamFun z‖ := by rw [norm_mul]; norm_num
      _ ≤ C2 * ‖Work.Kernels.qParamFun z‖ ^ 2 + 24 * ‖Work.Kernels.qParamFun z‖ := by
          linarith
      _ ≤ ((C2 + 24) + (C4 + 240) + (C6 + 504) + Cd + 1)
          * ‖Work.Kernels.qParamFun z‖ := by
          nlinarith [norm_nonneg (Work.Kernels.qParamFun z), hC4.le, hC6.le, hCd.le]
  · intro z hz
    have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
      rw [norm_qParamFun]; rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hz]
    have hq2 : ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ ‖Work.Kernels.qParamFun z‖ := by
      nlinarith [norm_nonneg (Work.Kernels.qParamFun z)]
    have h := h4 z hz
    have hsplit : Work.Kernels.E4Fun z - 1
        = (Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z)
          + 240 * Work.Kernels.qParamFun z := by ring
    have hC := hC4
    rw [hsplit]
    calc ‖(Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z)
          + 240 * Work.Kernels.qParamFun z‖
        ≤ ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z‖
          + ‖(240 : ℂ) * Work.Kernels.qParamFun z‖ := norm_add_le _ _
      _ = ‖Work.Kernels.E4Fun z - 1 - 240 * Work.Kernels.qParamFun z‖
          + 240 * ‖Work.Kernels.qParamFun z‖ := by rw [norm_mul]; norm_num
      _ ≤ C4 * ‖Work.Kernels.qParamFun z‖ ^ 2 + 240 * ‖Work.Kernels.qParamFun z‖ := by
          linarith
      _ ≤ ((C2 + 24) + (C4 + 240) + (C6 + 504) + Cd + 1)
          * ‖Work.Kernels.qParamFun z‖ := by
          nlinarith [norm_nonneg (Work.Kernels.qParamFun z), hC2.le, hC6.le, hCd.le]
  · intro z hz
    have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
      rw [norm_qParamFun]; rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hz]
    have hq2 : ‖Work.Kernels.qParamFun z‖ ^ 2 ≤ ‖Work.Kernels.qParamFun z‖ := by
      nlinarith [norm_nonneg (Work.Kernels.qParamFun z)]
    have h := h6 z hz
    have hsplit : Work.Kernels.E6Fun z - 1
        = (Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z)
          - 504 * Work.Kernels.qParamFun z := by ring
    have hC := hC6
    rw [hsplit]
    calc ‖(Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z)
          - 504 * Work.Kernels.qParamFun z‖
        ≤ ‖Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z‖
          + ‖(504 : ℂ) * Work.Kernels.qParamFun z‖ := norm_sub_le _ _
      _ = ‖Work.Kernels.E6Fun z - 1 + 504 * Work.Kernels.qParamFun z‖
          + 504 * ‖Work.Kernels.qParamFun z‖ := by rw [norm_mul]; norm_num
      _ ≤ C6 * ‖Work.Kernels.qParamFun z‖ ^ 2 + 504 * ‖Work.Kernels.qParamFun z‖ := by
          linarith
      _ ≤ ((C2 + 24) + (C4 + 240) + (C6 + 504) + Cd + 1)
          * ‖Work.Kernels.qParamFun z‖ := by
          nlinarith [norm_nonneg (Work.Kernels.qParamFun z), hC2.le, hC4.le, hCd.le]
  · intro z hz
    have h := hd z hz
    have hC := hCd
    calc ‖Work.Kernels.DeltaFun z - Work.Kernels.qParamFun z‖
        ≤ Cd * ‖Work.Kernels.qParamFun z‖ ^ 2 := h
      _ ≤ ((C2 + 24) + (C4 + 240) + (C6 + 504) + Cd + 1)
          * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
          nlinarith [pow_nonneg (norm_nonneg (Work.Kernels.qParamFun z)) 2, hC2.le, hC4.le, hC6.le]

end

end Work.Asymptotics.ZAtomsThird

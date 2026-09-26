import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Residues.E4FunSecondOrder
import Submission.Work.Residues.E6FunSecondOrder
import Submission.Work.Residues.DeltaExpansion
import Submission.Work.Modular.E2_qExpansion_coeff

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped Topology MatrixGroups ModularForm Manifold Bundle

noncomputable section

/-! ## Second order `q`-expansions of `E₂`, `E₄`, `E₆` on `{1 ≤ Im τ}`

Each of these is an instance of the `q`-expansion tail estimate
`Work.Residues.qExpansion_tail_bound` with `r = 3`, using the explicit coefficient
formulae `Work.Modular.E2_qExpansion_coeff`, `E4_qExpansion_coeff`, `E6_qExpansion_coeff`
and the divisor-sum bound `σ_k(m) ≤ m^{k+1}`. -/

/-- Coefficient bound for the `q`-expansion of `E₂`: `‖c_m‖ = 24 σ₁(m) ≤ 24 m²`. -/
private lemma E2_coeff_bound3 (m : ℕ) (hm : 2 ≤ m) :
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

/-- `E₂ = 1 - 24 q - 72 q² + O(‖q‖³)` on `{1 ≤ Im τ}`. -/
theorem E2Fun_second_order :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ
          + 72 * (Work.Kernels.qParamFun τ) ^ 2‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  have hper : Function.Periodic (Work.Kernels.E2Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    Work.Modular.E2_periodic_one
  have hhol : MDiff Work.Kernels.E2Fun := E2_mdifferentiable
  have hbdd : IsBoundedAtImInfty Work.Kernels.E2Fun := EisensteinSeries.isBoundedAtImInfty_E2
  obtain ⟨C, hC, hb⟩ := Work.Residues.qExpansion_tail_bound 3 hper hhol hbdd 24 2 (by norm_num)
    (fun m hm => E2_coeff_bound3 m (by omega))
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h := hb τ hτ
  have h0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E2Fun).coeff 0 = 1 := by
    rw [show Work.Kernels.E2Fun = Work.Modular.E2 from rfl, Work.Modular.E2_qExpansion_coeff]
    simp
  have h1 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E2Fun).coeff 1 = -24 := by
    rw [show Work.Kernels.E2Fun = Work.Modular.E2 from rfl, Work.Modular.E2_qExpansion_coeff]
    norm_num [ArithmeticFunction.sigma]
  have h2 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E2Fun).coeff 2 = -72 := by
    rw [show Work.Kernels.E2Fun = Work.Modular.E2 from rfl, Work.Modular.E2_qExpansion_coeff,
      if_neg (by norm_num : (2 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, h0, h1, h2] at h
  rw [show Function.Periodic.qParam 1 (τ : ℂ) = Work.Kernels.qParamFun τ from
    (qParamFun_eq_qParam τ).symm] at h
  convert h using 2 <;> ring

/-- Coefficient bound for the `q`-expansion of `E₄`: `‖c_m‖ = 240 σ₃(m) ≤ 240 m⁴`. -/
private lemma E4_coeff_bound3 (m : ℕ) (hm : 2 ≤ m) :
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

/-- `E₄ = 1 + 240 q + 2160 q² + O(‖q‖³)` on `{1 ≤ Im τ}`. -/
theorem E4Fun_second_order :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ
          - 2160 * (Work.Kernels.qParamFun τ) ^ 2‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  have hper : Function.Periodic (Work.Kernels.E4Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E4Fun := ModularForm.holo' ModularForm.E₄
  have hbdd : IsBoundedAtImInfty Work.Kernels.E4Fun :=
    ModularFormClass.bdd_at_infty ModularForm.E₄
  obtain ⟨C, hC, hb⟩ := Work.Residues.qExpansion_tail_bound 3 hper hhol hbdd 240 4 (by norm_num)
    (fun m hm => E4_coeff_bound3 m (by omega))
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h := hb τ hτ
  have h0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 0 = 1 := by
    rw [show (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun)
        = (UpperHalfPlane.qExpansion 1 Work.Modular.E4) from rfl]
    simpa using Work.Modular.E4_qExpansion_coeff 0
  have h1 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 1 = 240 := by
    rw [show (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun)
        = (UpperHalfPlane.qExpansion 1 Work.Modular.E4) from rfl,
      Work.Modular.E4_qExpansion_coeff 1, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  have h2 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 2 = 2160 := by
    rw [show (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun)
        = (UpperHalfPlane.qExpansion 1 Work.Modular.E4) from rfl,
      Work.Modular.E4_qExpansion_coeff 2, if_neg (by norm_num : (2 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, h0, h1, h2] at h
  rw [show Function.Periodic.qParam 1 (τ : ℂ) = Work.Kernels.qParamFun τ from
    (qParamFun_eq_qParam τ).symm] at h
  convert h using 2 <;> ring

/-- Coefficient bound for the `q`-expansion of `E₆`: `‖c_m‖ = 504 σ₅(m) ≤ 504 m⁶`. -/
private lemma E6_coeff_bound3 (m : ℕ) (hm : 2 ≤ m) :
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

/-- `E₆ = 1 - 504 q - 16632 q² + O(‖q‖³)` on `{1 ≤ Im τ}`. -/
theorem E6Fun_second_order :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ
          + 16632 * (Work.Kernels.qParamFun τ) ^ 2‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  have hper : Function.Periodic (Work.Kernels.E6Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E6Fun := ModularForm.holo' ModularForm.E₆
  have hbdd : IsBoundedAtImInfty Work.Kernels.E6Fun :=
    ModularFormClass.bdd_at_infty ModularForm.E₆
  obtain ⟨C, hC, hb⟩ := Work.Residues.qExpansion_tail_bound 3 hper hhol hbdd 504 6 (by norm_num)
    (fun m hm => E6_coeff_bound3 m (by omega))
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h := hb τ hτ
  have h0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 0 = 1 := by
    rw [show (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun)
        = (UpperHalfPlane.qExpansion 1 Work.Modular.E6) from rfl]
    simpa using Work.Modular.E6_qExpansion_coeff 0
  have h1 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 1 = -504 := by
    rw [show (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun)
        = (UpperHalfPlane.qExpansion 1 Work.Modular.E6) from rfl,
      Work.Modular.E6_qExpansion_coeff 1, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  have h2 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 2 = -16632 := by
    rw [show (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun)
        = (UpperHalfPlane.qExpansion 1 Work.Modular.E6) from rfl,
      Work.Modular.E6_qExpansion_coeff 2, if_neg (by norm_num : (2 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, h0, h1, h2] at h
  rw [show Function.Periodic.qParam 1 (τ : ℂ) = Work.Kernels.qParamFun τ from
    (qParamFun_eq_qParam τ).symm] at h
  convert h using 2 <;> ring

/-! ## Fourth order `q`-expansions of `E₄`, `E₆` on `{1 ≤ Im τ}` -/

/-- `E₄ = 1 + 240 q + 2160 q² + 6720 q³ + O(‖q‖⁴)` on `{1 ≤ Im τ}`. -/
theorem E4Fun_fourth_order :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ
          - 2160 * (Work.Kernels.qParamFun τ) ^ 2
          - 6720 * (Work.Kernels.qParamFun τ) ^ 3‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 4 := by
  have hper : Function.Periodic (Work.Kernels.E4Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E4Fun := ModularForm.holo' ModularForm.E₄
  have hbdd : IsBoundedAtImInfty Work.Kernels.E4Fun :=
    ModularFormClass.bdd_at_infty ModularForm.E₄
  obtain ⟨C, hC, hb⟩ := Work.Residues.qExpansion_tail_bound 4 hper hhol hbdd 240 4 (by norm_num)
    (fun m hm => E4_coeff_bound3 m (by omega))
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h := hb τ hτ
  have h0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 0 = 1 := by
    rw [show (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun)
        = (UpperHalfPlane.qExpansion 1 Work.Modular.E4) from rfl]
    simpa using Work.Modular.E4_qExpansion_coeff 0
  have h1 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 1 = 240 := by
    rw [show (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun)
        = (UpperHalfPlane.qExpansion 1 Work.Modular.E4) from rfl,
      Work.Modular.E4_qExpansion_coeff 1, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  have h2 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 2 = 2160 := by
    rw [show (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun)
        = (UpperHalfPlane.qExpansion 1 Work.Modular.E4) from rfl,
      Work.Modular.E4_qExpansion_coeff 2, if_neg (by norm_num : (2 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  have h3 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun).coeff 3 = 6720 := by
    rw [show (UpperHalfPlane.qExpansion 1 Work.Kernels.E4Fun)
        = (UpperHalfPlane.qExpansion 1 Work.Modular.E4) from rfl,
      Work.Modular.E4_qExpansion_coeff 3, if_neg (by norm_num : (3 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, h0, h1, h2, h3] at h
  rw [show Function.Periodic.qParam 1 (τ : ℂ) = Work.Kernels.qParamFun τ from
    (qParamFun_eq_qParam τ).symm] at h
  convert h using 2 <;> ring

/-- `E₆ = 1 - 504 q - 16632 q² - 122976 q³ + O(‖q‖⁴)` on `{1 ≤ Im τ}`. -/
theorem E6Fun_fourth_order :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ
          + 16632 * (Work.Kernels.qParamFun τ) ^ 2
          + 122976 * (Work.Kernels.qParamFun τ) ^ 3‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 4 := by
  have hper : Function.Periodic (Work.Kernels.E6Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆ one_mem_strictPeriods_SL
  have hhol : MDiff Work.Kernels.E6Fun := ModularForm.holo' ModularForm.E₆
  have hbdd : IsBoundedAtImInfty Work.Kernels.E6Fun :=
    ModularFormClass.bdd_at_infty ModularForm.E₆
  obtain ⟨C, hC, hb⟩ := Work.Residues.qExpansion_tail_bound 4 hper hhol hbdd 504 6 (by norm_num)
    (fun m hm => E6_coeff_bound3 m (by omega))
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h := hb τ hτ
  have h0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 0 = 1 := by
    rw [show (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun)
        = (UpperHalfPlane.qExpansion 1 Work.Modular.E6) from rfl]
    simpa using Work.Modular.E6_qExpansion_coeff 0
  have h1 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 1 = -504 := by
    rw [show (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun)
        = (UpperHalfPlane.qExpansion 1 Work.Modular.E6) from rfl,
      Work.Modular.E6_qExpansion_coeff 1, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  have h2 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 2 = -16632 := by
    rw [show (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun)
        = (UpperHalfPlane.qExpansion 1 Work.Modular.E6) from rfl,
      Work.Modular.E6_qExpansion_coeff 2, if_neg (by norm_num : (2 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  have h3 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 3 = -122976 := by
    rw [show (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun)
        = (UpperHalfPlane.qExpansion 1 Work.Modular.E6) from rfl,
      Work.Modular.E6_qExpansion_coeff 3, if_neg (by norm_num : (3 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, h0, h1, h2, h3] at h
  rw [show Function.Periodic.qParam 1 (τ : ℂ) = Work.Kernels.qParamFun τ from
    (qParamFun_eq_qParam τ).symm] at h
  convert h using 2 <;> ring

/-! ## Auxiliary norm estimates -/

/-- `‖x³ - y³‖ ≤ ‖x - y‖ (‖x‖² + ‖x‖‖y‖ + ‖y‖²)`. -/
private lemma norm_cube_sub_cube (x y : ℂ) :
    ‖x ^ 3 - y ^ 3‖ ≤ ‖x - y‖ * (‖x‖ ^ 2 + ‖x‖ * ‖y‖ + ‖y‖ ^ 2) := by
  have h : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring
  rw [h, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ‖x ^ 2 + x * y + y ^ 2‖ ≤ ‖x ^ 2 + x * y‖ + ‖y ^ 2‖ := norm_add_le _ _
    _ ≤ (‖x ^ 2‖ + ‖x * y‖) + ‖y ^ 2‖ := add_le_add_left (norm_add_le _ _) _
    _ = ‖x‖ ^ 2 + ‖x‖ * ‖y‖ + ‖y‖ ^ 2 := by rw [norm_pow, norm_mul, norm_pow]

/-- `‖x² - y²‖ ≤ ‖x - y‖ (‖x‖ + ‖y‖)`. -/
private lemma norm_sq_sub_sq (x y : ℂ) :
    ‖x ^ 2 - y ^ 2‖ ≤ ‖x - y‖ * (‖x‖ + ‖y‖) := by
  have h : x ^ 2 - y ^ 2 = (x - y) * (x + y) := by ring
  rw [h, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_add_le x y) (norm_nonneg _)

/-! ## The fourth-order `q`-expansion of `Δ` -/

/-- **Algebraic core.**  If `z = 1 + 240q + 2160q² + 6720q³ + O(q⁴)` and
`w = 1 - 504q - 16632q² - 122976q³ + O(q⁴)` then `(z³ - w²)/1728 = q - 24q² + 252q³ + O(q⁴)`. -/
private lemma delta_fourth_algebra {A B ρ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ1 : ρ ≤ 1)
    {q z w : ℂ} (hq : ‖q‖ ≤ ρ)
    (hz : ‖z - (1 + 240 * q + 2160 * q ^ 2 + 6720 * q ^ 3)‖ ≤ A * ‖q‖ ^ 4)
    (hw : ‖w - (1 - 504 * q - 16632 * q ^ 2 - 122976 * q ^ 3)‖ ≤ B * ‖q‖ ^ 4) :
    ‖(z ^ 3 - w ^ 2) / 1728 - (q - 24 * q ^ 2 + 252 * q ^ 3)‖ ≤
      ((3 * A * (9121 + A) ^ 2 + 2 * B * (140113 + B) + 739175913792) / 1728)
        * ‖q‖ ^ 4 := by
  set t : ℝ := ‖q‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have ht1 : t ≤ 1 := le_trans hq hρ1
  set Z : ℂ := 1 + 240 * q + 2160 * q ^ 2 + 6720 * q ^ 3 with hZ
  set W : ℂ := 1 - 504 * q - 16632 * q ^ 2 - 122976 * q ^ 3 with hW
  have hzt : ‖z - Z‖ ≤ A * t ^ 4 := by rw [ht]; exact hz
  have hwt : ‖w - W‖ ≤ B * t ^ 4 := by rw [ht]; exact hw
  have hAt : 0 ≤ A * t ^ 4 := mul_nonneg hA (by positivity)
  have hBt : 0 ≤ B * t ^ 4 := mul_nonneg hB (by positivity)
  have ht4 : t ^ 4 ≤ 1 := pow_le_one₀ ht0 ht1
  have ht3 : t ^ 3 ≤ 1 := pow_le_one₀ ht0 ht1
  have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
  have hZnorm : ‖Z‖ ≤ 9121 := by
    rw [hZ]
    have e1 : ‖(1 : ℂ)‖ = 1 := norm_one
    have e2 : ‖(240 : ℂ) * q‖ = 240 * t := by rw [norm_mul, Complex.norm_ofNat, ht]
    have e3 : ‖(2160 : ℂ) * q ^ 2‖ = 2160 * t ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ht]
    have e4 : ‖(6720 : ℂ) * q ^ 3‖ = 6720 * t ^ 3 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ht]
    calc ‖(1 : ℂ) + 240 * q + 2160 * q ^ 2 + 6720 * q ^ 3‖
        ≤ ‖(1 : ℂ) + 240 * q + 2160 * q ^ 2‖ + ‖(6720 : ℂ) * q ^ 3‖ := norm_add_le _ _
      _ ≤ (‖(1 : ℂ) + 240 * q‖ + ‖(2160 : ℂ) * q ^ 2‖) + ‖(6720 : ℂ) * q ^ 3‖ :=
          add_le_add_left (norm_add_le _ _) _
      _ ≤ ((‖(1 : ℂ)‖ + ‖(240 : ℂ) * q‖) + ‖(2160 : ℂ) * q ^ 2‖)
            + ‖(6720 : ℂ) * q ^ 3‖ := add_le_add_left (add_le_add_left (norm_add_le _ _) _) _
      _ = (1 + 240 * t + 2160 * t ^ 2) + 6720 * t ^ 3 := by rw [e1, e2, e3, e4]
      _ ≤ 9121 := by nlinarith [ht0, ht1, ht2, ht3]
  have hWnorm : ‖W‖ ≤ 140113 := by
    rw [hW]
    have e1 : ‖(1 : ℂ)‖ = 1 := norm_one
    have e2 : ‖(504 : ℂ) * q‖ = 504 * t := by rw [norm_mul, Complex.norm_ofNat, ht]
    have e3 : ‖(16632 : ℂ) * q ^ 2‖ = 16632 * t ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ht]
    have e4 : ‖(122976 : ℂ) * q ^ 3‖ = 122976 * t ^ 3 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ht]
    calc ‖(1 : ℂ) - 504 * q - 16632 * q ^ 2 - 122976 * q ^ 3‖
        ≤ ‖(1 : ℂ) - 504 * q - 16632 * q ^ 2‖ + ‖(122976 : ℂ) * q ^ 3‖ := norm_sub_le _ _
      _ ≤ (‖(1 : ℂ) - 504 * q‖ + ‖(16632 : ℂ) * q ^ 2‖) + ‖(122976 : ℂ) * q ^ 3‖ :=
          add_le_add_left (norm_sub_le _ _) _
      _ ≤ ((‖(1 : ℂ)‖ + ‖(504 : ℂ) * q‖) + ‖(16632 : ℂ) * q ^ 2‖)
            + ‖(122976 : ℂ) * q ^ 3‖ := add_le_add_left (add_le_add_left (norm_sub_le _ _) _) _
      _ = (1 + 504 * t + 16632 * t ^ 2) + 122976 * t ^ 3 := by rw [e1, e2, e3, e4]
      _ ≤ 140113 := by nlinarith [ht0, ht1, ht2, ht3]
  have hznorm : ‖z‖ ≤ 9121 + A := by
    have h1 : ‖z‖ ≤ ‖Z‖ + ‖z - Z‖ := by
      have h := norm_add_le Z (z - Z)
      have h' : Z + (z - Z) = z := by ring
      rwa [h'] at h
    have h2 : A * t ^ 4 ≤ A := by nlinarith [hA, ht4]
    linarith
  have hwnorm : ‖w‖ ≤ 140113 + B := by
    have h1 : ‖w‖ ≤ ‖W‖ + ‖w - W‖ := by
      have h := norm_add_le W (w - W)
      have h' : W + (w - W) = w := by ring
      rwa [h'] at h
    have h2 : B * t ^ 4 ≤ B := by nlinarith [hB, ht4]
    linarith
  have hid : (1 + 240 * q + 2160 * q ^ 2 + 6720 * q ^ 3) ^ 3
        - (1 - 504 * q - 16632 * q ^ 2 - 122976 * q ^ 3) ^ 2
        - (1728 * q - 41472 * q ^ 2 + 435456 * q ^ 3)
      = q ^ 4 * ((-3661632 : ℂ) + 516865536 * q + 15991962624 * q ^ 2
          + 126572544000 * q ^ 3 + 292626432000 * q ^ 4 + 303464448000 * q ^ 5) := by
    ring
  have hP : ‖(-3661632 : ℂ) + 516865536 * q + 15991962624 * q ^ 2 + 126572544000 * q ^ 3
      + 292626432000 * q ^ 4 + 303464448000 * q ^ 5‖ ≤ 739175913792 := by
    have e0 : ‖(-3661632 : ℂ)‖ = 3661632 := by norm_num
    have e1 : ‖(516865536 : ℂ) * q‖ = 516865536 * t := by rw [norm_mul, Complex.norm_ofNat, ht]
    have e2 : ‖(15991962624 : ℂ) * q ^ 2‖ = 15991962624 * t ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ht]
    have e3 : ‖(126572544000 : ℂ) * q ^ 3‖ = 126572544000 * t ^ 3 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ht]
    have e4 : ‖(292626432000 : ℂ) * q ^ 4‖ = 292626432000 * t ^ 4 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ht]
    have e5 : ‖(303464448000 : ℂ) * q ^ 5‖ = 303464448000 * t ^ 5 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ht]
    have ht5 : t ^ 5 ≤ 1 := pow_le_one₀ ht0 ht1
    calc ‖(-3661632 : ℂ) + 516865536 * q + 15991962624 * q ^ 2 + 126572544000 * q ^ 3
          + 292626432000 * q ^ 4 + 303464448000 * q ^ 5‖
        ≤ ‖(-3661632 : ℂ) + 516865536 * q + 15991962624 * q ^ 2 + 126572544000 * q ^ 3
              + 292626432000 * q ^ 4‖ + ‖(303464448000 : ℂ) * q ^ 5‖ := norm_add_le _ _
      _ ≤ (‖(-3661632 : ℂ) + 516865536 * q + 15991962624 * q ^ 2 + 126572544000 * q ^ 3‖
              + ‖(292626432000 : ℂ) * q ^ 4‖) + ‖(303464448000 : ℂ) * q ^ 5‖ :=
          add_le_add_left (norm_add_le _ _) _
      _ ≤ ((‖(-3661632 : ℂ) + 516865536 * q + 15991962624 * q ^ 2‖
              + ‖(126572544000 : ℂ) * q ^ 3‖) + ‖(292626432000 : ℂ) * q ^ 4‖)
            + ‖(303464448000 : ℂ) * q ^ 5‖ :=
          add_le_add_left (add_le_add_left (norm_add_le _ _) _) _
      _ ≤ (((‖(-3661632 : ℂ) + 516865536 * q‖ + ‖(15991962624 : ℂ) * q ^ 2‖)
              + ‖(126572544000 : ℂ) * q ^ 3‖) + ‖(292626432000 : ℂ) * q ^ 4‖)
            + ‖(303464448000 : ℂ) * q ^ 5‖ :=
          add_le_add_left (add_le_add_left (add_le_add_left (norm_add_le _ _) _) _) _
      _ ≤ ((((‖(-3661632 : ℂ)‖ + ‖(516865536 : ℂ) * q‖) + ‖(15991962624 : ℂ) * q ^ 2‖)
              + ‖(126572544000 : ℂ) * q ^ 3‖) + ‖(292626432000 : ℂ) * q ^ 4‖)
            + ‖(303464448000 : ℂ) * q ^ 5‖ :=
          add_le_add_left (add_le_add_left (add_le_add_left
            (add_le_add_left (norm_add_le _ _) _) _) _) _
      _ = ((((3661632 + 516865536 * t) + 15991962624 * t ^ 2) + 126572544000 * t ^ 3)
            + 292626432000 * t ^ 4) + 303464448000 * t ^ 5 := by rw [e0, e1, e2, e3, e4, e5]
      _ ≤ 739175913792 := by nlinarith [ht0, ht1, ht2, ht3, ht4, ht5]
  have hZW : ‖Z ^ 3 - W ^ 2 - (1728 * q - 41472 * q ^ 2 + 435456 * q ^ 3)‖
      ≤ 739175913792 * t ^ 4 := by
    rw [hZ, hW, hid, norm_mul, norm_pow]
    calc t ^ 4 * ‖(-3661632 : ℂ) + 516865536 * q + 15991962624 * q ^ 2
            + 126572544000 * q ^ 3 + 292626432000 * q ^ 4 + 303464448000 * q ^ 5‖
        = ‖q‖ ^ 4 * ‖(-3661632 : ℂ) + 516865536 * q + 15991962624 * q ^ 2
            + 126572544000 * q ^ 3 + 292626432000 * q ^ 4 + 303464448000 * q ^ 5‖ := by
          rw [ht]
      _ ≤ ‖q‖ ^ 4 * 739175913792 := mul_le_mul_of_nonneg_left hP (by positivity)
      _ = 739175913792 * t ^ 4 := by rw [ht]; ring
  have hcubeZ : ‖z ^ 3 - Z ^ 3‖ ≤ A * t ^ 4 * (3 * (9121 + A) ^ 2) := by
    have h := norm_cube_sub_cube z Z
    have hb : ‖z‖ ^ 2 + ‖z‖ * ‖Z‖ + ‖Z‖ ^ 2 ≤ 3 * (9121 + A) ^ 2 := by
      have hz' : ‖z‖ ≤ 9121 + A := hznorm
      have hZ' : ‖Z‖ ≤ 9121 + A := le_trans hZnorm (by linarith)
      nlinarith [norm_nonneg z, norm_nonneg Z, hz', hZ']
    have hX0 : 0 ≤ ‖z‖ ^ 2 + ‖z‖ * ‖Z‖ + ‖Z‖ ^ 2 := by positivity
    calc ‖z ^ 3 - Z ^ 3‖ ≤ ‖z - Z‖ * (‖z‖ ^ 2 + ‖z‖ * ‖Z‖ + ‖Z‖ ^ 2) := h
      _ ≤ (A * t ^ 4) * (3 * (9121 + A) ^ 2) := by
          refine le_trans (mul_le_mul_of_nonneg_right hzt hX0) ?_
          exact mul_le_mul_of_nonneg_left hb hAt
  have hsqW : ‖w ^ 2 - W ^ 2‖ ≤ B * t ^ 4 * (2 * (140113 + B)) := by
    have h := norm_sq_sub_sq w W
    have hb : ‖w‖ + ‖W‖ ≤ 2 * (140113 + B) := by
      have hw' : ‖w‖ ≤ 140113 + B := hwnorm
      have hW' : ‖W‖ ≤ 140113 + B := le_trans hWnorm (by linarith)
      linarith
    calc ‖w ^ 2 - W ^ 2‖ ≤ ‖w - W‖ * (‖w‖ + ‖W‖) := h
      _ ≤ (B * t ^ 4) * (2 * (140113 + B)) := by
          refine mul_le_mul hwt hb (by positivity) hBt
  have hsplit : (z ^ 3 - w ^ 2) / 1728 - (q - 24 * q ^ 2 + 252 * q ^ 3)
      = (z ^ 3 - Z ^ 3) / 1728 - (w ^ 2 - W ^ 2) / 1728
        + (Z ^ 3 - W ^ 2 - (1728 * q - 41472 * q ^ 2 + 435456 * q ^ 3)) / 1728 := by ring
  rw [hsplit]
  have h1 : ‖(z ^ 3 - Z ^ 3) / 1728‖ ≤ (A * t ^ 4 * (3 * (9121 + A) ^ 2)) / 1728 := by
    rw [norm_div, Complex.norm_ofNat]
    exact div_le_div_of_nonneg_right hcubeZ (by norm_num)
  have h2 : ‖(w ^ 2 - W ^ 2) / 1728‖ ≤ (B * t ^ 4 * (2 * (140113 + B))) / 1728 := by
    rw [norm_div, Complex.norm_ofNat]
    exact div_le_div_of_nonneg_right hsqW (by norm_num)
  have h3 : ‖(Z ^ 3 - W ^ 2 - (1728 * q - 41472 * q ^ 2 + 435456 * q ^ 3)) / 1728‖
      ≤ (739175913792 / 1728) * t ^ 4 := by
    rw [norm_div, Complex.norm_ofNat]
    calc ‖Z ^ 3 - W ^ 2 - (1728 * q - 41472 * q ^ 2 + 435456 * q ^ 3)‖ / 1728
        ≤ (739175913792 * t ^ 4) / 1728 := div_le_div_of_nonneg_right hZW (by norm_num)
      _ = (739175913792 / 1728) * t ^ 4 := by ring
  have hfin : ‖(z ^ 3 - Z ^ 3) / 1728 - (w ^ 2 - W ^ 2) / 1728
        + (Z ^ 3 - W ^ 2 - (1728 * q - 41472 * q ^ 2 + 435456 * q ^ 3)) / 1728‖ ≤
      ((3 * A * (9121 + A) ^ 2 + 2 * B * (140113 + B) + 739175913792) / 1728) * t ^ 4 := by
    calc ‖(z ^ 3 - Z ^ 3) / 1728 - (w ^ 2 - W ^ 2) / 1728
          + (Z ^ 3 - W ^ 2 - (1728 * q - 41472 * q ^ 2 + 435456 * q ^ 3)) / 1728‖
        ≤ ‖(z ^ 3 - Z ^ 3) / 1728 - (w ^ 2 - W ^ 2) / 1728‖
            + ‖(Z ^ 3 - W ^ 2 - (1728 * q - 41472 * q ^ 2 + 435456 * q ^ 3)) / 1728‖ :=
          norm_add_le _ _
      _ ≤ (‖(z ^ 3 - Z ^ 3) / 1728‖ + ‖(w ^ 2 - W ^ 2) / 1728‖)
            + ‖(Z ^ 3 - W ^ 2 - (1728 * q - 41472 * q ^ 2 + 435456 * q ^ 3)) / 1728‖ :=
          add_le_add_left (norm_sub_le _ _) _
      _ ≤ ((A * t ^ 4 * (3 * (9121 + A) ^ 2)) / 1728
            + (B * t ^ 4 * (2 * (140113 + B))) / 1728) + (739175913792 / 1728) * t ^ 4 := by
          linarith [h1, h2, h3]
      _ = ((3 * A * (9121 + A) ^ 2 + 2 * B * (140113 + B) + 739175913792) / 1728) * t ^ 4 := by
          ring
  simpa only [ht] using hfin

/-- `Δ = q - 24 q² + 252 q³ + O(‖q‖⁴)` on `{1 ≤ Im τ}`. -/
theorem DeltaFun_fourth_order :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖Work.Kernels.DeltaFun τ - (Work.Kernels.qParamFun τ
          - 24 * (Work.Kernels.qParamFun τ) ^ 2
          + 252 * (Work.Kernels.qParamFun τ) ^ 3)‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 4 := by
  obtain ⟨A, hA, hE4⟩ := E4Fun_fourth_order
  obtain ⟨B, hB, hE6⟩ := E6Fun_fourth_order
  refine ⟨(3 * A * (9121 + A) ^ 2 + 2 * B * (140113 + B) + 739175913792) / 1728 + 1,
    by positivity, fun τ hτ => ?_⟩
  have hρ1 : Real.exp (-(2 * Real.pi)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos]
  have hqle : ‖Work.Kernels.qParamFun τ‖ ≤ Real.exp (-(2 * Real.pi)) := norm_qParamFun_le τ hτ
  have hD : Work.Kernels.DeltaFun τ
      = (Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2) / 1728 := by
    have h1 : Work.Kernels.DeltaFun τ = ModularForm.discriminant τ := by
      rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant]
    rw [h1, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  have hz : ‖Work.Kernels.E4Fun τ - (1 + 240 * Work.Kernels.qParamFun τ
      + 2160 * (Work.Kernels.qParamFun τ) ^ 2
      + 6720 * (Work.Kernels.qParamFun τ) ^ 3)‖
      ≤ A * ‖Work.Kernels.qParamFun τ‖ ^ 4 := by
    convert hE4 τ hτ using 2 <;> ring
  have hw : ‖Work.Kernels.E6Fun τ - (1 - 504 * Work.Kernels.qParamFun τ
      - 16632 * (Work.Kernels.qParamFun τ) ^ 2
      - 122976 * (Work.Kernels.qParamFun τ) ^ 3)‖
      ≤ B * ‖Work.Kernels.qParamFun τ‖ ^ 4 := by
    convert hE6 τ hτ using 2 <;> push_cast <;> ring
  rw [hD]
  have hmain := delta_fourth_algebra hA.le hB.le hρ1 hqle hz hw
  have hs : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ 4 := by positivity
  calc ‖(Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2) / 1728
        - (Work.Kernels.qParamFun τ - 24 * Work.Kernels.qParamFun τ ^ 2
            + 252 * Work.Kernels.qParamFun τ ^ 3)‖
      ≤ ((3 * A * (9121 + A) ^ 2 + 2 * B * (140113 + B) + 739175913792) / 1728)
          * ‖Work.Kernels.qParamFun τ‖ ^ 4 := hmain
    _ ≤ ((3 * A * (9121 + A) ^ 2 + 2 * B * (140113 + B) + 739175913792) / 1728 + 1)
          * ‖Work.Kernels.qParamFun τ‖ ^ 4 := by nlinarith [hs]

/-! ## The second-order `q`-expansion of `j · q` on `{1 ≤ Im τ}` -/

/-- `j(τ) q = 1 + 744 q + 196884 q² + O(‖q‖³)` on `{1 ≤ Im τ}`. -/
theorem jqParam_second_order :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖Work.Kernels.jInvariantFun τ * Work.Kernels.qParamFun τ - 1
          - 744 * Work.Kernels.qParamFun τ
          - 196884 * (Work.Kernels.qParamFun τ) ^ 2‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  obtain ⟨CA, hCA, hE4⟩ := E4Fun_second_order
  obtain ⟨CD, hCD, hΔ4⟩ := DeltaFun_fourth_order
  obtain ⟨c0, hc0, hΔlow⟩ := DeltaFun_lower
  refine ⟨(3 * CA * (2401 + CA) ^ 2 + 13841107200 + 54152496 + 197629 * CD) / c0 + 1,
    by positivity, fun τ hτ => ?_⟩
  set q : ℂ := Work.Kernels.qParamFun τ with hqdef
  have hq0 : q ≠ 0 := by rw [hqdef]; exact qParamFun_ne_zero' τ
  set t : ℝ := ‖q‖ with ht
  have ht0 : 0 ≤ t := by rw [ht]; exact norm_nonneg _
  have ht1 : t ≤ 1 := by
    have h1 : ‖Work.Kernels.qParamFun τ‖ ≤ Real.exp (-(2 * Real.pi)) := norm_qParamFun_le τ hτ
    have h2 : Real.exp (-(2 * Real.pi)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos]
    rw [ht, hqdef]; linarith
  have hqpos : 0 < t := by rw [ht, hqdef, norm_qParamFun]; exact Real.exp_pos _
  have ht3 : 0 ≤ t ^ 3 := by positivity
  have hE4τ : ‖Work.Kernels.E4Fun τ - 1 - 240 * q - 2160 * q ^ 2‖ ≤ CA * t ^ 3 := by
    have h := hE4 τ hτ
    rw [← hqdef, ← ht] at h
    exact h
  have hΔ4τ : ‖Work.Kernels.DeltaFun τ - (q - 24 * q ^ 2 + 252 * q ^ 3)‖ ≤ CD * t ^ 4 := by
    have h := hΔ4 τ hτ
    rw [← hqdef, ← ht] at h
    exact h
  have hΔlowτ : c0 * t ≤ ‖Work.Kernels.DeltaFun τ‖ := by
    have h := hΔlow τ hτ
    rw [← hqdef, ← ht] at h
    exact h
  have hΔ0 : Work.Kernels.DeltaFun τ ≠ 0 := by
    rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant]
    exact ModularForm.discriminant_ne_zero τ
  set d : ℂ := Work.Kernels.DeltaFun τ / q with hddef
  have hd0 : d ≠ 0 := by rw [hddef]; exact div_ne_zero hΔ0 hq0
  have hdlow : c0 ≤ ‖d‖ := by
    rw [hddef, norm_div, le_div_iff₀ hqpos]
    exact hΔlowτ
  have hd : ‖d - (1 - 24 * q + 252 * q ^ 2)‖ ≤ CD * t ^ 3 := by
    have h1 : Work.Kernels.DeltaFun τ - (q - 24 * q ^ 2 + 252 * q ^ 3)
        = q * (d - (1 - 24 * q + 252 * q ^ 2)) := by
      rw [hddef, mul_sub, mul_div_cancel₀ (Work.Kernels.DeltaFun τ) hq0]
      ring
    have h2 : ‖q * (d - (1 - 24 * q + 252 * q ^ 2))‖ ≤ CD * t ^ 4 := by
      rw [← h1]; exact hΔ4τ
    rw [norm_mul, ← ht] at h2
    have h3 : t * (CD * t ^ 3) = CD * t ^ 4 := by ring
    have h4 : t * ‖d - (1 - 24 * q + 252 * q ^ 2)‖ ≤ t * (CD * t ^ 3) := by
      rw [h3]; exact h2
    exact le_of_mul_le_mul_left h4 hqpos
  -- the `O(q³)` bound for `E4³ - (1 + 720q + 179280q²)`
  have ha3 : ‖Work.Kernels.E4Fun τ ^ 3 - (1 + 720 * q + 179280 * q ^ 2)‖
      ≤ (3 * CA * (2401 + CA) ^ 2 + 13841107200) * t ^ 3 := by
    set P3 : ℂ := 1 + 240 * q + 2160 * q ^ 2 with hP3def
    have hP3 : ‖P3‖ ≤ 2401 := by
      rw [hP3def]
      have e1 : ‖(1 : ℂ)‖ = 1 := norm_one
      have e2 : ‖(240 : ℂ) * q‖ = 240 * t := by rw [norm_mul, Complex.norm_ofNat, ht]
      have e3 : ‖(2160 : ℂ) * q ^ 2‖ = 2160 * t ^ 2 := by
        rw [norm_mul, norm_pow, Complex.norm_ofNat, ht]
      calc ‖(1 : ℂ) + 240 * q + 2160 * q ^ 2‖
          ≤ ‖(1 : ℂ) + 240 * q‖ + ‖(2160 : ℂ) * q ^ 2‖ := norm_add_le _ _
        _ ≤ (‖(1 : ℂ)‖ + ‖(240 : ℂ) * q‖) + ‖(2160 : ℂ) * q ^ 2‖ :=
            add_le_add_left (norm_add_le _ _) _
        _ = (1 + 240 * t) + 2160 * t ^ 2 := by rw [e1, e2, e3]
        _ ≤ 2401 := by
            have q2 := mul_le_mul_of_nonneg_left (pow_le_one₀ ht0 ht1 (n := 2))
              (by norm_num : (0:ℝ) ≤ 2160)
            have q1 := mul_le_mul_of_nonneg_left ht1 (by norm_num : (0:ℝ) ≤ 240)
            linarith
    have hdev : ‖Work.Kernels.E4Fun τ - P3‖ ≤ CA * t ^ 3 := by
      rw [hP3def]; convert hE4τ using 2 <;> ring
    have hP3poly : ‖P3 ^ 3 - (1 + 720 * q + 179280 * q ^ 2)‖ ≤ 13841107200 * t ^ 3 := by
      have hid : P3 ^ 3 - (1 + 720 * q + 179280 * q ^ 2)
          = q ^ 3 * ((16934400 : ℂ) + 387244800 * q + 3359232000 * q ^ 2
              + 10077696000 * q ^ 3) := by rw [hP3def]; ring
      rw [hid, norm_mul, norm_pow]
      have hPb : ‖(16934400 : ℂ) + 387244800 * q + 3359232000 * q ^ 2
          + 10077696000 * q ^ 3‖ ≤ 13841107200 := by
        have e1 : ‖(16934400 : ℂ)‖ = 16934400 := by norm_num
        have e2 : ‖(387244800 : ℂ) * q‖ = 387244800 * t := by
          rw [norm_mul, Complex.norm_ofNat, ht]
        have e3 : ‖(3359232000 : ℂ) * q ^ 2‖ = 3359232000 * t ^ 2 := by
          rw [norm_mul, norm_pow, Complex.norm_ofNat, ht]
        have e4 : ‖(10077696000 : ℂ) * q ^ 3‖ = 10077696000 * t ^ 3 := by
          rw [norm_mul, norm_pow, Complex.norm_ofNat, ht]
        have e2b : 387244800 * t ≤ 387244800 := by
          have := mul_le_mul_of_nonneg_left ht1 (by norm_num : (0:ℝ) ≤ 387244800)
          linarith [this]
        have e3b : 3359232000 * t ^ 2 ≤ 3359232000 := by
          have := mul_le_mul_of_nonneg_left (pow_le_one₀ ht0 ht1 (n := 2))
            (by norm_num : (0:ℝ) ≤ 3359232000)
          linarith [this]
        have e4b : 10077696000 * t ^ 3 ≤ 10077696000 := by
          have := mul_le_mul_of_nonneg_left (pow_le_one₀ ht0 ht1 (n := 3))
            (by norm_num : (0:ℝ) ≤ 10077696000)
          linarith [this]
        calc ‖(16934400 : ℂ) + 387244800 * q + 3359232000 * q ^ 2 + 10077696000 * q ^ 3‖
            ≤ ‖(16934400 : ℂ) + 387244800 * q + 3359232000 * q ^ 2‖
                + ‖(10077696000 : ℂ) * q ^ 3‖ := norm_add_le _ _
          _ ≤ (‖(16934400 : ℂ) + 387244800 * q‖ + ‖(3359232000 : ℂ) * q ^ 2‖)
                + ‖(10077696000 : ℂ) * q ^ 3‖ := add_le_add_left (norm_add_le _ _) _
          _ ≤ ((‖(16934400 : ℂ)‖ + ‖(387244800 : ℂ) * q‖) + ‖(3359232000 : ℂ) * q ^ 2‖)
                + ‖(10077696000 : ℂ) * q ^ 3‖ :=
              add_le_add_left (add_le_add_left (norm_add_le _ _) _) _
          _ = (16934400 + 387244800 * t + 3359232000 * t ^ 2) + 10077696000 * t ^ 3 := by
              rw [e1, e2, e3, e4]
          _ ≤ 13841107200 := by linarith [e2b, e3b, e4b]
      calc t ^ 3 * ‖(16934400 : ℂ) + 387244800 * q + 3359232000 * q ^ 2
              + 10077696000 * q ^ 3‖
          = ‖q‖ ^ 3 * ‖(16934400 : ℂ) + 387244800 * q + 3359232000 * q ^ 2
              + 10077696000 * q ^ 3‖ := by rw [ht]
        _ ≤ ‖q‖ ^ 3 * 13841107200 := mul_le_mul_of_nonneg_left hPb (by positivity)
        _ = 13841107200 * t ^ 3 := by rw [ht]; ring
    have hcube : ‖Work.Kernels.E4Fun τ ^ 3 - P3 ^ 3‖ ≤ 3 * CA * (2401 + CA) ^ 2 * t ^ 3 := by
      have h := norm_cube_sub_cube (Work.Kernels.E4Fun τ) P3
      have hb : ‖Work.Kernels.E4Fun τ‖ ^ 2 + ‖Work.Kernels.E4Fun τ‖ * ‖P3‖ + ‖P3‖ ^ 2
          ≤ 3 * (2401 + CA) ^ 2 := by
        have hz' : ‖Work.Kernels.E4Fun τ‖ ≤ 2401 + CA := by
          have h2 : ‖Work.Kernels.E4Fun τ‖ ≤ ‖P3‖ + ‖Work.Kernels.E4Fun τ - P3‖ := by
            have h3 := norm_add_le P3 (Work.Kernels.E4Fun τ - P3)
            have h4 : P3 + (Work.Kernels.E4Fun τ - P3) = Work.Kernels.E4Fun τ := by ring
            rwa [h4] at h3
          have h5 : CA * t ^ 3 ≤ CA := by
            have := mul_le_mul_of_nonneg_left (pow_le_one₀ ht0 ht1 (n := 3)) hCA.le
            linarith [this]
          linarith [h2, hP3, h5]
        have hP3' : ‖P3‖ ≤ 2401 + CA := le_trans hP3 (by linarith)
        nlinarith [norm_nonneg (Work.Kernels.E4Fun τ), norm_nonneg P3, hz', hP3']
      have hX0 : 0 ≤ ‖Work.Kernels.E4Fun τ‖ ^ 2 + ‖Work.Kernels.E4Fun τ‖ * ‖P3‖ + ‖P3‖ ^ 2 :=
        by positivity
      calc ‖Work.Kernels.E4Fun τ ^ 3 - P3 ^ 3‖
          ≤ ‖Work.Kernels.E4Fun τ - P3‖
              * (‖Work.Kernels.E4Fun τ‖ ^ 2 + ‖Work.Kernels.E4Fun τ‖ * ‖P3‖ + ‖P3‖ ^ 2) := h
        _ ≤ (CA * t ^ 3) * (3 * (2401 + CA) ^ 2) := by
            refine le_trans (mul_le_mul_of_nonneg_right hdev hX0) ?_
            exact mul_le_mul_of_nonneg_left hb (mul_nonneg hCA.le (by positivity))
        _ = 3 * CA * (2401 + CA) ^ 2 * t ^ 3 := by ring
    have hsplit : Work.Kernels.E4Fun τ ^ 3 - (1 + 720 * q + 179280 * q ^ 2)
        = (Work.Kernels.E4Fun τ ^ 3 - P3 ^ 3)
          + (P3 ^ 3 - (1 + 720 * q + 179280 * q ^ 2)) := by ring
    rw [hsplit]
    calc ‖(Work.Kernels.E4Fun τ ^ 3 - P3 ^ 3) + (P3 ^ 3 - (1 + 720 * q + 179280 * q ^ 2))‖
        ≤ ‖Work.Kernels.E4Fun τ ^ 3 - P3 ^ 3‖ + ‖P3 ^ 3 - (1 + 720 * q + 179280 * q ^ 2)‖ :=
          norm_add_le _ _
      _ ≤ 3 * CA * (2401 + CA) ^ 2 * t ^ 3 + 13841107200 * t ^ 3 := add_le_add hcube hP3poly
      _ = (3 * CA * (2401 + CA) ^ 2 + 13841107200) * t ^ 3 := by ring
  -- the polynomial identity `(1+720q+179280q²) - (1-24q+252q²)(1+744q+196884q²)`
  have hpol : ‖(1 + 720 * q + 179280 * q ^ 2)
      - (1 - 24 * q + 252 * q ^ 2) * (1 + 744 * q + 196884 * q ^ 2)‖ ≤ 54152496 * t ^ 3 := by
    have hid : (1 + 720 * q + 179280 * q ^ 2)
        - (1 - 24 * q + 252 * q ^ 2) * (1 + 744 * q + 196884 * q ^ 2)
        = q ^ 3 * ((4537728 : ℂ) - 49614768 * q) := by ring
    rw [hid, norm_mul]
    have hb : ‖(4537728 : ℂ) - 49614768 * q‖ ≤ 54152496 := by
      have e1 : ‖(4537728 : ℂ)‖ = 4537728 := by norm_num
      have e2 : ‖(49614768 : ℂ) * q‖ = 49614768 * t := by rw [norm_mul, Complex.norm_ofNat, ht]
      have e2b : 49614768 * t ≤ 49614768 := by
        have := mul_le_mul_of_nonneg_left ht1 (by norm_num : (0:ℝ) ≤ 49614768)
        linarith [this]
      calc ‖(4537728 : ℂ) - 49614768 * q‖
          ≤ ‖(4537728 : ℂ)‖ + ‖(49614768 : ℂ) * q‖ := norm_sub_le _ _
        _ = 4537728 + 49614768 * t := by rw [e1, e2]
        _ ≤ 54152496 := by linarith [e2b]
    calc ‖q ^ 3‖ * ‖(4537728 : ℂ) - 49614768 * q‖
        ≤ t ^ 3 * 54152496 := by
          rw [norm_pow, ht]
          exact mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 54152496 * t ^ 3 := by ring
  have hT2b : ‖(1 : ℂ) + 744 * q + 196884 * q ^ 2‖ ≤ 197629 := by
    have e1 : ‖(1 : ℂ)‖ = 1 := norm_one
    have e2 : ‖(744 : ℂ) * q‖ = 744 * t := by rw [norm_mul, Complex.norm_ofNat, ht]
    have e3 : ‖(196884 : ℂ) * q ^ 2‖ = 196884 * t ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ht]
    have e2b : 744 * t ≤ 744 := by
      have := mul_le_mul_of_nonneg_left ht1 (by norm_num : (0:ℝ) ≤ 744); linarith [this]
    have e3b : 196884 * t ^ 2 ≤ 196884 := by
      have := mul_le_mul_of_nonneg_left (pow_le_one₀ ht0 ht1 (n := 2))
        (by norm_num : (0:ℝ) ≤ 196884)
      linarith [this]
    calc ‖(1 : ℂ) + 744 * q + 196884 * q ^ 2‖
        ≤ ‖(1 : ℂ) + 744 * q‖ + ‖(196884 : ℂ) * q ^ 2‖ := norm_add_le _ _
      _ ≤ (‖(1 : ℂ)‖ + ‖(744 : ℂ) * q‖) + ‖(196884 : ℂ) * q ^ 2‖ :=
          add_le_add_left (norm_add_le _ _) _
      _ = (1 + 744 * t) + 196884 * t ^ 2 := by rw [e1, e2, e3]
      _ ≤ 197629 := by linarith [e2b, e3b]
  -- identify `j q = E4³ / d`
  have hjq : Work.Kernels.jInvariantFun τ * q = Work.Kernels.E4Fun τ ^ 3 / d := by
    rw [show Work.Kernels.jInvariantFun τ
        = Work.Kernels.E4Fun τ ^ 3 / Work.Kernels.DeltaFun τ from rfl]
    rw [hddef]
    field_simp
  rw [hjq]
  have hsplit : Work.Kernels.E4Fun τ ^ 3 / d - 1 - 744 * q - 196884 * q ^ 2
      = (Work.Kernels.E4Fun τ ^ 3 - (1 + 720 * q + 179280 * q ^ 2)) / d
        + ((1 + 720 * q + 179280 * q ^ 2)
            - (1 - 24 * q + 252 * q ^ 2) * (1 + 744 * q + 196884 * q ^ 2)) / d
        + (1 + 744 * q + 196884 * q ^ 2) * ((1 - 24 * q + 252 * q ^ 2) - d) / d := by
    field_simp
    ring
  rw [hsplit]
  have hA1 : ‖(Work.Kernels.E4Fun τ ^ 3 - (1 + 720 * q + 179280 * q ^ 2)) / d‖
      ≤ (3 * CA * (2401 + CA) ^ 2 + 13841107200) * t ^ 3 / c0 := by
    rw [norm_div]
    exact div_le_div₀ (by positivity) ha3 hc0 hdlow
  have hA2 : ‖((1 + 720 * q + 179280 * q ^ 2)
      - (1 - 24 * q + 252 * q ^ 2) * (1 + 744 * q + 196884 * q ^ 2)) / d‖
      ≤ 54152496 * t ^ 3 / c0 := by
    rw [norm_div]
    exact div_le_div₀ (by positivity) hpol hc0 hdlow
  have hA3 : ‖(1 + 744 * q + 196884 * q ^ 2) * ((1 - 24 * q + 252 * q ^ 2) - d) / d‖
      ≤ 197629 * CD * t ^ 3 / c0 := by
    rw [show (1 + 744 * q + 196884 * q ^ 2) * ((1 - 24 * q + 252 * q ^ 2) - d) / d
        = (1 + 744 * q + 196884 * q ^ 2) * (((1 - 24 * q + 252 * q ^ 2) - d) / d) from by ring]
    rw [norm_mul, norm_div]
    rw [show ‖(1 - 24 * q + 252 * q ^ 2) - d‖ = ‖d - (1 - 24 * q + 252 * q ^ 2)‖ from
      norm_sub_rev _ _]
    have hinner : ‖d - (1 - 24 * q + 252 * q ^ 2)‖ / ‖d‖ ≤ CD * t ^ 3 / c0 :=
      div_le_div₀ (by positivity) hd hc0 hdlow
    calc ‖(1 + 744 * q + 196884 * q ^ 2)‖ * (‖d - (1 - 24 * q + 252 * q ^ 2)‖ / ‖d‖)
        ≤ 197629 * (CD * t ^ 3 / c0) := mul_le_mul hT2b hinner (by positivity) (by norm_num)
      _ = 197629 * CD * t ^ 3 / c0 := by ring
  calc ‖(Work.Kernels.E4Fun τ ^ 3 - (1 + 720 * q + 179280 * q ^ 2)) / d
        + ((1 + 720 * q + 179280 * q ^ 2)
            - (1 - 24 * q + 252 * q ^ 2) * (1 + 744 * q + 196884 * q ^ 2)) / d
        + (1 + 744 * q + 196884 * q ^ 2) * ((1 - 24 * q + 252 * q ^ 2) - d) / d‖
      ≤ (3 * CA * (2401 + CA) ^ 2 + 13841107200) * t ^ 3 / c0
          + 54152496 * t ^ 3 / c0 + 197629 * CD * t ^ 3 / c0 := by
        have h1 := norm_add_le
          ((Work.Kernels.E4Fun τ ^ 3 - (1 + 720 * q + 179280 * q ^ 2)) / d
            + ((1 + 720 * q + 179280 * q ^ 2)
                - (1 - 24 * q + 252 * q ^ 2) * (1 + 744 * q + 196884 * q ^ 2)) / d)
          ((1 + 744 * q + 196884 * q ^ 2) * ((1 - 24 * q + 252 * q ^ 2) - d) / d)
        have h2 := norm_add_le
          ((Work.Kernels.E4Fun τ ^ 3 - (1 + 720 * q + 179280 * q ^ 2)) / d)
          (((1 + 720 * q + 179280 * q ^ 2)
              - (1 - 24 * q + 252 * q ^ 2) * (1 + 744 * q + 196884 * q ^ 2)) / d)
        linarith [h1, h2, hA1, hA2, hA3]
    _ ≤ ((3 * CA * (2401 + CA) ^ 2 + 13841107200 + 54152496 + 197629 * CD) / c0 + 1) * t ^ 3 := by
        rw [show (3 * CA * (2401 + CA) ^ 2 + 13841107200) * t ^ 3 / c0
              + 54152496 * t ^ 3 / c0 + 197629 * CD * t ^ 3 / c0
            = ((3 * CA * (2401 + CA) ^ 2 + 13841107200 + 54152496 + 197629 * CD) / c0)
              * t ^ 3 from by ring]
        have hnn : (0:ℝ) ≤ (3 * CA * (2401 + CA) ^ 2 + 13841107200 + 54152496 + 197629 * CD) / c0 :=
          div_nonneg (by positivity) hc0.le
        nlinarith [ht3, hnn]

/-! ## The `τ`-atoms of the funnel at second order -/

/-- **Second-order `q`-expansions of the `τ`-atoms on the funnel.**

With `q = qParamFun τ` (`‖q‖ = e^{-2π Im τ}`), the five `τ`-atoms of the funnel analysis
satisfy, on the funnel `𝔽 = {τ ∈ 𝓓 : 2 ≤ Im τ}`,

  `E₂ = 1 - 24q - 72q² + O((scale τ)^N ‖q‖³)`,
  `E₄ = 1 + 240q + 2160q² + O((scale τ)^N ‖q‖³)`,
  `E₆ = 1 - 504q - 16632q² + O((scale τ)^N ‖q‖³)`,
  `Δ  = q - 24q² + O((scale τ)^N ‖q‖³)`,
  `j·q = 1 + 744q + 196884q² + O((scale τ)^N ‖q‖³)`

(the last one stated multiplied by `q` to avoid the pole of `j = q^{-1}+744+196884q+…`).
All coefficients are the standard ones (`σ₁(2)=3`, `240σ₃(2)=2160`, `504σ₅(2)=16632`,
`Δ = q∏(1-qⁿ)^24 = q-24q²+252q³-…`, `j = E₄³/Δ = q⁻¹+744+196884q+…`); since
`‖q‖ ≤ e^{-4π} < 1` uniformly on the funnel, each tail converges absolutely and is
`O(‖q‖³)` with a τ-independent constant, so `N = 0` suffices (the `(scale τ)^N` slack is
harmless).  The first-order versions are already proved and axiom-clean
(`Work.Residues.E4FunSecondOrder`, `Work.Residues.E6FunSecondOrder`,
`Work.Asymptotics.E2Fun_two_term`, `Work.Asymptotics.DeltaFun_isBigOq`), as are the
boundedness facts used here (`E2Fun_bdd`, `E4Fun_bdd`, `E6Fun_bdd` from
`FunnelNumerics/E4_funnel_bounds.lean`, `DeltaFun_upper_sharp`,
`exists_Delta_Funnel_lower`, `exists_jInvariantFun_Funnel_bound`).

This is the `τ`-side input needed by the `d = 8` second-order atom algebra for the funnel
bracket (the `ψ`-side is `Work.Asymptotics.KhatE1Core.psi_second_order`); the completed
`d = 24` analogue is `Work.Asymptotics.KMinusFunnelMainBoundDecay` with the `KMFD*` files,
which use exactly such truncated expansions. -/
theorem funnel_tauAtom_second_order :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ
          + 72 * (Work.Kernels.qParamFun τ) ^ 2‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 3 ∧
      ‖Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ
          - 2160 * (Work.Kernels.qParamFun τ) ^ 2‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 3 ∧
      ‖Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ
          + 16632 * (Work.Kernels.qParamFun τ) ^ 2‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 3 ∧
      ‖Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ
          + 24 * (Work.Kernels.qParamFun τ) ^ 2‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 3 ∧
      ‖Work.Kernels.jInvariantFun τ * Work.Kernels.qParamFun τ - 1
          - 744 * Work.Kernels.qParamFun τ
          - 196884 * (Work.Kernels.qParamFun τ) ^ 2‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  obtain ⟨C2, hC2, h2⟩ := E2Fun_second_order
  obtain ⟨C4, hC4, h4⟩ := E4Fun_second_order
  obtain ⟨C6, hC6, h6⟩ := E6Fun_second_order
  obtain ⟨Cd, hCd, hd⟩ := DeltaFun_fourth_order
  obtain ⟨Cj, hCj, hj⟩ := jqParam_second_order
  set C : ℝ := C2 + C4 + C6 + (Cd + 252) + Cj + 1 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have h2C : C2 ≤ C := by rw [hCdef]; linarith [hC4.le, hC6.le, hCd.le, hCj.le]
  have h4C : C4 ≤ C := by rw [hCdef]; linarith [hC2.le, hC6.le, hCd.le, hCj.le]
  have h6C : C6 ≤ C := by rw [hCdef]; linarith [hC2.le, hC4.le, hCd.le, hCj.le]
  have hdC : Cd + 252 ≤ C := by rw [hCdef]; linarith [hC2.le, hC4.le, hC6.le, hCj.le]
  have hjC : Cj ≤ C := by rw [hCdef]; linarith [hC2.le, hC4.le, hC6.le, hCd.le]
  refine ⟨C, 0, hCpos, le_refl 0, fun τ hτ => ?_⟩
  have h1 : 1 ≤ τ.im := Funnel.im_one hτ
  have hscale : (Work.Kernels.scale τ) ^ (0 : ℝ) = 1 := Real.rpow_zero _
  have hq3 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ 3 := by positivity
  have key : ∀ {a : ℝ} {e : ℂ}, a ≤ C →
      ‖e‖ ≤ a * ‖Work.Kernels.qParamFun τ‖ ^ 3 →
      ‖e‖ ≤ C * (Work.Kernels.scale τ) ^ (0 : ℝ) * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
    intro a e ha he
    rw [hscale, mul_one]
    nlinarith [hq3, he, ha]
  have hq1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := by
    have hql := norm_qParamFun_le τ h1
    have h1' : Real.exp (-(2 * Real.pi)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos]
    linarith
  refine ⟨key h2C (h2 τ h1), key h4C (h4 τ h1), key h6C (h6 τ h1), ?_, key hjC (hj τ h1)⟩
  -- the `Δ` case needs one term of the fourth-order expansion to be absorbed
  have hq4 : ‖Work.Kernels.qParamFun τ‖ ^ 4 ≤ ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
    calc ‖Work.Kernels.qParamFun τ‖ ^ 4
        = ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Kernels.qParamFun τ‖ := by ring
      _ ≤ ‖Work.Kernels.qParamFun τ‖ ^ 3 * 1 :=
          mul_le_mul_of_nonneg_left hq1 (by positivity)
      _ = ‖Work.Kernels.qParamFun τ‖ ^ 3 := by ring
  have hdd := hd τ h1
  rw [hscale, mul_one]
  have hsplit : Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ
        + 24 * (Work.Kernels.qParamFun τ) ^ 2
      = (Work.Kernels.DeltaFun τ - (Work.Kernels.qParamFun τ
            - 24 * (Work.Kernels.qParamFun τ) ^ 2
            + 252 * (Work.Kernels.qParamFun τ) ^ 3))
        + 252 * (Work.Kernels.qParamFun τ) ^ 3 := by ring
  rw [hsplit]
  have h252 : ‖(252 : ℂ) * Work.Kernels.qParamFun τ ^ 3‖
      = 252 * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
  calc ‖(Work.Kernels.DeltaFun τ - (Work.Kernels.qParamFun τ
            - 24 * (Work.Kernels.qParamFun τ) ^ 2
            + 252 * (Work.Kernels.qParamFun τ) ^ 3))
        + 252 * (Work.Kernels.qParamFun τ) ^ 3‖
      ≤ ‖Work.Kernels.DeltaFun τ - (Work.Kernels.qParamFun τ
            - 24 * (Work.Kernels.qParamFun τ) ^ 2
            + 252 * (Work.Kernels.qParamFun τ) ^ 3)‖
          + ‖(252 : ℂ) * Work.Kernels.qParamFun τ ^ 3‖ := norm_add_le _ _
    _ ≤ Cd * ‖Work.Kernels.qParamFun τ‖ ^ 4 + 252 * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
        rw [h252]
        exact add_le_add hdd (le_refl _)
    _ ≤ (Cd + 252) * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by nlinarith [hq3, hq4]
    _ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by nlinarith [hq3, hdC]

end

end Work.Asymptotics

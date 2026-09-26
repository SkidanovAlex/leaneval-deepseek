import Mathlib
import Submission.Work.Residues.ThetaExpansion
import Submission.Work.Residues.DeltaExpansion

/-!
# The second-order cusp expansion of `1 / Δ`

With `E = e^{πiτ}` (`‖E‖ = e^{-π Im τ}`) and `q = E² = e^{2πiτ}` the modular discriminant has
`q`-expansion
`Δ = q - 24 q² + O(q³)`,
so that
`1/Δ = q⁻¹ + 24 + O(q)`,
i.e. `1/Δ(z) = (E(z)⁻¹)² + 24 + O(‖E(z)‖²)` for `Im z ≥ 1`.  This file proves that estimate
(`Work.Asymptotics.cusp_invDelta`), with the explicit constant `C₃ + (24 + C₃)²/c`, where `C₃`
is the constant of the third-order expansion of `Δ` and `c` that of the lower bound
`‖Δ‖ ≥ c ‖q‖` on `Im ≥ 1` (proved below, privately, since `Work.Residues.ThetaLowerBound`
clashes with the `theta_lower_bound` module).

The third-order expansion `Δ = q - 24q² + O(q³)` is obtained from the third-order cusp
expansions
`E₄ = 1 + 240 q + 2160 q² + O(q³)`,  `E₆ = 1 - 504 q - 16632 q² + O(q³)`
(each an instance of the tail estimate `Work.Residues.qExpansion_tail_bound` applied to the
`q`-expansion coefficients `240 σ₃(m)` and `-504 σ₅(m)`) together with the identity
`Δ = (E₄³ - E₆²)/1728`.  Since `Δ^{(3)}(q) = q - 24 q²` exactly, and the `q²`-coefficients of
`E₄` and `E₆` are what they are, `Δ = q(1 + w)` with `w = -24q + O(q²)`, and the inversion
uses the algebraic identity
`1/Δ - (q⁻¹ + 24) = q⁻¹ (w²/(1+w)) - q⁻¹ (Δ - q + 24q²)/q`,
in which the first term is `O(q)` because `q/Δ = 1/(1+w)` is bounded by the lower bound for `Δ`
and the second because `Δ - q + 24q² = O(q³)`.
-/

namespace Work.Asymptotics

open UpperHalfPlane ModularForm
open scoped MatrixGroups Manifold _root_.Modular ModularForm

noncomputable section

/-! ## Elementary norm estimates -/

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

/-! ## A lower bound for `Δ` on `Im ≥ 1`

`Δ = q ∏ (1 - q^{n+1})^24` with `‖q‖ = e^{-2π Im}` and the product `≥ 2/3` for `Im ≥ 1`, so
`‖Δ‖ ≥ (2/3)^24 e^{-2π Im}`.  (Repeated here, privately, because the module
`Work.Residues.ThetaLowerBound` clashes with the `theta_lower_bound` module imported by
`Work.Residues.ThetaExpansion`.) -/

private lemma one_sub_sum_le_prod_c {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      have hi0 : 0 ≤ a i := ha i (Finset.mem_insert_self i s)
      have hs0 : 0 ≤ ∑ j ∈ s, a j :=
        Finset.sum_nonneg fun j hj => ha j (Finset.mem_insert_of_mem hj)
      have hih := ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
        (fun j hj => ha1 j (Finset.mem_insert_of_mem hj))
      have h1 : (1 - a i) * (1 - ∑ j ∈ s, a j) ≤ (1 - a i) * ∏ j ∈ s, (1 - a j) :=
        mul_le_mul_of_nonneg_left hih (by linarith [ha1 i (Finset.mem_insert_self i s)])
      nlinarith [h1, mul_nonneg hi0 hs0]

private lemma geom_sum_range_le_c {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    ∑ i ∈ Finset.range N, r ^ i ≤ (1 - r)⁻¹ := by
  have hs : Summable fun i : ℕ => r ^ i := summable_geometric_of_lt_one hr0 hr1
  calc ∑ i ∈ Finset.range N, r ^ i ≤ ∑' i : ℕ, r ^ i :=
        hs.sum_le_tsum _ (fun i _ => pow_nonneg hr0 i)
    _ = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1

private lemma multipliable_one_sub_eta_q_c (z : UpperHalfPlane) :
    Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n (z:ℂ)) := by
  have hq_lt : ‖Function.Periodic.qParam 1 (z:ℂ)‖ < 1 :=
    Function.Periodic.norm_qParam_lt_one one_pos (by rw [UpperHalfPlane.coe_im]; exact z.im_pos)
  exact ModularForm.multipliable_one_sub_pow hq_lt

private lemma tprod_one_sub_eta_q_lower_c (z : UpperHalfPlane) (hz : 1 ≤ z.im) :
    (2/3 : ℝ) ≤ ‖∏' n : ℕ, (1 - ModularForm.eta_q n (z:ℂ))‖ := by
  set q : ℂ := Function.Periodic.qParam 1 (z:ℂ) with hqdef
  have hq_lt : ‖q‖ < 1 := by
    rw [hqdef]
    exact Function.Periodic.norm_qParam_lt_one one_pos (by rw [UpperHalfPlane.coe_im]; exact z.im_pos)
  have hr0 : 0 ≤ ‖q‖ := norm_nonneg _
  have hq_le1 : ‖q‖ ≤ 1 := le_of_lt hq_lt
  have hq_le : ‖q‖ ≤ 1/4 := by
    rw [hqdef, Function.Periodic.norm_qParam]
    have h4 : (4:ℝ) ≤ Real.exp (2 * Real.pi) := by
      have h6 : Real.exp 6 ≤ Real.exp (2 * Real.pi) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three])
      have h7 : (7:ℝ) ≤ Real.exp 6 := by
        have := Real.add_one_le_exp (6:ℝ); linarith
      linarith
    have harg : 2 * Real.pi ≤ 2 * Real.pi * (z:ℂ).im := by
      rw [UpperHalfPlane.coe_im]; nlinarith [Real.pi_pos, hz]
    have hge : (4:ℝ) ≤ Real.exp (2 * Real.pi * (z:ℂ).im) :=
      h4.trans (Real.exp_le_exp.mpr harg)
    have harg2 : -2 * Real.pi * (z:ℂ).im / 1 = -(2*Real.pi*(z:ℂ).im) := by ring
    rw [harg2, Real.exp_neg, show (1/4:ℝ) = (4:ℝ)⁻¹ by norm_num]
    exact (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 4)).mpr hge
  have hmul : Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n (z:ℂ)) :=
    multipliable_one_sub_eta_q_c z
  have hlim := hmul.tendsto_prod_tprod_nat
  refine ge_of_tendsto hlim.norm ?_
  filter_upwards with N
  have hfac : ∀ n : ℕ, 1 - ‖q‖^(n+1) ≤ ‖(1 - ModularForm.eta_q n (z:ℂ))‖ := by
    intro n
    have hnorm : ‖ModularForm.eta_q n (z:ℂ)‖ = ‖q‖^(n+1) := by
      simp [ModularForm.eta_q, hqdef, norm_pow]
    have h := norm_add_le (1 - ModularForm.eta_q n (z:ℂ)) (ModularForm.eta_q n (z:ℂ))
    rw [sub_add_cancel, norm_one] at h
    rw [hnorm] at h
    linarith
  have hgeom : ∑ n ∈ Finset.range N, ‖q‖^(n+1) ≤ 1/3 := by
    have heq : ∑ n ∈ Finset.range N, ‖q‖^(n+1) = ‖q‖ * ∑ n ∈ Finset.range N, ‖q‖^n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [pow_succ']
    rw [heq]
    have hg := geom_sum_range_le_c hr0 hq_lt N
    have h1 : ‖q‖ * (∑ n ∈ Finset.range N, ‖q‖^n) ≤ ‖q‖ * (1 - ‖q‖)⁻¹ :=
      mul_le_mul_of_nonneg_left hg hr0
    refine h1.trans ?_
    have hden : 0 < 1 - ‖q‖ := by linarith
    exact (div_le_iff₀ hden).mpr (by linarith [hq_le])
  have h1 : ∏ n ∈ Finset.range N, (1 - ‖q‖^(n+1))
      ≤ ∏ n ∈ Finset.range N, ‖(1 - ModularForm.eta_q n (z:ℂ))‖ :=
    Finset.prod_le_prod₀ (fun n hn => by
      have : ‖q‖^(n+1) ≤ ‖q‖^1 := pow_le_pow_of_le_one hr0 hq_le1 (by omega)
      linarith) (fun n hn => hfac n)
  have h2 : 1 - ∑ n ∈ Finset.range N, ‖q‖^(n+1)
      ≤ ∏ n ∈ Finset.range N, (1 - ‖q‖^(n+1)) :=
    one_sub_sum_le_prod_c _ _ (fun n hn => by positivity) (fun n hn => by
      have : ‖q‖^(n+1) ≤ ‖q‖^1 := pow_le_pow_of_le_one hr0 hq_le1 (by omega)
      linarith)
  rw [norm_prod]
  linarith

/-- `‖Δ z‖ ≥ (2/3)^24 e^{-2π Im z}` for `Im z ≥ 1`. -/
private lemma DeltaFun_lower_cusp_priv : ∃ c : ℝ, 0 < c ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
    c * Real.exp (-(2 * Real.pi * z.im)) ≤ ‖Work.Kernels.DeltaFun z‖ := by
  refine ⟨(2/3 : ℝ)^24, by norm_num, ?_⟩
  intro z hz
  have hA := tprod_one_sub_eta_q_lower_c z hz
  have hmul := multipliable_one_sub_eta_q_c z
  have hnormq : ‖Function.Periodic.qParam 1 (z:ℂ)‖ = Real.exp (-(2*Real.pi*z.im)) := by
    rw [Function.Periodic.norm_qParam, UpperHalfPlane.coe_im]
    norm_num
  calc (2/3 : ℝ)^24 * Real.exp (-(2 * Real.pi * z.im))
      = Real.exp (-(2 * Real.pi * z.im)) * (2/3 : ℝ)^24 := by ring
    _ ≤ Real.exp (-(2 * Real.pi * z.im))
          * ‖∏' n : ℕ, (1 - ModularForm.eta_q n (z:ℂ))‖^24 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) hA 24) (Real.exp_nonneg _)
    _ = ‖Work.Kernels.DeltaFun z‖ := by
        rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant,
            ModularForm.discriminant_eq_q_prod, norm_mul, hmul.tprod_pow, norm_pow, hnormq]

/-! ## Third-order cusp expansions of `E₄` and `E₆` -/

/-- Coefficient bound for the `q`-expansion of `E₄`: `‖c_m‖ = 240 σ₃(m) ≤ 240 m⁴`. -/
private lemma E4_coeff_bound (m : ℕ) (hm : 3 ≤ m) :
    ‖(UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff m‖ ≤ 240 * (m : ℝ) ^ 4 := by
  have hm0 : m ≠ 0 := by omega
  rw [Work.Modular.E4_qExpansion_coeff m, if_neg hm0, norm_mul, Complex.norm_ofNat,
    Complex.norm_natCast]
  have h' : ArithmeticFunction.sigma 3 m ≤ m ^ 4 := by
    simpa using ArithmeticFunction.sigma_le_pow_succ 3 m
  have h'' : (ArithmeticFunction.sigma 3 m : ℝ) ≤ (m : ℝ) ^ 4 := by exact_mod_cast h'
  exact mul_le_mul_of_nonneg_left h'' (by norm_num)

/-- `E₄ - (1 + 240q + 2160q²) = O(‖q‖³)` on the cusp region. -/
private theorem E4FunThirdOrder :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.E4Fun τ -
          (1 + 240 * Work.Kernels.qParamFun τ + 2160 * Work.Kernels.qParamFun τ ^ 2)‖ ≤
        C * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Residues.qExpansion_tail_bound (r := 3)
    (f := (⇑ModularForm.E₄ : ℍ → ℂ))
    (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL)
    (ModularForm.holo' ModularForm.E₄) (ModularFormClass.bdd_at_infty ModularForm.E₄)
    240 4 (by norm_num) E4_coeff_bound
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h0 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff 0 = 1 := by
    simpa using Work.Modular.E4_qExpansion_coeff 0
  have h1 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff 1 = 240 := by
    rw [Work.Modular.E4_qExpansion_coeff 1, if_neg (by norm_num : (1 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  have h2 : (UpperHalfPlane.qExpansion 1 (⇑ModularForm.E₄ : ℍ → ℂ)).coeff 2 = 2160 := by
    rw [Work.Modular.E4_qExpansion_coeff 2, if_neg (by norm_num : (2 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  have hmain := h τ hτ
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, h0, h1, h2] at hmain
  have hq : Function.Periodic.qParam 1 (τ : ℂ) = Work.Kernels.qParamFun τ := by
    simp [Work.Kernels.qParamFun, Function.Periodic.qParam]
  rw [hq] at hmain
  convert hmain using 2
  ring

/-- `E₆ - (1 - 504q - 16632q²) = O(‖q‖³)` on the cusp region. -/
private theorem E6FunThirdOrder :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.E6Fun τ -
          (1 - 504 * Work.Kernels.qParamFun τ - 16632 * Work.Kernels.qParamFun τ ^ 2)‖ ≤
        C * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  obtain ⟨C, hC, h⟩ := Work.Residues.qExpansion_tail_bound (r := 3)
    (f := Work.Kernels.E6Fun)
    (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₆ one_mem_strictPeriods_SL)
    (ModularForm.holo' ModularForm.E₆) (ModularFormClass.bdd_at_infty ModularForm.E₆)
    504 6 (by norm_num) (fun m hm => Work.Residues.E6_qExpansion_coeff_tail m (by omega))
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h0 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 0 = 1 := by
    rw [Work.Modular.E6_qExpansion_coeff]; simp
  have h1 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 1 = -504 := by
    rw [Work.Modular.E6_qExpansion_coeff]
    norm_num [ArithmeticFunction.sigma_one]
  have h2 : (UpperHalfPlane.qExpansion 1 Work.Kernels.E6Fun).coeff 2 = -16632 := by
    rw [Work.Modular.E6_qExpansion_coeff, if_neg (by norm_num : (2 : ℕ) ≠ 0)]
    norm_num [ArithmeticFunction.sigma]
  have hmain := h τ hτ
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, h0, h1, h2] at hmain
  have hq : Function.Periodic.qParam 1 (τ : ℂ) = Work.Kernels.qParamFun τ := by
    simp [Function.Periodic.qParam, Work.Kernels.qParamFun]
  rw [hq] at hmain
  convert hmain using 2
  ring

/-! ## The third-order expansion of `Δ` -/

/-- **Algebraic core.**  If `z = 1 + 240q + 2160q² + O(q³)` and `w = 1 - 504q - 16632q² + O(q³)`
then `(z³ - w²)/1728 = q - 24q² + O(q³)`.  This is the pointwise identity
`Δ = (E₄³ - E₆²)/1728` combined with the Taylor expansion of the cube and the square: the
truncated polynomial `Z³ - W²` equals `1728q - 41472q²` plus `q³` times an explicit polynomial
whose coefficients are bounded because `‖q‖ ≤ 1`. -/
private lemma delta_third_algebra {A B ρ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ1 : ρ ≤ 1) {q z w : ℂ} (hq : ‖q‖ ≤ ρ)
    (hz : ‖z - (1 + 240 * q + 2160 * q ^ 2)‖ ≤ A * ‖q‖ ^ 3)
    (hw : ‖w - (1 - 504 * q - 16632 * q ^ 2)‖ ≤ B * ‖q‖ ^ 3) :
    ‖(z ^ 3 - w ^ 2) / 1728 - (q - 24 * q ^ 2)‖ ≤
      ((3 * A * (2401 + A) ^ 2 + 2 * B * (17137 + B) + 13547718720) / 1728) * ‖q‖ ^ 3 := by
  set t : ℝ := ‖q‖ with ht
  have ht0 : 0 ≤ t := norm_nonneg _
  have ht1 : t ≤ 1 := le_trans hq hρ1
  set Z : ℂ := 1 + 240 * q + 2160 * q ^ 2 with hZ
  set W : ℂ := 1 - 504 * q - 16632 * q ^ 2 with hW
  have hzt : ‖z - Z‖ ≤ A * t ^ 3 := by rw [ht]; exact hz
  have hwt : ‖w - W‖ ≤ B * t ^ 3 := by rw [ht]; exact hw
  have hAt : 0 ≤ A * t ^ 3 := mul_nonneg hA (by positivity)
  have hBt : 0 ≤ B * t ^ 3 := mul_nonneg hB (by positivity)
  have ht3 : t ^ 3 ≤ 1 := pow_le_one₀ ht0 ht1
  have ht2 : t ^ 2 ≤ 1 := pow_le_one₀ ht0 ht1
  -- norms of the polynomial parts
  have hZnorm : ‖Z‖ ≤ 2401 := by
    rw [hZ]
    have e1 : ‖(1 : ℂ)‖ = 1 := norm_one
    have e2 : ‖(240 : ℂ) * q‖ = 240 * t := by rw [norm_mul, Complex.norm_ofNat, ht]
    have e3 : ‖(2160 : ℂ) * q ^ 2‖ = 2160 * t ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ht]
    calc ‖(1 : ℂ) + 240 * q + 2160 * q ^ 2‖
        ≤ ‖(1 : ℂ) + 240 * q‖ + ‖(2160 : ℂ) * q ^ 2‖ := norm_add_le _ _
      _ ≤ (‖(1 : ℂ)‖ + ‖(240 : ℂ) * q‖) + ‖(2160 : ℂ) * q ^ 2‖ :=
          add_le_add_left (norm_add_le _ _) _
      _ = 1 + 240 * t + 2160 * t ^ 2 := by rw [e1, e2, e3]
      _ ≤ 2401 := by nlinarith [ht0, ht1]
  have hWnorm : ‖W‖ ≤ 17137 := by
    rw [hW]
    have e1 : ‖(1 : ℂ)‖ = 1 := norm_one
    have e2 : ‖(504 : ℂ) * q‖ = 504 * t := by rw [norm_mul, Complex.norm_ofNat, ht]
    have e3 : ‖(16632 : ℂ) * q ^ 2‖ = 16632 * t ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ht]
    calc ‖(1 : ℂ) - 504 * q - 16632 * q ^ 2‖
        ≤ ‖(1 : ℂ) - 504 * q‖ + ‖(16632 : ℂ) * q ^ 2‖ := norm_sub_le _ _
      _ ≤ (‖(1 : ℂ)‖ + ‖(504 : ℂ) * q‖) + ‖(16632 : ℂ) * q ^ 2‖ :=
          add_le_add_left (norm_sub_le _ _) _
      _ = 1 + 504 * t + 16632 * t ^ 2 := by rw [e1, e2, e3]
      _ ≤ 17137 := by nlinarith [ht0, ht1]
  have hznorm : ‖z‖ ≤ 2401 + A := by
    have h1 : ‖z‖ ≤ ‖Z‖ + ‖z - Z‖ := by
      have h := norm_add_le Z (z - Z)
      have h' : Z + (z - Z) = z := by ring
      rwa [h'] at h
    have h2 : A * t ^ 3 ≤ A := by nlinarith [hA, ht3]
    linarith
  have hwnorm : ‖w‖ ≤ 17137 + B := by
    have h1 : ‖w‖ ≤ ‖W‖ + ‖w - W‖ := by
      have h := norm_add_le W (w - W)
      have h' : W + (w - W) = w := by ring
      rwa [h'] at h
    have h2 : B * t ^ 3 ≤ B := by nlinarith [hB, ht3]
    linarith
  -- the truncated polynomial expansion of `Z³ - W²`
  have hid : (1 + 240 * q + 2160 * q ^ 2) ^ 3 - (1 - 504 * q - 16632 * q ^ 2) ^ 2
        - (1728 * q - 41472 * q ^ 2)
      = q ^ 3 * ((169344 : ℂ) + 110621376 * q + 3359232000 * q ^ 2 + 10077696000 * q ^ 3) := by
    ring
  have hP : ‖(169344 : ℂ) + 110621376 * q + 3359232000 * q ^ 2 + 10077696000 * q ^ 3‖
      ≤ 13547718720 := by
    have e1 : ‖(169344 : ℂ)‖ = 169344 := by norm_num
    have e2 : ‖(110621376 : ℂ) * q‖ = 110621376 * t := by
      rw [norm_mul, Complex.norm_ofNat, ht]
    have e3 : ‖(3359232000 : ℂ) * q ^ 2‖ = 3359232000 * t ^ 2 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ht]
    have e4 : ‖(10077696000 : ℂ) * q ^ 3‖ = 10077696000 * t ^ 3 := by
      rw [norm_mul, norm_pow, Complex.norm_ofNat, ht]
    calc ‖(169344 : ℂ) + 110621376 * q + 3359232000 * q ^ 2 + 10077696000 * q ^ 3‖
        ≤ ‖(169344 : ℂ) + 110621376 * q + 3359232000 * q ^ 2‖
            + ‖(10077696000 : ℂ) * q ^ 3‖ := norm_add_le _ _
      _ ≤ (‖(169344 : ℂ) + 110621376 * q‖ + ‖(3359232000 : ℂ) * q ^ 2‖)
            + ‖(10077696000 : ℂ) * q ^ 3‖ := add_le_add_left (norm_add_le _ _) _
      _ ≤ ((‖(169344 : ℂ)‖ + ‖(110621376 : ℂ) * q‖) + ‖(3359232000 : ℂ) * q ^ 2‖)
            + ‖(10077696000 : ℂ) * q ^ 3‖ :=
          add_le_add_left (add_le_add_left (norm_add_le _ _) _) _
      _ = (169344 + 110621376 * t + 3359232000 * t ^ 2) + 10077696000 * t ^ 3 := by
          rw [e1, e2, e3, e4]
      _ ≤ 13547718720 := by nlinarith [ht1, ht2, ht3, ht0]
  have hZW : ‖Z ^ 3 - W ^ 2 - (1728 * q - 41472 * q ^ 2)‖ ≤ 13547718720 * t ^ 3 := by
    rw [hZ, hW, hid, norm_mul, norm_pow]
    calc t ^ 3 * ‖(169344 : ℂ) + 110621376 * q + 3359232000 * q ^ 2 + 10077696000 * q ^ 3‖
        = ‖q‖ ^ 3 * ‖(169344 : ℂ) + 110621376 * q + 3359232000 * q ^ 2 + 10077696000 * q ^ 3‖ := by
          rw [ht]
      _ ≤ ‖q‖ ^ 3 * 13547718720 := mul_le_mul_of_nonneg_left hP (by positivity)
      _ = 13547718720 * t ^ 3 := by rw [ht]; ring
  -- error from replacing `z` by `Z` and `w` by `W`
  have hcubeZ : ‖z ^ 3 - Z ^ 3‖ ≤ A * t ^ 3 * (3 * (2401 + A) ^ 2) := by
    have h := norm_cube_sub_cube z Z
    have hb : ‖z‖ ^ 2 + ‖z‖ * ‖Z‖ + ‖Z‖ ^ 2 ≤ 3 * (2401 + A) ^ 2 := by
      have hz' : ‖z‖ ≤ 2401 + A := hznorm
      have hZ' : ‖Z‖ ≤ 2401 + A := le_trans hZnorm (by linarith)
      nlinarith [norm_nonneg z, norm_nonneg Z, hz', hZ']
    have hX0 : 0 ≤ ‖z‖ ^ 2 + ‖z‖ * ‖Z‖ + ‖Z‖ ^ 2 := by positivity
    calc ‖z ^ 3 - Z ^ 3‖ ≤ ‖z - Z‖ * (‖z‖ ^ 2 + ‖z‖ * ‖Z‖ + ‖Z‖ ^ 2) := h
      _ ≤ (A * t ^ 3) * (3 * (2401 + A) ^ 2) := by
          refine le_trans (mul_le_mul_of_nonneg_right hzt hX0) ?_
          exact mul_le_mul_of_nonneg_left hb hAt
  have hsqW : ‖w ^ 2 - W ^ 2‖ ≤ B * t ^ 3 * (2 * (17137 + B)) := by
    have h := norm_sq_sub_sq w W
    have hb : ‖w‖ + ‖W‖ ≤ 2 * (17137 + B) := by
      have hw' : ‖w‖ ≤ 17137 + B := hwnorm
      have hW' : ‖W‖ ≤ 17137 + B := le_trans hWnorm (by linarith)
      linarith
    calc ‖w ^ 2 - W ^ 2‖ ≤ ‖w - W‖ * (‖w‖ + ‖W‖) := h
      _ ≤ (B * t ^ 3) * (2 * (17137 + B)) := by
          refine mul_le_mul hwt hb (by positivity) hBt
  have hsplit : (z ^ 3 - w ^ 2) / 1728 - (q - 24 * q ^ 2)
      = (z ^ 3 - Z ^ 3) / 1728 - (w ^ 2 - W ^ 2) / 1728
        + (Z ^ 3 - W ^ 2 - (1728 * q - 41472 * q ^ 2)) / 1728 := by ring
  rw [hsplit]
  have h1 : ‖(z ^ 3 - Z ^ 3) / 1728‖ ≤ (A * t ^ 3 * (3 * (2401 + A) ^ 2)) / 1728 := by
    rw [norm_div, Complex.norm_ofNat]
    exact div_le_div_of_nonneg_right hcubeZ (by norm_num)
  have h2 : ‖(w ^ 2 - W ^ 2) / 1728‖ ≤ (B * t ^ 3 * (2 * (17137 + B))) / 1728 := by
    rw [norm_div, Complex.norm_ofNat]
    exact div_le_div_of_nonneg_right hsqW (by norm_num)
  have h3 : ‖(Z ^ 3 - W ^ 2 - (1728 * q - 41472 * q ^ 2)) / 1728‖
      ≤ (13547718720 / 1728) * t ^ 3 := by
    rw [norm_div, Complex.norm_ofNat]
    calc ‖Z ^ 3 - W ^ 2 - (1728 * q - 41472 * q ^ 2)‖ / 1728
        ≤ (13547718720 * t ^ 3) / 1728 := div_le_div_of_nonneg_right hZW (by norm_num)
      _ = (13547718720 / 1728) * t ^ 3 := by ring
  have hfin : ‖(z ^ 3 - Z ^ 3) / 1728 - (w ^ 2 - W ^ 2) / 1728
        + (Z ^ 3 - W ^ 2 - (1728 * q - 41472 * q ^ 2)) / 1728‖ ≤
      ((3 * A * (2401 + A) ^ 2 + 2 * B * (17137 + B) + 13547718720) / 1728) * t ^ 3 := by
    calc ‖(z ^ 3 - Z ^ 3) / 1728 - (w ^ 2 - W ^ 2) / 1728
          + (Z ^ 3 - W ^ 2 - (1728 * q - 41472 * q ^ 2)) / 1728‖
        ≤ ‖(z ^ 3 - Z ^ 3) / 1728 - (w ^ 2 - W ^ 2) / 1728‖
            + ‖(Z ^ 3 - W ^ 2 - (1728 * q - 41472 * q ^ 2)) / 1728‖ := norm_add_le _ _
      _ ≤ (‖(z ^ 3 - Z ^ 3) / 1728‖ + ‖(w ^ 2 - W ^ 2) / 1728‖)
            + ‖(Z ^ 3 - W ^ 2 - (1728 * q - 41472 * q ^ 2)) / 1728‖ :=
          add_le_add_left (norm_sub_le _ _) _
      _ ≤ ((A * t ^ 3 * (3 * (2401 + A) ^ 2)) / 1728 + (B * t ^ 3 * (2 * (17137 + B))) / 1728)
            + (13547718720 / 1728) * t ^ 3 := by linarith [h1, h2, h3]
      _ = ((3 * A * (2401 + A) ^ 2 + 2 * B * (17137 + B) + 13547718720) / 1728) * t ^ 3 := by
          ring
  simpa only [ht] using hfin

/-- `Δ - (q - 24q²) = O(‖q‖³)` on the cusp region, `q = e^{2πiτ} = E²`. -/
private theorem DeltaFunThirdOrder :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖Work.Kernels.DeltaFun τ - (Work.Kernels.qParamFun τ - 24 * Work.Kernels.qParamFun τ ^ 2)‖ ≤
        C * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  obtain ⟨A, hA, hE4⟩ := E4FunThirdOrder
  obtain ⟨B, hB, hE6⟩ := E6FunThirdOrder
  have hK : 0 < (3 * A * (2401 + A) ^ 2 + 2 * B * (17137 + B) + 13547718720) / 1728 := by
    have h1 : 0 ≤ 3 * A * (2401 + A) ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) hA.le) (sq_nonneg _)
    have h2 : 0 ≤ 2 * B * (17137 + B) := mul_nonneg (mul_nonneg (by norm_num) hB.le) (by linarith)
    exact div_pos (by linarith) (by norm_num)
  refine ⟨_, hK, fun τ hτ => ?_⟩
  have hρ1 : Real.exp (-(2 * Real.pi)) ≤ 1 :=
    le_of_lt (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos]))
  have hqE : Work.Kernels.qParamFun τ = Work.Residues.Ept τ ^ 2 := by
    rw [Work.Residues.Ept, Work.Kernels.qParamFun, sq, ← Complex.exp_add]
    congr 1; ring
  have hqnorm : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
    rw [hqE, norm_pow, Work.Residues.norm_Ept, sq, ← Real.exp_add]
    congr 1; ring
  have hqle : ‖Work.Kernels.qParamFun τ‖ ≤ Real.exp (-(2 * Real.pi)) := by
    rw [hqnorm, Real.exp_le_exp]
    nlinarith [Real.pi_pos, hτ]
  have hD : Work.Kernels.DeltaFun τ
      = (Work.Kernels.E4Fun τ ^ 3 - Work.Kernels.E6Fun τ ^ 2) / 1728 := by
    rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant,
      ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq]
  rw [hD]
  exact delta_third_algebra hA.le hB.le hρ1 hqle (hE4 τ hτ) (hE6 τ hτ)

/-! ## Inversion of the expansion -/

theorem cusp_invDelta : ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 ≤ z.im →
    ‖(Work.Kernels.DeltaFun z)⁻¹ - ((Work.Residues.Ept z)⁻¹ ^ 2 + 24)‖ ≤
      C * ‖Work.Residues.Ept z‖ ^ 2 := by
  obtain ⟨C3, hC3, hDelta⟩ := DeltaFunThirdOrder
  obtain ⟨c, hc, hlow⟩ := DeltaFun_lower_cusp_priv
  refine ⟨C3 + (24 + C3) ^ 2 / c, ?_, fun z hz => ?_⟩
  · have h1 : 0 ≤ (24 + C3) ^ 2 := sq_nonneg _
    have h2 : 0 < (24 + C3) ^ 2 / c := div_pos (by positivity) hc
    linarith
  · set q : ℂ := Work.Kernels.qParamFun z with hqdef
    set D : ℂ := Work.Kernels.DeltaFun z with hDdef
    have hqE : q = Work.Residues.Ept z ^ 2 := by
      rw [hqdef, Work.Residues.Ept, Work.Kernels.qParamFun, sq, ← Complex.exp_add]
      congr 1; ring
    have hq0 : q ≠ 0 := by rw [hqE]; exact pow_ne_zero 2 (Work.Residues.Ept_ne_zero z)
    have hqnorm : ‖q‖ = Real.exp (-(2 * Real.pi * z.im)) := by
      rw [hqE, norm_pow, Work.Residues.norm_Ept, sq, ← Real.exp_add]; congr 1; ring
    have hqpos : 0 < ‖q‖ := by rw [hqnorm]; exact Real.exp_pos _
    have hEptnorm : ‖q‖ = ‖Work.Residues.Ept z‖ ^ 2 := by rw [hqE, norm_pow]
    have hqle1 : ‖q‖ ≤ 1 := by
      rw [hqnorm]
      exact le_of_lt (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, hz]))
    have hDeltaq : ‖D - (q - 24 * q ^ 2)‖ ≤ C3 * ‖q‖ ^ 3 := by
      simpa only [hqdef, hDdef] using hDelta z hz
    have hlowq : c * ‖q‖ ≤ ‖D‖ := by
      have h := hlow z hz
      rw [← hqnorm] at h
      rwa [← hDdef] at h
    have hD0 : D ≠ 0 := by
      have hpos : 0 < c * ‖q‖ := mul_pos hc hqpos
      exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le hpos hlowq))
    -- the algebraic identity for the inversion
    have hkey : D⁻¹ - (q⁻¹ + 24)
        = q⁻¹ * (((D / q - 1) ^ 2 * (q * D⁻¹)) - ((D - q + 24 * q ^ 2) / q)) := by
      field_simp
      ring
    -- bound on the two error terms
    have hrho : ‖(D - q + 24 * q ^ 2) / q‖ ≤ C3 * ‖q‖ ^ 2 := by
      rw [norm_div, show D - q + 24 * q ^ 2 = D - (q - 24 * q ^ 2) by ring]
      calc ‖D - (q - 24 * q ^ 2)‖ / ‖q‖ ≤ (C3 * ‖q‖ ^ 3) / ‖q‖ :=
            div_le_div_of_nonneg_right hDeltaq (norm_nonneg _)
        _ = C3 * ‖q‖ ^ 2 := by
            rw [div_eq_iff (ne_of_gt hqpos)]; ring
    have hwD : ‖D / q - 1‖ ≤ (24 + C3) * ‖q‖ := by
      have hsplit : D / q - 1 = (D - q) / q := by
        rw [div_sub_one hq0]  -- (D - q)/q = D/q - 1
      rw [hsplit, norm_div]
      have hnum : ‖D - q‖ ≤ (24 + C3) * ‖q‖ ^ 2 := by
        have h1 : ‖D - q‖ ≤ ‖D - (q - 24 * q ^ 2)‖ + ‖(24 : ℂ) * q ^ 2‖ := by
          have h := norm_sub_le (D - (q - 24 * q ^ 2)) ((24 : ℂ) * q ^ 2)
          have he : D - (q - 24 * q ^ 2) - (24 : ℂ) * q ^ 2 = D - q := by ring
          rwa [he] at h
        have h2 : ‖(24 : ℂ) * q ^ 2‖ = 24 * ‖q‖ ^ 2 := by
          rw [norm_mul, norm_pow, Complex.norm_ofNat]
        have h3 : C3 * ‖q‖ ^ 3 ≤ C3 * ‖q‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg q) hqle1 (by norm_num)) hC3.le
        linarith
      calc ‖D - q‖ / ‖q‖ ≤ ((24 + C3) * ‖q‖ ^ 2) / ‖q‖ :=
            div_le_div_of_nonneg_right hnum (norm_nonneg _)
        _ = (24 + C3) * ‖q‖ := by rw [div_eq_iff (ne_of_gt hqpos)]; ring
    have hS : ‖q * D⁻¹‖ ≤ 1 / c := by
      rw [norm_mul, norm_inv]
      have hcpos : 0 < c * ‖q‖ := mul_pos hc hqpos
      have hDpos : 0 < ‖D‖ := lt_of_lt_of_le hcpos hlowq
      have hinv : ‖D‖⁻¹ ≤ (c * ‖q‖)⁻¹ := (inv_le_inv₀ hDpos hcpos).mpr hlowq
      calc ‖q‖ * ‖D‖⁻¹ ≤ ‖q‖ * (c * ‖q‖)⁻¹ := mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
        _ = 1 / c := by
            rw [mul_inv, ← mul_assoc, mul_comm ‖q‖ c⁻¹, mul_assoc,
              mul_inv_cancel₀ (ne_of_gt hqpos), mul_one, one_div]
    have h1 : ‖((D / q - 1) ^ 2 * (q * D⁻¹)) - ((D - q + 24 * q ^ 2) / q)‖
        ≤ (24 + C3) ^ 2 * ‖q‖ ^ 2 * (1 / c) + C3 * ‖q‖ ^ 2 := by
      have hsq : ‖(D / q - 1) ^ 2 * (q * D⁻¹)‖ ≤ (24 + C3) ^ 2 * ‖q‖ ^ 2 * (1 / c) := by
        rw [norm_mul, norm_pow]
        have hw2 : ‖D / q - 1‖ ^ 2 ≤ ((24 + C3) * ‖q‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hwD 2
        calc ‖D / q - 1‖ ^ 2 * ‖q * D⁻¹‖
            ≤ ((24 + C3) * ‖q‖) ^ 2 * (1 / c) := mul_le_mul hw2 hS (by positivity) (by positivity)
          _ = (24 + C3) ^ 2 * ‖q‖ ^ 2 * (1 / c) := by ring
      calc ‖((D / q - 1) ^ 2 * (q * D⁻¹)) - ((D - q + 24 * q ^ 2) / q)‖
          ≤ ‖(D / q - 1) ^ 2 * (q * D⁻¹)‖ + ‖(D - q + 24 * q ^ 2) / q‖ := norm_sub_le _ _
        _ ≤ (24 + C3) ^ 2 * ‖q‖ ^ 2 * (1 / c) + C3 * ‖q‖ ^ 2 := add_le_add hsq hrho
    have hmain : ‖D⁻¹ - (q⁻¹ + 24)‖ ≤ (C3 + (24 + C3) ^ 2 / c) * ‖q‖ := by
      rw [hkey, norm_mul]
      calc ‖q⁻¹‖ * ‖((D / q - 1) ^ 2 * (q * D⁻¹)) - ((D - q + 24 * q ^ 2) / q)‖
          ≤ ‖q⁻¹‖ * ((24 + C3) ^ 2 * ‖q‖ ^ 2 * (1 / c) + C3 * ‖q‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = (C3 + (24 + C3) ^ 2 / c) * ‖q‖ := by
            rw [norm_inv, ← div_eq_inv_mul, div_eq_iff (ne_of_gt hqpos)]
            ring
    have hEptinv : (Work.Residues.Ept z)⁻¹ ^ 2 = q⁻¹ := by rw [inv_pow, ← hqE]
    simpa only [hDdef, hEptinv, ← hEptnorm] using hmain

end

end Work.Asymptotics

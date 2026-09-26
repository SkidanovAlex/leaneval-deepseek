import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.All
import Submission.Work.Residues.QExpansionTail
import Submission.Work.Residues.E4FunSecondOrder
import Submission.Work.Residues.E6FunSecondOrder
import Submission.Work.Residues.DeltaExpansion
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Modular.E2_qExpansion_coeff

namespace Work.Asymptotics.MFix

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

noncomputable section

/-! ## Cusp expansions at `i∞`

The first-order (`O(q²)`) expansions of the three level-one Eisenstein series and of `Δ`,
together with a two-sided bound for `Δ/q`, where `q = exp (2 π i τ)`. -/

/-- `qParamFun τ = exp (2 π i τ)` agrees with `Function.Periodic.qParam 1`. -/
lemma qParamFun_eq_qParam (τ : ℍ) :
    Work.Kernels.qParamFun τ = Function.Periodic.qParam 1 (τ : ℂ) := by
  simp [Work.Kernels.qParamFun, Function.Periodic.qParam]

/-- `‖qParamFun τ‖ = exp (-2 π Im τ)`. -/
lemma norm_qParamFun (τ : ℍ) :
    ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) := by
  rw [qParamFun_eq_qParam, Function.Periodic.norm_qParam, div_one, UpperHalfPlane.coe_im]
  congr 1; ring

lemma qParamFun_ne_zero' (τ : ℍ) : Work.Kernels.qParamFun τ ≠ 0 := by
  rw [qParamFun_eq_qParam]; exact Function.Periodic.qParam_ne_zero _

/-- The `q`-expansion coefficient bound for `E₂` used for the second-order expansion. -/
private lemma E2_coeff_bound (m : ℕ) (hm : 2 ≤ m) :
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

/-- `E₂ = 1 - 24 q + O(q²)`. -/
theorem E2Fun_two_term :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ‖ ≤
        C * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
  have hper : Function.Periodic (Work.Kernels.E2Fun ∘ UpperHalfPlane.ofComplex) 1 :=
    Work.Modular.E2_periodic_one
  have hhol : MDiff Work.Kernels.E2Fun := E2_mdifferentiable
  have hbdd : IsBoundedAtImInfty Work.Kernels.E2Fun := EisensteinSeries.isBoundedAtImInfty_E2
  obtain ⟨C, hC, hb⟩ := Work.Residues.qExpansion_tail_bound 2 hper hhol hbdd 24 2 (by norm_num)
    E2_coeff_bound
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

/-- `E₄ = 1 + 240 q + O(q²)`. -/
theorem E4Fun_two_term :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ‖ ≤
        C * ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
  Work.Residues.E4FunSecondOrder

/-- `E₆ = 1 - 504 q + O(q²)`. -/
theorem E6Fun_two_term :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ‖ ≤
        C * ‖Work.Kernels.qParamFun τ‖ ^ 2 :=
  Work.Residues.E6FunSecondOrder

/-- `Δ = q + O(q²)`. -/
theorem DeltaFun_two_term :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ‖ ≤
        C * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := Work.Residues.DeltaExpansion
  have hE : ∀ τ : ℍ, Work.Residues.Ept τ ^ 2 = Work.Kernels.qParamFun τ := by
    intro τ
    rw [Work.Kernels.qParamFun, Work.Residues.Ept, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have h1 := h τ hτ
  rw [hE τ] at h1
  have h2 : ‖Work.Kernels.qParamFun τ‖ ^ 2 = ‖Work.Residues.Ept τ‖ ^ 4 := by
    rw [← hE τ, norm_pow]; ring
  simpa [h2] using h1

/-! ## Boundedness of the Eisenstein series near the cusp -/

lemma norm_qParamFun_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.qParamFun τ‖ ≤ Real.exp (-(2 * Real.pi)) := by
  rw [norm_qParamFun, Real.exp_le_exp]; nlinarith [Real.pi_pos, hτ]

/-- `E₂` is bounded on `{1 ≤ Im τ}`. -/
theorem E2Fun_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖Work.Kernels.E2Fun τ‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := E2Fun_two_term
  refine ⟨1 + 24 * Real.exp (-(2 * Real.pi)) + C * Real.exp (-(2 * Real.pi)) ^ 2,
    by positivity, fun τ hτ => ?_⟩
  have h1 := h τ hτ
  have h2 : ‖Work.Kernels.qParamFun τ‖ ≤ Real.exp (-(2 * Real.pi)) := norm_qParamFun_le τ hτ
  have h3 : ‖Work.Kernels.qParamFun τ‖ ^ 2 ≤ Real.exp (-(2 * Real.pi)) ^ 2 := by
    nlinarith [norm_nonneg (Work.Kernels.qParamFun τ), h2]
  have he : (0:ℝ) < Real.exp (-(2 * Real.pi)) := Real.exp_pos _
  have he1 : Real.exp (-(2 * Real.pi)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos]
  have h4 : ‖Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ‖
      ≤ C * Real.exp (-(2 * Real.pi)) ^ 2 := le_trans h1 (by nlinarith)
  have hsplit : Work.Kernels.E2Fun τ
      = (Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ)
        + 1 - 24 * Work.Kernels.qParamFun τ := by ring
  rw [hsplit]
  calc ‖(Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ) + 1
        - 24 * Work.Kernels.qParamFun τ‖
      ≤ ‖(Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ) + 1‖
        + ‖(24 : ℂ) * Work.Kernels.qParamFun τ‖ := norm_sub_le _ _
    _ ≤ (‖Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ‖ + 1)
        + 24 * ‖Work.Kernels.qParamFun τ‖ := by
        have h5 : ‖(Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ) + 1‖
            ≤ ‖Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ‖ + ‖(1:ℂ)‖ :=
          norm_add_le _ _
        rw [norm_one] at h5
        have h6 : ‖(24 : ℂ) * Work.Kernels.qParamFun τ‖
            = 24 * ‖Work.Kernels.qParamFun τ‖ := by
          rw [norm_mul]; norm_num
        rw [h6]; linarith
    _ ≤ 1 + 24 * Real.exp (-(2 * Real.pi)) + C * Real.exp (-(2 * Real.pi)) ^ 2 := by
        nlinarith [h4, h2, h3, norm_nonneg (Work.Kernels.qParamFun τ)]

/-- `E₄` is bounded on `{1 ≤ Im τ}`. -/
theorem E4Fun_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖Work.Kernels.E4Fun τ‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := E4Fun_two_term
  refine ⟨1 + 240 * Real.exp (-(2 * Real.pi)) + C * Real.exp (-(2 * Real.pi)) ^ 2,
    by positivity, fun τ hτ => ?_⟩
  have h1 := h τ hτ
  have h2 : ‖Work.Kernels.qParamFun τ‖ ≤ Real.exp (-(2 * Real.pi)) := norm_qParamFun_le τ hτ
  have he : (0:ℝ) < Real.exp (-(2 * Real.pi)) := Real.exp_pos _
  have h4 : ‖Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ‖
      ≤ C * Real.exp (-(2 * Real.pi)) ^ 2 := by
    refine le_trans h1 ?_
    have h3 : ‖Work.Kernels.qParamFun τ‖ ^ 2 ≤ Real.exp (-(2 * Real.pi)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith [hC.le]
  have hsplit : Work.Kernels.E4Fun τ
      = (Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ)
        + 1 + 240 * Work.Kernels.qParamFun τ := by ring
  rw [hsplit]
  have h6 : ‖(240 : ℂ) * Work.Kernels.qParamFun τ‖ = 240 * ‖Work.Kernels.qParamFun τ‖ := by
    rw [norm_mul]; norm_num
  calc ‖(Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ) + 1
        + 240 * Work.Kernels.qParamFun τ‖
      ≤ ‖(Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ) + 1‖
        + ‖(240 : ℂ) * Work.Kernels.qParamFun τ‖ := norm_add_le _ _
    _ ≤ (‖Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ‖ + 1)
        + 240 * ‖Work.Kernels.qParamFun τ‖ := by
        have h5 : ‖(Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ) + 1‖
            ≤ ‖Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ‖ + ‖(1:ℂ)‖ :=
          norm_add_le _ _
        rw [norm_one] at h5
        rw [h6]; linarith
    _ ≤ 1 + 240 * Real.exp (-(2 * Real.pi)) + C * Real.exp (-(2 * Real.pi)) ^ 2 := by
        nlinarith [h4, h2, he]

/-- `E₆` is bounded on `{1 ≤ Im τ}`. -/
theorem E6Fun_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖Work.Kernels.E6Fun τ‖ ≤ C := by
  obtain ⟨C, hC, h⟩ := E6Fun_two_term
  refine ⟨1 + 504 * Real.exp (-(2 * Real.pi)) + C * Real.exp (-(2 * Real.pi)) ^ 2,
    by positivity, fun τ hτ => ?_⟩
  have h1 := h τ hτ
  have h2 : ‖Work.Kernels.qParamFun τ‖ ≤ Real.exp (-(2 * Real.pi)) := norm_qParamFun_le τ hτ
  have he : (0:ℝ) < Real.exp (-(2 * Real.pi)) := Real.exp_pos _
  have h4 : ‖Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ‖
      ≤ C * Real.exp (-(2 * Real.pi)) ^ 2 := by
    refine le_trans h1 ?_
    have h3 : ‖Work.Kernels.qParamFun τ‖ ^ 2 ≤ Real.exp (-(2 * Real.pi)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    nlinarith [hC.le]
  have hsplit : Work.Kernels.E6Fun τ
      = (Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ)
        + 1 - 504 * Work.Kernels.qParamFun τ := by ring
  rw [hsplit]
  have h6 : ‖(504 : ℂ) * Work.Kernels.qParamFun τ‖ = 504 * ‖Work.Kernels.qParamFun τ‖ := by
    rw [norm_mul]; norm_num
  calc ‖(Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ) + 1
        - 504 * Work.Kernels.qParamFun τ‖
      ≤ ‖(Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ) + 1‖
        + ‖(504 : ℂ) * Work.Kernels.qParamFun τ‖ := norm_sub_le _ _
    _ ≤ (‖Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ‖ + 1)
        + 504 * ‖Work.Kernels.qParamFun τ‖ := by
        have h5 : ‖(Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ) + 1‖
            ≤ ‖Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ‖ + ‖(1:ℂ)‖ :=
          norm_add_le _ _
        rw [norm_one] at h5
        rw [h6]; linarith
    _ ≤ 1 + 504 * Real.exp (-(2 * Real.pi)) + C * Real.exp (-(2 * Real.pi)) ^ 2 := by
        nlinarith [h4, h2, he]

/-- `Δ = O(q)` on `{1 ≤ Im τ}`. -/
theorem DeltaFun_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      ‖Work.Kernels.DeltaFun τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ := by
  obtain ⟨C, hC, h⟩ := Work.Residues.DeltaFun_decay
  exact ⟨C, hC, fun τ hτ => by rw [norm_qParamFun]; exact h τ hτ⟩

/-! ## The lower bound `Δ ≳ q`

Mathlib's eta-product formula `Δ = q * ∏' n, (1 - eta_q n ·)^24` together with the elementary
estimate `‖∏' (1 - a_n)‖ ≥ ∏' (1 - ‖a_n‖) ≥ 1 - ∑ ‖a_n‖` gives `‖Δ τ‖ ≥ (1/2)^24 ‖q τ‖`
uniformly for `Im τ ≥ 1`. -/

/-- The `n`-th factor of the eta product: `‖eta_q n τ‖ = exp (-2 π (n+1) Im τ)`. -/
lemma norm_eta_q (n : ℕ) (τ : ℍ) :
    ‖ModularForm.eta_q n (τ : ℂ)‖ = Real.exp (-(2 * Real.pi * (n + 1) * τ.im)) := by
  rw [ModularForm.eta_q_eq_cexp, Complex.norm_exp]
  congr 1
  have h : (2 : ℂ) * ↑Real.pi * Complex.I * ((n : ℂ) + 1) * (τ : ℂ)
      = ((2 * Real.pi * (n + 1) : ℝ) : ℂ) * (Complex.I * (τ : ℂ)) := by
    push_cast; ring
  rw [h, Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
  ring

/-- `∏_{i ∈ s} (1 - f i) ≥ 1 - ∑_{i ∈ s} f i` for `0 ≤ f i ≤ 1`. -/
lemma one_sub_sum_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have h0a := h0 a (Finset.mem_insert_self a s)
      have h1a := h1 a (Finset.mem_insert_self a s)
      have h0s : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_insert_of_mem hi)
      have h1s : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (Finset.mem_insert_of_mem hi)
      have ih' := ih h0s h1s
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hsum : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg fun i hi => h0s i hi
      have hprod : 0 ≤ ∏ i ∈ s, (1 - f i) := Finset.prod_nonneg fun i hi => by linarith [h1s i hi]
      have hkey : (1 - f a) * (1 - ∑ i ∈ s, f i) ≤ (1 - f a) * ∏ i ∈ s, (1 - f i) :=
        mul_le_mul_of_nonneg_left ih' (by linarith)
      nlinarith [hkey, mul_nonneg h0a hsum, mul_nonneg h0a hprod]

/-- Products of nonnegative reals: monotonicity in each factor. -/
lemma prod_le_prod_of_nonneg {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ g i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact mul_le_mul (h1 a (Finset.mem_insert_self a s))
        (ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
            (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
            (fun i hi => hg i (Finset.mem_insert_of_mem hi)))
        (Finset.prod_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi))
        (hg a (Finset.mem_insert_self a s))

/-- `∑_n ‖eta_q n τ‖ ≤ 1/2` for `Im τ ≥ 1`. -/
lemma tsum_norm_eta_q_le (τ : ℍ) (hτ : 1 ≤ τ.im) :
    ∑' n : ℕ, ‖ModularForm.eta_q n (τ : ℂ)‖ ≤ 1 / 2 := by
  have hexp : Real.exp (-(2 * Real.pi)) ≤ 1 / 3 := by
    have h6 : (6:ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have h7 : (3:ℝ) ≤ Real.exp 6 := by
      have := Real.add_one_le_exp 6
      linarith
    have h8 : Real.exp 6 ≤ Real.exp (2 * Real.pi) := Real.exp_le_exp.mpr h6
    have h9 : (0:ℝ) < Real.exp (2 * Real.pi) := Real.exp_pos _
    rw [Real.exp_neg]
    set x := (Real.exp (2 * Real.pi))⁻¹ with hx
    have hx1 : x * Real.exp (2 * Real.pi) = 1 := by
      rw [hx, inv_mul_cancel₀ (ne_of_gt h9)]
    have hxpos : 0 < x := by rw [hx]; exact inv_pos.mpr h9
    have h10 : x * 3 ≤ x * Real.exp (2 * Real.pi) :=
      mul_le_mul_of_nonneg_left (le_trans h7 h8) hxpos.le
    rw [hx1] at h10
    linarith
  have hbound : ∀ n : ℕ, ‖ModularForm.eta_q n (τ : ℂ)‖ ≤ (1/3 : ℝ) ^ (n + 1) := by
    intro n
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hstep1 : ‖ModularForm.eta_q n (τ : ℂ)‖ ≤ Real.exp (-(2 * Real.pi * ((n:ℝ) + 1))) := by
      rw [norm_eta_q]
      rw [Real.exp_le_exp]
      have h0 : (0:ℝ) ≤ 2 * Real.pi * ((n:ℝ) + 1) := by positivity
      have h1 : 2 * Real.pi * ((n:ℝ) + 1) * 1 ≤ 2 * Real.pi * ((n:ℝ) + 1) * τ.im :=
        mul_le_mul_of_nonneg_left hτ h0
      linarith
    refine le_trans hstep1 ?_
    rw [show -(2 * Real.pi * ((n:ℝ) + 1)) = ((n + 1 : ℕ) : ℝ) * (-(2 * Real.pi)) by
      rw [hcast]; ring]
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hexp (n + 1)
  have hsumm : Summable (fun n : ℕ => (1/3 : ℝ) ^ (n + 1)) := by
    have h0 : (0:ℝ) ≤ 1/3 := by norm_num
    have h1 : (1/3 : ℝ) < 1 := by norm_num
    have h := (summable_geometric_of_lt_one h0 h1).mul_left (1/3 : ℝ)
    simpa [pow_succ, mul_comm] using h
  have hS : ∑' n : ℕ, (1/3 : ℝ) ^ (n + 1) = 1 / 2 := by
    have h0 : (0:ℝ) ≤ 1/3 := by norm_num
    have h1 : (1/3 : ℝ) < 1 := by norm_num
    have hsplit : (fun n : ℕ => (1/3 : ℝ) ^ (n + 1)) = fun n : ℕ => (1/3) * (1/3) ^ n := by
      funext n; rw [pow_succ, mul_comm]
    rw [hsplit, tsum_mul_left, tsum_geometric_of_lt_one h0 h1]
    norm_num
  have hsum : Summable (fun n : ℕ => ‖ModularForm.eta_q n (τ : ℂ)‖) := by
    simpa using ModularForm.summable_eta_q τ
  calc ∑' n : ℕ, ‖ModularForm.eta_q n (τ : ℂ)‖
      ≤ ∑' n : ℕ, (1/3 : ℝ) ^ (n + 1) := Summable.tsum_le_tsum hbound hsum hsumm
    _ = 1 / 2 := hS

/-- The eta product is bounded below by `(1/2)^24` on `Im τ ≥ 1`. -/
lemma tprod_eta_q_lower (τ : ℍ) (hτ : 1 ≤ τ.im) :
    (1/2 : ℝ) ^ 24 ≤ ‖∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) ^ 24‖ := by
  have hmult : Multipliable (fun n : ℕ => 1 - ModularForm.eta_q n (τ : ℂ)) :=
    ModularForm.multipliableLocallyUniformlyOn_eta.multipliable τ.2
  have hr0 : ∀ n : ℕ, (0:ℝ) ≤ ‖ModularForm.eta_q n (τ : ℂ)‖ := fun n => norm_nonneg _
  have hr1 : ∀ n : ℕ, ‖ModularForm.eta_q n (τ : ℂ)‖ ≤ 1 := by
    intro n
    rw [norm_eta_q, Real.exp_le_one_iff]
    have h0 : (0:ℝ) < 2 * Real.pi * ((n:ℝ) + 1) := by positivity
    have := mul_pos h0 τ.im_pos
    linarith
  have hsum : Summable (fun n : ℕ => ‖ModularForm.eta_q n (τ : ℂ)‖) := by
    simpa using ModularForm.summable_eta_q τ
  have hmul1 : Multipliable (fun n : ℕ => 1 - ‖ModularForm.eta_q n (τ : ℂ)‖) :=
    Real.multipliable_one_add_of_summable (f := fun n : ℕ => -‖ModularForm.eta_q n (τ : ℂ)‖)
      hsum.neg
  have hmul2 : Multipliable (fun n : ℕ => ‖1 - ModularForm.eta_q n (τ : ℂ)‖) := hmult.norm
  have hge : (1/2 : ℝ) ≤ ∏' n : ℕ, ‖1 - ModularForm.eta_q n (τ:ℂ)‖ := by
    refine le_hasProd_of_le_prod hmul2.hasProd (fun s => ?_)
    have hs : ∑ i ∈ s, ‖ModularForm.eta_q i (τ:ℂ)‖ ≤ ∑' n : ℕ, ‖ModularForm.eta_q n (τ:ℂ)‖ :=
      hsum.sum_le_tsum s (fun i _ => hr0 i)
    have h2 := one_sub_sum_le_prod s (fun n => ‖ModularForm.eta_q n (τ:ℂ)‖)
      (fun i _ => hr0 i) (fun i _ => hr1 i)
    have h3 : ∏ i ∈ s, (1 - ‖ModularForm.eta_q i (τ:ℂ)‖)
        ≤ ∏ i ∈ s, ‖1 - ModularForm.eta_q i (τ:ℂ)‖ :=
      prod_le_prod_of_nonneg s _ _ (fun i _ => by linarith [hr1 i])
        (fun i _ => by
          have h := norm_sub_norm_le (1:ℂ) (ModularForm.eta_q i (τ:ℂ))
          rw [norm_one] at h
          linarith)
        (fun i _ => norm_nonneg _)
    have h4 := tsum_norm_eta_q_le τ hτ
    linarith
  have hnormeq : ‖∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) ^ 24‖
      = (∏' n : ℕ, ‖1 - ModularForm.eta_q n (τ : ℂ)‖) ^ 24 := by
    rw [hmult.tprod_pow, norm_pow, hmult.norm_tprod]
  rw [hnormeq]
  exact pow_le_pow_left₀ (by norm_num) hge 24

/-- `‖Δ τ‖ ≥ (1/2)^24 ‖q τ‖` for `Im τ ≥ 1`. -/
theorem DeltaFun_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im →
      c * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖ := by
  refine ⟨(1/2 : ℝ) ^ 24, by positivity, fun τ hτ => ?_⟩
  have hΔ : Work.Kernels.DeltaFun τ = ModularForm.discriminant τ := by
    rw [show Work.Kernels.DeltaFun = ⇑CuspForm.discriminant from rfl, CuspForm.coe_discriminant]
  rw [hΔ, ModularForm.discriminant_eq_q_prod,
    show Function.Periodic.qParam 1 (τ : ℂ) = Work.Kernels.qParamFun τ
      from (qParamFun_eq_qParam τ).symm]
  have hP := tprod_eta_q_lower τ hτ
  calc (1/2 : ℝ) ^ 24 * ‖Work.Kernels.qParamFun τ‖
      ≤ ‖∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) ^ 24‖
          * ‖Work.Kernels.qParamFun τ‖ :=
        mul_le_mul_of_nonneg_right hP (norm_nonneg _)
    _ = ‖Work.Kernels.qParamFun τ
          * ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) ^ 24‖ := by
        rw [norm_mul]; ring

/-! ## A small `O(q^n)` toolkit at the cusp -/

/-- `IsBigOq f n` : `f = O(q^n)` near the cusp `i∞`, with `q = exp (2 π i τ)`. -/
def IsBigOq (f : ℍ → ℂ) (n : ℕ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖f τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ n

lemma norm_qParamFun_le_one (τ : ℍ) (hτ : 1 ≤ τ.im) : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := by
  rw [norm_qParamFun, Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hτ]

lemma IsBigOq.mono {f : ℍ → ℂ} {m n : ℕ} (h : IsBigOq f n) (hmn : m ≤ n) : IsBigOq f m := by
  obtain ⟨C, hC, hf⟩ := h
  refine ⟨C, hC, fun τ hτ => ?_⟩
  have hqn : ‖Work.Kernels.qParamFun τ‖ ^ n ≤ ‖Work.Kernels.qParamFun τ‖ ^ m :=
    pow_le_pow_of_le_one (norm_nonneg _) (norm_qParamFun_le_one τ hτ) hmn
  have h1 := hf τ hτ
  have h2 := pow_nonneg (norm_nonneg (Work.Kernels.qParamFun τ)) n
  have h3 := pow_nonneg (norm_nonneg (Work.Kernels.qParamFun τ)) m
  nlinarith [hC.le]

lemma IsBigOq.congr {f g : ℍ → ℂ} {n : ℕ} (h : IsBigOq f n) (hfg : ∀ τ, f τ = g τ) :
    IsBigOq g n := by
  obtain ⟨C, hC, hf⟩ := h
  exact ⟨C, hC, fun τ hτ => by rw [← hfg τ]; exact hf τ hτ⟩

lemma IsBigOq.bounded {f : ℍ → ℂ} (B : ℝ) (hB : 0 < B)
    (h : ∀ τ : ℍ, 1 ≤ τ.im → ‖f τ‖ ≤ B) : IsBigOq f 0 := by
  refine ⟨B, hB, fun τ hτ => ?_⟩
  simpa using h τ hτ

lemma IsBigOq.add {f g : ℍ → ℂ} {m n : ℕ} (hf : IsBigOq f m) (hg : IsBigOq g n) :
    IsBigOq (fun τ => f τ + g τ) (min m n) := by
  obtain ⟨C1, hC1, h1⟩ := IsBigOq.mono hf (min_le_left m n)
  obtain ⟨C2, hC2, h2⟩ := IsBigOq.mono hg (min_le_right m n)
  refine ⟨C1 + C2, by positivity, fun τ hτ => ?_⟩
  have hp := h1 τ hτ
  have hq := h2 τ hτ
  have h3 : ‖f τ + g τ‖ ≤ ‖f τ‖ + ‖g τ‖ := norm_add_le (f τ) (g τ)
  rw [add_mul]
  linarith

lemma IsBigOq.mul {f g : ℍ → ℂ} {m n : ℕ} (hf : IsBigOq f m) (hg : IsBigOq g n) :
    IsBigOq (fun τ => f τ * g τ) (m + n) := by
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  refine ⟨Cf * Cg, mul_pos hCf hCg, fun τ hτ => ?_⟩
  have h1 := hf τ hτ
  have h2 := hg τ hτ
  have hb : (0:ℝ) ≤ Cf * ‖Work.Kernels.qParamFun τ‖ ^ m :=
    mul_nonneg hCf.le (pow_nonneg (norm_nonneg _) m)
  have hc : (0:ℝ) ≤ ‖g τ‖ := norm_nonneg _
  have h4 : ‖f τ‖ * ‖g τ‖ ≤ (Cf * ‖Work.Kernels.qParamFun τ‖ ^ m)
      * (Cg * ‖Work.Kernels.qParamFun τ‖ ^ n) := mul_le_mul h1 h2 hc hb
  rw [norm_mul, pow_add]
  nlinarith [h4, mul_nonneg hCf.le (pow_nonneg (norm_nonneg (Work.Kernels.qParamFun τ)) m),
    mul_nonneg hCg.le (pow_nonneg (norm_nonneg (Work.Kernels.qParamFun τ)) n)]

lemma IsBigOq.const_mul (c : ℂ) {f : ℍ → ℂ} {n : ℕ} (hf : IsBigOq f n) :
    IsBigOq (fun τ => c * f τ) n := by
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨‖c‖ * C + 1, by positivity, fun τ hτ => ?_⟩
  rw [norm_mul]
  have h1 := hf τ hτ
  have h2 := mul_le_mul_of_nonneg_left h1 (norm_nonneg c)
  have h3 := pow_nonneg (norm_nonneg (Work.Kernels.qParamFun τ)) n
  nlinarith [h2]

lemma IsBigOq.neg {f : ℍ → ℂ} {n : ℕ} (hf : IsBigOq f n) : IsBigOq (fun τ => -f τ) n := by
  have h := IsBigOq.const_mul (-1 : ℂ) hf
  simpa using h

/-! ## The building blocks `O(q^n)` at the cusp -/

lemma qParamFun_isBigOq : IsBigOq Work.Kernels.qParamFun 1 :=
  ⟨1, one_pos, fun τ _ => by simp⟩

lemma qParamFun_sq_isBigOq : IsBigOq (fun τ => Work.Kernels.qParamFun τ ^ 2) 2 := by
  have h := qParamFun_isBigOq.mul qParamFun_isBigOq
  refine IsBigOq.congr h (fun τ => ?_)
  ring

lemma isBigOq_one_add_const_mul_q (c : ℂ) :
    IsBigOq (fun τ => 1 + c * Work.Kernels.qParamFun τ) 0 := by
  refine IsBigOq.bounded (f := fun τ => 1 + c * Work.Kernels.qParamFun τ) (1 + ‖c‖)
    (by positivity) (fun τ hτ => ?_)
  calc ‖1 + c * Work.Kernels.qParamFun τ‖ ≤ 1 + ‖c * Work.Kernels.qParamFun τ‖ := by
        simpa using norm_add_le (1:ℂ) (c * Work.Kernels.qParamFun τ)
    _ = 1 + ‖c‖ * ‖Work.Kernels.qParamFun τ‖ := by rw [norm_mul]
    _ ≤ 1 + ‖c‖ := by
        have := norm_qParamFun_le_one τ hτ
        nlinarith [norm_nonneg c]

lemma E2Fun_isBigOq :
    IsBigOq (fun τ => Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ) 2 := by
  obtain ⟨C, hC, h⟩ := E2Fun_two_term
  exact ⟨C, hC, fun τ hτ => h τ hτ⟩

lemma E4Fun_isBigOq :
    IsBigOq (fun τ => Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ) 2 := by
  obtain ⟨C, hC, h⟩ := E4Fun_two_term
  exact ⟨C, hC, fun τ hτ => h τ hτ⟩

lemma E6Fun_isBigOq :
    IsBigOq (fun τ => Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ) 2 := by
  obtain ⟨C, hC, h⟩ := E6Fun_two_term
  exact ⟨C, hC, fun τ hτ => h τ hτ⟩

lemma DeltaFun_isBigOq :
    IsBigOq (fun τ => Work.Kernels.DeltaFun τ - Work.Kernels.qParamFun τ) 2 := by
  obtain ⟨C, hC, h⟩ := DeltaFun_two_term
  exact ⟨C, hC, fun τ hτ => h τ hτ⟩

lemma DeltaFun_isBigOq_one : IsBigOq Work.Kernels.DeltaFun 1 := by
  obtain ⟨C, hC, h⟩ := DeltaFun_upper
  exact ⟨C, hC, fun τ hτ => by rw [pow_one]; exact h τ hτ⟩

lemma E2Fun_bdd : IsBigOq Work.Kernels.E2Fun 0 := by
  obtain ⟨C, hC, h⟩ := E2Fun_bound
  exact ⟨C, hC, fun τ hτ => by simpa using h τ hτ⟩

lemma E4Fun_bdd : IsBigOq Work.Kernels.E4Fun 0 := by
  obtain ⟨C, hC, h⟩ := E4Fun_bound
  exact ⟨C, hC, fun τ hτ => by simpa using h τ hτ⟩

lemma E6Fun_bdd : IsBigOq Work.Kernels.E6Fun 0 := by
  obtain ⟨C, hC, h⟩ := E6Fun_bound
  exact ⟨C, hC, fun τ hτ => by simpa using h τ hτ⟩

lemma E2_minus_one : IsBigOq (fun τ => Work.Kernels.E2Fun τ - 1) 1 := by
  have h := E2Fun_isBigOq.add (qParamFun_isBigOq.const_mul (-24))
  refine (IsBigOq.mono h (le_refl 1)).congr (fun τ => ?_)
  ring

lemma E4_minus_one : IsBigOq (fun τ => Work.Kernels.E4Fun τ - 1) 1 := by
  have h := E4Fun_isBigOq.add (qParamFun_isBigOq.const_mul (240))
  refine (IsBigOq.mono h (le_refl 1)).congr (fun τ => ?_)
  ring

lemma E6_minus_one : IsBigOq (fun τ => Work.Kernels.E6Fun τ - 1) 1 := by
  have h := E6Fun_isBigOq.add (qParamFun_isBigOq.const_mul (-504))
  refine (IsBigOq.mono h (le_refl 1)).congr (fun τ => ?_)
  ring

/-- `E₂² = 1 - 48 q + O(q²)`. -/
lemma E2sq_two_term :
    IsBigOq (fun τ => Work.Kernels.E2Fun τ ^ 2 - 1 + 48 * Work.Kernels.qParamFun τ) 2 := by
  have hρ : IsBigOq (fun τ => Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ) 2 :=
    E2Fun_isBigOq
  have hb : IsBigOq (fun τ => (Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ)
      - 48 * Work.Kernels.qParamFun τ + 2) 0 := by
    have h1 := (E2Fun_isBigOq.add (qParamFun_isBigOq.const_mul (-48))).add
      (IsBigOq.bounded (f := fun _ : ℍ => (2 : ℂ)) 2 (by norm_num) (fun _ _ => by simp))
    refine h1.congr (fun τ => ?_)
    ring
  have hprod : IsBigOq (fun τ => (Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ)
      * ((Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ)
        - 48 * Work.Kernels.qParamFun τ + 2)) 2 := hρ.mul hb
  have hsq : IsBigOq (fun τ => 576 * Work.Kernels.qParamFun τ ^ 2) 2 :=
    qParamFun_sq_isBigOq.const_mul (576 : ℂ)
  refine (hsq.add hprod).congr (fun τ => ?_)
  ring

lemma E2sq_minus_one : IsBigOq (fun τ => Work.Kernels.E2Fun τ ^ 2 - 1) 1 := by
  have h := E2sq_two_term.add (qParamFun_isBigOq.const_mul (-48))
  refine (IsBigOq.mono h (le_refl 1)).congr (fun τ => ?_)
  ring

/-- `E₄ - E₂² = 288 q + O(q²)`. -/
lemma delta1_two_term :
    IsBigOq (fun τ => Work.Kernels.E4Fun τ - Work.Kernels.E2Fun τ ^ 2
      - 288 * Work.Kernels.qParamFun τ) 2 := by
  refine (E4Fun_isBigOq.add E2sq_two_term.neg).congr (fun τ => ?_)
  ring

lemma delta1_isBigOq : IsBigOq (fun τ => Work.Kernels.E4Fun τ - Work.Kernels.E2Fun τ ^ 2) 1 := by
  have h := delta1_two_term.add (qParamFun_isBigOq.const_mul (288))
  refine (IsBigOq.mono h (le_refl 1)).congr (fun τ => ?_)
  ring

/-- `E₄² - E₆E₂ = 1008 q + O(q²)`. -/
lemma eps_two_term :
    IsBigOq (fun τ => Work.Kernels.E4Fun τ ^ 2
      - Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ
      - 1008 * Work.Kernels.qParamFun τ) 2 := by
  have hA := E4Fun_isBigOq
  have hB := E6Fun_isBigOq
  have hC := E2Fun_isBigOq
  have h1 : IsBigOq (fun τ => 2 * (1 + 240 * Work.Kernels.qParamFun τ)
      * (Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ)) 2 :=
    ((isBigOq_one_add_const_mul_q (240)).const_mul (2:ℂ)).mul hA
  have h2 : IsBigOq (fun τ => (1 + (-504 : ℂ) * Work.Kernels.qParamFun τ)
      * (Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ)) 2 :=
    (isBigOq_one_add_const_mul_q (-504)).mul hC
  have h3 : IsBigOq (fun τ => (1 + (-24 : ℂ) * Work.Kernels.qParamFun τ)
      * (Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ)) 2 :=
    (isBigOq_one_add_const_mul_q (-24)).mul hB
  have h4 : IsBigOq (fun τ => (Work.Kernels.E4Fun τ - 1 - 240 * Work.Kernels.qParamFun τ) ^ 2) 2 := by
    refine ((hA.mul hA).mono (by norm_num : 2 ≤ 2 + 2)).congr (fun τ => ?_)
    ring
  have h5 : IsBigOq (fun τ => (Work.Kernels.E6Fun τ - 1 + 504 * Work.Kernels.qParamFun τ)
      * (Work.Kernels.E2Fun τ - 1 + 24 * Work.Kernels.qParamFun τ)) 2 :=
    (hB.mul hC).mono (by norm_num : 2 ≤ 2 + 2)
  have h6 : IsBigOq (fun τ => 45504 * Work.Kernels.qParamFun τ ^ 2) 2 :=
    qParamFun_sq_isBigOq.const_mul (45504 : ℂ)
  refine (h6.add ((h1.add (h2.neg)).add h3.neg)).add (h4.add h5.neg) |>.congr (fun τ => ?_)
  ring

lemma eps_isBigOq :
    IsBigOq (fun τ => Work.Kernels.E4Fun τ ^ 2 - Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ) 1 := by
  have h := eps_two_term.add (qParamFun_isBigOq.const_mul (1008))
  refine (IsBigOq.mono h (le_refl 1)).congr (fun τ => ?_)
  ring

/-! ## The explicit numerators `Ξ_8`, `Ξ_24`

`Ξ_d(τ,z) = c_d · Δ(z) · (j(τ) - j(z)) · z^{d/2-2} · K_+^{(d)}(τ, S·z)` is a sum of products of
bounded quantities and of `O(q)` quantities; it is the object bounded in the main theorem. -/

/-- The numerator for `d = 8`. -/
def Xi8 (τ z : ℍ) : ℂ :=
  ∑ i : Fin 3, ∑ m : Fin 3,
    Work.Kernels.phiVec τ i * Work.Kernels.fk ((![6, 4, 2] : Fin 3 → ℤ) i) τ *
      (!![Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z, 0, 1;
          -2 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z), -2, 0;
          1, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ) i m *
      Work.Kernels.fk ((![12, 10, 8] : Fin 3 → ℤ) m) z * Work.Kernels.E2Fun z ^ (m : ℕ)

/-- The numerator for `d = 24`. -/
def Xi24 (τ z : ℍ) : ℂ :=
  ∑ i : Fin 3, ∑ m : Fin 3,
    Work.Kernels.phiVec τ i * Work.Kernels.fk ((![14, 12, 10] : Fin 3 → ℤ) i) τ *
      (!![6 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z), 0,
          Work.Kernels.c1728 - 6 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z);
          -12 * Work.Kernels.jInvariantFun τ * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
            + 5 * Work.Kernels.c1728 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z),
            -2 * Work.Kernels.c1728,
            12 * Work.Kernels.jInvariantFun τ * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
              - 7 * Work.Kernels.c1728 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z);
          Work.Kernels.c1728 + 6 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z), 0,
            -6 * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)] :
        Matrix (Fin 3) (Fin 3) ℂ) i m *
      Work.Kernels.fk ((![4, 2, 0] : Fin 3 → ℤ) m) z * Work.Kernels.E2Fun z ^ (m : ℕ)

private lemma PiMat_mul_apply_entry (a b : Fin 3 → ℤ) (M : Matrix (Fin 3) (Fin 3) ℂ)
    (x y : ℍ) (i m : Fin 3) :
    (Work.Kernels.PiMat a x * M * Work.Kernels.PiMat b y) i m
      = Work.Kernels.fk (a i) x * M i m * Work.Kernels.fk (b m) y := by
  simp only [Work.Kernels.PiMat]
  rw [Matrix.mul_assoc, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

/-- `phitVec (S·z) m · z² = z ^ (2m) · E₂(z) ^ m`. -/
lemma phitVec_S_smul (z : ℍ) (m : Fin 3) :
    Work.Kernels.phitVec (ModularGroup.S • z) m * (z : ℂ) ^ 2
      = (z : ℂ) ^ (2 * (m : ℕ)) * Work.Kernels.E2Fun z ^ (m : ℕ) := by
  have hz : (z : ℂ) ≠ 0 := Work.Kernels.KernelFacts.kpc_tau_ne_zero z
  have hsq : (-(z : ℂ)⁻¹) ^ 2 * (z : ℂ) ^ 2 = 1 := by
    rw [pow_two, neg_mul_neg]
    field_simp
  have key : ∀ (n : ℕ) (w : ℂ), (-(z : ℂ)⁻¹) ^ 2 * ((z : ℂ) ^ 2 * w) ^ n * (z : ℂ) ^ 2
      = (z : ℂ) ^ (2 * n) * w ^ n := by
    intro n w
    rw [mul_pow, ← pow_mul]
    have h1 : (-(z : ℂ)⁻¹) ^ 2 * ((z : ℂ) ^ (2 * n) * w ^ n) * (z : ℂ) ^ 2
        = ((-(z : ℂ)⁻¹) ^ 2 * (z : ℂ) ^ 2) * ((z : ℂ) ^ (2 * n) * w ^ n) := by ring
    rw [h1, hsq, one_mul]
  fin_cases m
  · simp only [Work.Kernels.phitVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.val_two]
    rw [Work.Kernels.S_smul_coe]
    simpa [hsq, Nat.mul_zero, pow_zero, mul_one, one_mul] using hsq
  · simp only [Work.Kernels.phitVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.val_two]
    rw [Work.Kernels.S_smul_coe, Work.Kernels.TildeFacts.E2S_S_smul]
    simpa using key 1 (Work.Kernels.E2Fun z)
  · simp only [Work.Kernels.phitVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.val_zero, Fin.val_one, Fin.val_two]
    rw [Work.Kernels.S_smul_coe, Work.Kernels.TildeFacts.E2S_S_smul]
    simpa using key 2 (Work.Kernels.E2Fun z)

lemma E4sq_bdd : IsBigOq (fun τ => Work.Kernels.E4Fun τ ^ 2) 0 :=
  (E4Fun_bdd.mul E4Fun_bdd).congr (fun τ => by ring)

lemma E4cube_bdd : IsBigOq (fun τ => Work.Kernels.E4Fun τ ^ 3) 0 :=
  (E4sq_bdd.mul E4Fun_bdd).congr (fun τ => by ring)

lemma E4sq_minus_one : IsBigOq (fun τ => Work.Kernels.E4Fun τ ^ 2 - 1) 1 := by
  have hb : IsBigOq (fun τ => Work.Kernels.E4Fun τ + 1) 0 :=
    E4Fun_bdd.add (IsBigOq.bounded (f := fun _ : ℍ => (1 : ℂ)) 1 (by norm_num) (fun _ _ => by simp))
  refine (E4_minus_one.mul hb).congr (fun τ => ?_)
  ring

lemma E4cube_minus_one : IsBigOq (fun τ => Work.Kernels.E4Fun τ ^ 3 - 1) 1 := by
  have hb : IsBigOq (fun τ => Work.Kernels.E4Fun τ ^ 2 + Work.Kernels.E4Fun τ + 1) 0 :=
    (E4sq_bdd.add E4Fun_bdd).add
      (IsBigOq.bounded (f := fun _ : ℍ => (1 : ℂ)) 1 (by norm_num) (fun _ _ => by simp))
  refine (E4_minus_one.mul hb).congr (fun τ => ?_)
  ring

/-- `E₄³(E₄ - E₂²) = 288 Δ + O(q²)`. -/
lemma E4cube_delta1_minus_Delta :
    IsBigOq (fun τ => Work.Kernels.E4Fun τ ^ 3
      * (Work.Kernels.E4Fun τ - Work.Kernels.E2Fun τ ^ 2) - 288 * Work.Kernels.DeltaFun τ) 2 := by
  have h1 : IsBigOq (fun τ => Work.Kernels.E4Fun τ ^ 3
      * (Work.Kernels.E4Fun τ - Work.Kernels.E2Fun τ ^ 2 - 288 * Work.Kernels.qParamFun τ)) 2 :=
    E4cube_bdd.mul delta1_two_term
  have h2 : IsBigOq (fun τ => (Work.Kernels.E4Fun τ ^ 3 - 1)
      * (288 * Work.Kernels.qParamFun τ)) 2 :=
    E4cube_minus_one.mul (qParamFun_isBigOq.const_mul (288))
  have h3 : IsBigOq (fun τ => (288 : ℂ) * (Work.Kernels.qParamFun τ - Work.Kernels.DeltaFun τ)) 2 :=
    (DeltaFun_isBigOq.neg.const_mul (288)).congr (fun τ => by ring)
  refine ((h1.add h2).add h3).congr (fun τ => ?_)
  ring

/-- `E₄²(E₄² - E₆E₂) = 1008 Δ + O(q²)`. -/
lemma E4sq_eps_minus_Delta :
    IsBigOq (fun τ => Work.Kernels.E4Fun τ ^ 2
      * (Work.Kernels.E4Fun τ ^ 2 - Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ)
      - 1008 * Work.Kernels.DeltaFun τ) 2 := by
  have h1 : IsBigOq (fun τ => Work.Kernels.E4Fun τ ^ 2
      * (Work.Kernels.E4Fun τ ^ 2 - Work.Kernels.E6Fun τ * Work.Kernels.E2Fun τ
        - 1008 * Work.Kernels.qParamFun τ)) 2 :=
    E4sq_bdd.mul eps_two_term
  have h2 : IsBigOq (fun τ => (Work.Kernels.E4Fun τ ^ 2 - 1)
      * (1008 * Work.Kernels.qParamFun τ)) 2 :=
    E4sq_minus_one.mul (qParamFun_isBigOq.const_mul (1008))
  have h3 : IsBigOq (fun τ => (1008 : ℂ) * (Work.Kernels.qParamFun τ - Work.Kernels.DeltaFun τ)) 2 :=
    (DeltaFun_isBigOq.neg.const_mul (1008)).congr (fun τ => by ring)
  refine ((h1.add h2).add h3).congr (fun τ => ?_)
  ring

/-- `E₄³(E₄ - E₂²) = 288 E₂² Δ + O(q²)`. -/
lemma E4cube_delta1_minus_E2sqDelta :
    IsBigOq (fun τ => Work.Kernels.E4Fun τ ^ 3
      * (Work.Kernels.E4Fun τ - Work.Kernels.E2Fun τ ^ 2)
      - 288 * Work.Kernels.E2Fun τ ^ 2 * Work.Kernels.DeltaFun τ) 2 := by
  have h1 : IsBigOq (fun τ => Work.Kernels.E4Fun τ ^ 3
      * (Work.Kernels.E4Fun τ - Work.Kernels.E2Fun τ ^ 2 - 288 * Work.Kernels.qParamFun τ)) 2 :=
    E4cube_bdd.mul delta1_two_term
  have h2 : IsBigOq (fun τ => (Work.Kernels.E4Fun τ ^ 3 - 1)
      * (288 * Work.Kernels.qParamFun τ)) 2 :=
    E4cube_minus_one.mul (qParamFun_isBigOq.const_mul (288))
  have h3 : IsBigOq (fun τ => (288 : ℂ) * (Work.Kernels.qParamFun τ - Work.Kernels.DeltaFun τ)) 2 :=
    (DeltaFun_isBigOq.neg.const_mul (288)).congr (fun τ => by ring)
  have h4 : IsBigOq (fun τ => (288 : ℂ) * (Work.Kernels.DeltaFun τ
      * (1 - Work.Kernels.E2Fun τ ^ 2))) 2 :=
    ((DeltaFun_isBigOq_one.mul E2sq_minus_one.neg).const_mul (288)).congr (fun τ => by ring)
  refine ((h1.add (h2.add (h3.add h4)))).congr (fun τ => ?_)
  ring

/-! ## Bounds on the closed ball -/

lemma exists_bound_on_closedBall {f : ℍ → ℂ} (hf : Continuous f) (τ₀ : ℍ) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, dist τ τ₀ ≤ R → ‖f τ‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall τ₀ R).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max C 0 + 1, by positivity, fun τ hτ => le_trans (hC τ hτ)
    (by linarith [le_max_left C (0:ℝ)])⟩

lemma continuous_jInvariantFun : Continuous Work.Kernels.jInvariantFun :=
  (((ModularForm.holo' ModularForm.E₄).continuous.pow 3).div
    (CuspForm.holo' CuspForm.discriminant).continuous
    (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ))

/-- Uniform bounds for all the `τ`-dependent factors of `Xi8` and `Xi24` on a closed ball. -/
lemma ball_factor_bounds (τ₀ : ℍ) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, dist τ τ₀ ≤ R →
      ‖Work.Kernels.jInvariantFun τ‖ ≤ C ∧
      ‖Work.Kernels.phiVec τ 0‖ ≤ C ∧ ‖Work.Kernels.phiVec τ 1‖ ≤ C ∧
      ‖Work.Kernels.phiVec τ 2‖ ≤ C ∧
      ‖Work.Kernels.fk 2 τ‖ ≤ C ∧ ‖Work.Kernels.fk 4 τ‖ ≤ C ∧
      ‖Work.Kernels.fk 6 τ‖ ≤ C ∧ ‖Work.Kernels.fk 10 τ‖ ≤ C ∧
      ‖Work.Kernels.fk 12 τ‖ ≤ C ∧ ‖Work.Kernels.fk 14 τ‖ ≤ C := by
  obtain ⟨c1, hc1, hb1⟩ := exists_bound_on_closedBall continuous_jInvariantFun τ₀ R
  have hE2c : Continuous Work.Kernels.E2Fun := E2_mdifferentiable.continuous
  have hcoe : Continuous (fun τ : ℍ => (τ : ℂ)) := UpperHalfPlane.continuous_coe
  have hphi0 : Continuous Work.Kernels.phiNeg2 := by
    rw [show Work.Kernels.phiNeg2 = fun τ : ℍ => (τ : ℂ) from rfl]; exact hcoe
  have hphi1 : Continuous Work.Kernels.phi0 := by
    rw [show Work.Kernels.phi0 = fun τ : ℍ =>
      (τ : ℂ) * Work.Kernels.E2Fun τ - 3 * Complex.I / (Real.pi : ℂ) from rfl]
    exact (hcoe.mul hE2c).sub continuous_const
  have hphi2 : Continuous Work.Kernels.phi2 := by
    rw [show Work.Kernels.phi2 = fun τ : ℍ =>
      (τ : ℂ) * Work.Kernels.E2Fun τ ^ 2
        - (6 * Complex.I / (Real.pi : ℂ)) * Work.Kernels.E2Fun τ from rfl]
    exact (hcoe.mul (hE2c.pow 2)).sub (hE2c.const_mul _)
  have hE4c : Continuous Work.Kernels.E4Fun := (ModularForm.holo' ModularForm.E₄).continuous
  have hE6c : Continuous Work.Kernels.E6Fun := (ModularForm.holo' ModularForm.E₆).continuous
  have hE14c : Continuous Work.Kernels.E14Fun := (hE4c.pow 2).mul hE6c
  have hDc : Continuous Work.Kernels.DeltaFun := (CuspForm.holo' CuspForm.discriminant).continuous
  obtain ⟨c3, hc3, hb3⟩ := exists_bound_on_closedBall hphi0 τ₀ R
  obtain ⟨c4, hc4, hb4⟩ := exists_bound_on_closedBall hphi1 τ₀ R
  obtain ⟨c5, hc5, hb5⟩ := exists_bound_on_closedBall hphi2 τ₀ R
  obtain ⟨c6, hc6, hb6⟩ := exists_bound_on_closedBall
    (hE14c.div hDc (fun τ => Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)) τ₀ R
  obtain ⟨c7, hc7, hb7⟩ := exists_bound_on_closedBall hE4c τ₀ R
  obtain ⟨c8, hc8, hb8⟩ := exists_bound_on_closedBall hE6c τ₀ R
  obtain ⟨c9, hc9, hb9⟩ := exists_bound_on_closedBall (hE4c.mul hE6c) τ₀ R
  obtain ⟨c10, hc10, hb10⟩ := exists_bound_on_closedBall hDc τ₀ R
  obtain ⟨c11, hc11, hb11⟩ := exists_bound_on_closedBall hE14c τ₀ R
  refine ⟨c1 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + 1, by positivity, fun τ hτ => ?_⟩
  have hMpos : (0:ℝ) < c1 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + 1 := by positivity
  have h1' : c1 ≤ c1 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + 1 := by linarith [hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11]
  have h3' : c3 ≤ c1 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + 1 := by linarith [hc1, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11]
  have h4' : c4 ≤ c1 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + 1 := by linarith [hc1, hc3, hc5, hc6, hc7, hc8, hc9, hc10, hc11]
  have h5' : c5 ≤ c1 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + 1 := by linarith [hc1, hc3, hc4, hc6, hc7, hc8, hc9, hc10, hc11]
  have h6' : c6 ≤ c1 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + 1 := by linarith [hc1, hc3, hc4, hc5, hc7, hc8, hc9, hc10, hc11]
  have h7' : c7 ≤ c1 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + 1 := by linarith [hc1, hc3, hc4, hc5, hc6, hc8, hc9, hc10, hc11]
  have h8' : c8 ≤ c1 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + 1 := by linarith [hc1, hc3, hc4, hc5, hc6, hc7, hc9, hc10, hc11]
  have h9' : c9 ≤ c1 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + 1 := by linarith [hc1, hc3, hc4, hc5, hc6, hc7, hc8, hc10, hc11]
  have h10' : c10 ≤ c1 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + 1 := by linarith [hc1, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc11]
  have h11' : c11 ≤ c1 + c3 + c4 + c5 + c6 + c7 + c8 + c9 + c10 + c11 + 1 := by linarith [hc1, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10]
  exact ⟨le_trans (hb1 τ hτ) h1',
    le_trans (by simpa [Work.Kernels.phiVec, Work.Kernels.phiNeg2] using hb3 τ hτ) h3',
    le_trans (by simpa [Work.Kernels.phiVec, Work.Kernels.phi0] using hb4 τ hτ) h4',
    le_trans (by simpa [Work.Kernels.phiVec, Work.Kernels.phi2] using hb5 τ hτ) h5',
    le_trans (by simpa [Work.Kernels.fk] using hb6 τ hτ) h6',
    le_trans (by simpa [Work.Kernels.fk] using hb7 τ hτ) h7',
    le_trans (by simpa [Work.Kernels.fk] using hb8 τ hτ) h8',
    le_trans (by simpa [Work.Kernels.fk] using hb9 τ hτ) h9',
    le_trans (by simpa [Work.Kernels.fk] using hb10 τ hτ) h10',
    le_trans (by simpa [Work.Kernels.fk] using hb11 τ hτ) h11'⟩

end

end Work.Asymptotics.MFix

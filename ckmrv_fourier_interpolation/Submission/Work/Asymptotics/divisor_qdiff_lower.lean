/-
# The CKMRV divisor dominates the `q`-difference

CKMRV control the contour kernel by the *divisor* `Δ(τ)Δ(z)(j(τ) - j(z))`.  For the tail
expansions one needs the converse comparison: the divisor is at least a fixed multiple of the
`q`-difference

  `c ‖q(τ) - q(z)‖ ≤ ‖Δ(τ)Δ(z)(j τ - j z)‖`   (`Work.Kernels.qParamFun τ = e^{2πiτ}`),

uniformly for `Im τ ≥ T₀` and `Im z ≥ 1/3` (with `T₀ ≥ 1/3`).

## Why the hypothesis `T₀ ≤ Im τ` is needed

`j` is `SL(2,ℤ)`-invariant, so for `z = S τ = -1/τ` one has `j z = j τ` while `q z ≠ q τ`
whenever `τ` is such that both heights are at least `1/3`: taking `τ = 2i` and `z = i/2` gives
`q τ = e^{-4π} ≠ e^{-π} = q z`.  Hence *some* restriction on `τ` is required.  For `T₀ > 3` the
only `SL(2,ℤ)`-translates of `τ` of height `≥ 1/3` are the integer translates `τ + k`, for which
both sides vanish, so the statement is not vacuous.

## The proof, and the two ingredients that are *formalised elsewhere*

Write `ε = j - q⁻¹ - 744`, so that `ε = O(q)` at the cusp (`j = q⁻¹ + 744 + O(q)`).  Then

  `j τ - j z = (ε τ - ε z) + (q τ⁻¹ - q z⁻¹)
             = (ε τ - ε z) + (q z - q τ)/(q τ q z)`,

and `‖q τ⁻¹ - q z⁻¹‖ = ‖q τ - q z‖/(‖q τ‖ ‖q z‖)`.

* **`Work.Asymptotics.cuspFunction_diff_lipschitz`** (proved in
  `Submission/Work/Asymptotics/cuspFunction_diff_lipschitz.lean`): a holomorphic, `1`-periodic
  function bounded at the cusp has values that are Lipschitz in the `q`-variable on the disc
  `‖q‖ ≤ 1/2`.  Applied to `ε` this gives `‖ε τ - ε z‖ ≤ C‖q τ - q z‖`.
* **`Work.Asymptotics.delta_lower_third`** (proved in
  `Submission/Work/Asymptotics/KPlusFunnel/ZFacts.lean`): `‖Δ(w)‖ ≥ c_Δ‖q(w)‖` for
  `Im w ≥ 1/3`, from the product formula `Δ = q ∏(1 - q^{n+1})^{24}`.

Choosing `T₀ = max 2 (log (2C)/(2π))` gives `‖q τ‖ ≤ 1/(2C)` and `‖q z‖ ≤ 1/3`, so
`C ‖q τ‖ ‖q z‖ ≤ 1/2` and

  `‖j τ - j z‖ ≥ ‖q τ - q z‖/(‖q τ‖‖q z‖) - C‖q τ - q z‖
             = ‖q τ - q z‖ (1 - C‖q τ‖‖q z‖)/(‖q τ‖‖q z‖)
             ≥ ‖q τ - q z‖/(2‖q τ‖‖q z‖)`,

whence
`‖Δ τ Δ z (j τ - j z)‖ ≥ c_Δ²‖q τ‖‖q z‖ · ‖q τ - q z‖/(2‖q τ‖‖q z‖) = (c_Δ²/2)‖q τ - q z‖`.
-/
import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts
import Submission.Work.Asymptotics.jInvariantFun_cusp_second
import Submission.Work.Asymptotics.cuspFunction_diff_lipschitz

open scoped Manifold

noncomputable section

namespace Work.Asymptotics

open UpperHalfPlane

/-- The remainder `ε = j - q⁻¹ - 744` of the cusp expansion `j = q⁻¹ + 744 + O(q)`, where
`q = qParamFun` is the `q`-parameter. -/
private abbrev epsF (τ : UpperHalfPlane) : ℂ :=
  Work.Kernels.jInvariantFun τ - (Work.Kernels.qParamFun τ)⁻¹ - 744

/-- The `q`-parameter is invariant under `τ ↦ τ + 1`. -/
private lemma qParamFun_vadd_one (τ : UpperHalfPlane) :
    Work.Kernels.qParamFun ((1 : ℝ) +ᵥ τ) = Work.Kernels.qParamFun τ := by
  simp only [Work.Kernels.qParamFun]
  rw [show (((1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) = 1 + (τ : ℂ) by
    rw [UpperHalfPlane.coe_vadd]; push_cast; ring]
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 + (τ : ℂ))
      = (1 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I)
        + 2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

/-- `ε` is invariant under `τ ↦ τ + 1`. -/
private lemma epsF_vadd_one (τ : UpperHalfPlane) : epsF ((1 : ℝ) +ᵥ τ) = epsF τ := by
  simp only [epsF, qParamFun_vadd_one, Work.Kernels.KernelFacts.jInvariantFun_vadd_one]

/-- `ε` is holomorphic, being `j` minus the holomorphic function `q⁻¹` minus a constant. -/
private lemma epsF_differentiableOn :
    DifferentiableOn ℂ (epsF ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} := by
  have hDne : ∀ w : UpperHalfPlane, Work.Kernels.DeltaFun w ≠ 0 := fun w => by
    simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero w
  have hj : MDiff Work.Kernels.jInvariantFun :=
    ((ModularFormClass.holo ModularForm.E₄).pow 3).div
      (CuspFormClass.holo CuspForm.discriminant) hDne
  have hq : MDiff (fun w : UpperHalfPlane => (Work.Kernels.qParamFun w)⁻¹) := by
    have h1 : MDiff Work.Kernels.qParamFun := by
      rw [UpperHalfPlane.mdifferentiable_iff]
      have hg : DifferentiableOn ℂ
          (fun z : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)) {z : ℂ | 0 < z.im} :=
        (by fun_prop : Differentiable ℂ
          (fun z : ℂ => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z))).differentiableOn
      refine hg.congr (fun z hz => ?_)
      simp only [Function.comp_apply, Work.Kernels.qParamFun]
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    exact h1.inv fun w => Complex.exp_ne_zero _
  have hF : MDiff (fun w : UpperHalfPlane =>
      Work.Kernels.jInvariantFun w - (Work.Kernels.qParamFun w)⁻¹ - 744) :=
    (hj.sub hq).sub mdifferentiable_const
  exact (UpperHalfPlane.mdifferentiable_iff).mp hF

/-- `ε = j - q⁻¹ - 744` is bounded at the cusp `i∞`, since `ε = O(q)`. -/
private lemma epsF_bounded : UpperHalfPlane.IsBoundedAtImInfty epsF := by
  obtain ⟨T, M, _hT, hM, hbd⟩ := jInvariantFun_cusp_second
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  refine ⟨M, T, fun z hz => ?_⟩
  have hq : Work.Kernels.qParamFun z = Work.Residues.Ept z ^ 2 := by
    rw [Work.Kernels.qParamFun, Work.Residues.Ept, sq, ← Complex.exp_add]; congr 1; ring
  have h1 : epsF z = Work.Kernels.jInvariantFun z - ((Work.Residues.Ept z)⁻¹) ^ 2 - 744 := by
    simp only [epsF, hq, inv_pow]
  rw [h1]
  have h2 := hbd z hz
  have hE : ‖Work.Residues.Ept z‖ ≤ 1 := le_of_lt (Work.Residues.norm_Ept_lt_one z)
  calc ‖Work.Kernels.jInvariantFun z - ((Work.Residues.Ept z)⁻¹) ^ 2 - 744‖
      ≤ M * ‖Work.Residues.Ept z‖ ^ 2 := h2
    _ ≤ M * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hM.le
        nlinarith [hE, norm_nonneg (Work.Residues.Ept z)]
    _ = M := by ring

/-- **The divisor dominates the `q`-difference**, given the Lipschitz constant `C` for `ε` in the
`q`-variable on the disc `‖q‖ ≤ 1/2`. -/
private lemma divisor_qdiff_lower_of_lipschitz (C : ℝ) (hC : 0 < C)
    (hlip : ∀ τ z : UpperHalfPlane, ‖Work.Kernels.qParamFun τ‖ ≤ 1 / 2 →
      ‖Work.Kernels.qParamFun z‖ ≤ 1 / 2 →
      ‖epsF τ - epsF z‖ ≤ C * ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖) :
    ∃ c T₀ : ℝ, 0 < c ∧ 1 / 3 ≤ T₀ ∧ ∀ τ z : UpperHalfPlane, T₀ ≤ τ.im → 1 / 3 ≤ z.im →
      c * ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖
        ≤ ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  obtain ⟨cΔ, hcΔ, hΔ⟩ := delta_lower_third
  set T₀ : ℝ := max 2 (Real.log (2 * C) / (2 * Real.pi)) with hT₀
  have h2T : (2 : ℝ) ≤ T₀ := by rw [hT₀]; exact le_max_left _ _
  have hlogT : Real.log (2 * C) ≤ 2 * Real.pi * T₀ := by
    have h1 : Real.log (2 * C) / (2 * Real.pi) ≤ T₀ := by rw [hT₀]; exact le_max_right _ _
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
    have h3 : 2 * Real.pi * (Real.log (2 * C) / (2 * Real.pi)) = Real.log (2 * C) := by
      field_simp
    linarith [h2, h3]
  refine ⟨cΔ ^ 2 / 2, T₀, by positivity, le_trans (by norm_num) h2T, ?_⟩
  intro τ z hτ hz
  have hτ13 : 1 / 3 ≤ τ.im := le_trans (by norm_num : (1 : ℝ) / 3 ≤ 2) (le_trans h2T hτ)
  -- the two `q`-values are small
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hqτ_inv : ‖Work.Kernels.qParamFun τ‖ ≤ 1 / (2 * C) := by
    rw [norm_qParamFun]
    rw [show (1 : ℝ) / (2 * C) = Real.exp (-(Real.log (2 * C))) by
      rw [Real.exp_neg, Real.exp_log (by positivity), inv_eq_one_div]]
    exact Real.exp_le_exp.mpr (by nlinarith [hlogT, hτ, Real.pi_pos])
  have hqτ_half : ‖Work.Kernels.qParamFun τ‖ ≤ 1 / 2 := by
    rw [norm_qParamFun]
    calc Real.exp (-(2 * Real.pi * τ.im)) ≤ Real.exp (-(4 * Real.pi)) :=
          Real.exp_le_exp.mpr (by nlinarith [h2T, hτ, Real.pi_pos])
      _ ≤ 1 / 2 := by
          rw [show (1 : ℝ) / 2 = Real.exp (-(Real.log 2)) by
            rw [Real.exp_neg, Real.exp_log (by norm_num), inv_eq_one_div]]
          exact Real.exp_le_exp.mpr (by linarith [hlog2, Real.pi_gt_three])
  have hqz_half : ‖Work.Kernels.qParamFun z‖ ≤ 1 / 2 :=
    le_trans (norm_qParam_le_third hz) (by norm_num)
  have hqz_ne : Work.Kernels.qParamFun z ≠ 0 := Complex.exp_ne_zero _
  have hqτ_ne : Work.Kernels.qParamFun τ ≠ 0 := Complex.exp_ne_zero _
  -- the decomposition `j τ - j z = ε τ - ε z + (qτ⁻¹ - qz⁻¹)`
  have hdecomp : (epsF τ - epsF z)
      + ((Work.Kernels.qParamFun τ)⁻¹ - (Work.Kernels.qParamFun z)⁻¹)
      = Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z := by
    simp only [epsF]; ring
  have hqnorm : ‖(Work.Kernels.qParamFun τ)⁻¹ - (Work.Kernels.qParamFun z)⁻¹‖
      = ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖
        / (‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖) := by
    rw [show (Work.Kernels.qParamFun τ)⁻¹ - (Work.Kernels.qParamFun z)⁻¹
        = ((Work.Kernels.qParamFun z) - (Work.Kernels.qParamFun τ))
            / (Work.Kernels.qParamFun τ * Work.Kernels.qParamFun z) from by
      field_simp]
    rw [norm_div, norm_mul, norm_sub_rev]
  have hlip' := hlip τ z hqτ_half hqz_half
  have hden_pos : 0 < ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖ :=
    mul_pos (norm_pos_iff.mpr hqτ_ne) (norm_pos_iff.mpr hqz_ne)
  have htri : ‖(Work.Kernels.qParamFun τ)⁻¹ - (Work.Kernels.qParamFun z)⁻¹‖
      - ‖epsF τ - epsF z‖ ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := by
    have h1 := norm_sub_le
      ((Work.Kernels.qParamFun τ)⁻¹ - (Work.Kernels.qParamFun z)⁻¹ + (epsF τ - epsF z))
      (epsF τ - epsF z)
    rw [add_sub_cancel_right] at h1
    have h2 : (Work.Kernels.qParamFun τ)⁻¹ - (Work.Kernels.qParamFun z)⁻¹
        + (epsF τ - epsF z) = Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z := by
      rw [← hdecomp]; ring
    rw [h2] at h1
    linarith
  have hsmall : C * (‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖) ≤ 1 / 2 := by
    have h1 : C * ‖Work.Kernels.qParamFun τ‖ ≤ C * (1 / (2 * C)) :=
      mul_le_mul_of_nonneg_left hqτ_inv hC.le
    have h2 : C * (1 / (2 * C)) = 1 / 2 := by field_simp
    rw [h2] at h1
    have h3 : C * ‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖
        ≤ (1 / 2) * (1 / 2) := mul_le_mul h1 hqz_half (norm_nonneg _) (by norm_num)
    nlinarith [h3]
  -- the key norm bound
  have hkey : (1 / 2) * ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖
      ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖
        * (‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖) := by
    have h1 : ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖
          / (‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖)
        - C * ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖
        ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := by
      rw [hqnorm] at htri
      linarith [htri, hlip']
    have h2 := mul_le_mul_of_nonneg_right h1 hden_pos.le
    have h3 : (‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖
          / (‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖)
        - C * ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖)
        * (‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖)
        = ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖
          * (1 - C * (‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖)) := by
      field_simp
    rw [h3] at h2
    have h4 : ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖ * (1 / 2)
        ≤ ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖
          * (1 - C * (‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖)) :=
      mul_le_mul_of_nonneg_left (by linarith [hsmall]) (norm_nonneg _)
    linarith [h2, h4]
  -- assemble
  have hA : cΔ * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖ := hΔ τ hτ13
  have hB : cΔ * ‖Work.Kernels.qParamFun z‖ ≤ ‖Work.Kernels.DeltaFun z‖ := hΔ z hz
  have hprod : cΔ ^ 2 * (‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖)
      ≤ ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.DeltaFun z‖ := by
    have h1 : cΔ ^ 2 * (‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖)
        = (cΔ * ‖Work.Kernels.qParamFun τ‖) * (cΔ * ‖Work.Kernels.qParamFun z‖) := by ring
    rw [h1]
    exact mul_le_mul hA hB (by positivity) (norm_nonneg _)
  have step1 : cΔ ^ 2 * ((1 / 2) * ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖)
      ≤ cΔ ^ 2 * (‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖
          * (‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖)) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  have step2 : cΔ ^ 2 * (‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖
        * (‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖))
      = (cΔ ^ 2 * (‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖))
        * ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := by ring
  have step3 : (cΔ ^ 2 * (‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖))
        * ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖
      ≤ (‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.DeltaFun z‖)
        * ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ :=
    mul_le_mul_of_nonneg_right hprod (norm_nonneg _)
  calc cΔ ^ 2 / 2 * ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖
      = cΔ ^ 2 * ((1 / 2) * ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖) := by ring
    _ ≤ cΔ ^ 2 * (‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖
          * (‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖)) := step1
    _ = (cΔ ^ 2 * (‖Work.Kernels.qParamFun τ‖ * ‖Work.Kernels.qParamFun z‖))
        * ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := step2
    _ ≤ (‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.DeltaFun z‖)
        * ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := step3
    _ = ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
        rw [norm_mul, norm_mul]

theorem divisor_qdiff_lower :
    ∃ c T₀ : ℝ, 0 < c ∧ 1 / 3 ≤ T₀ ∧ ∀ τ z : UpperHalfPlane, T₀ ≤ τ.im → 1 / 3 ≤ z.im →
      c * ‖Work.Kernels.qParamFun τ - Work.Kernels.qParamFun z‖
        ≤ ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  obtain ⟨C, hC, hlip⟩ :=
    cuspFunction_diff_lipschitz epsF_vadd_one epsF_differentiableOn epsF_bounded
  exact divisor_qdiff_lower_of_lipschitz C hC hlip

end Work.Asymptotics

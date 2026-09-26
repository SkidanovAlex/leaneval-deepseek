import Mathlib
import Submission.Work.Asymptotics.HalfFunnel.lowBadDefs
import Submission.Work.Asymptotics.BlLow.Defs
import Submission.Work.Asymptotics.BlLow.ClearTS
import Submission.Work.Asymptotics.arcT_jprime_dense
import Submission.Work.Asymptotics.Graze.Vanishing

set_option maxHeartbeats 400000

noncomputable section

open UpperHalfPlane ModularGroup

namespace Work.Asymptotics.BlLow

open Work.Kernels
open Work.Asymptotics.HalfFunnel (tsign)
/-! ## 0. The two grazing branches and the tangency margin -/

/-- `blR τ = 1 - |Re τ|`, the distance of `Re τ` to the bad lines `Re τ = ±1`. -/
def blR (τ : ℍ) : ℝ := 1 - |τ.re|

/-- The tangency margin `blMargin τ = (Im τ)² - |Re τ| (1 - |Re τ|)`.  It vanishes exactly on
the two tangency arcs `{|τ ∓ 1/2| = 1/2}` and is positive in `𝒟`. -/
def blMargin (τ : ℍ) : ℝ := τ.im ^ 2 - |τ.re| * (1 - |τ.re|)

lemma blMargin_eq (τ : ℍ) : blMargin τ = ‖(τ : ℂ)‖ ^ 2 - |τ.re| := by
  have h : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im]
    ring
  rw [blMargin, h]
  have h2 : |τ.re| * (1 - |τ.re|) = |τ.re| - |τ.re| ^ 2 := by ring
  rw [h2, sq_abs]
  ring

/-- The grazing branch of `τ`: `blW τ = tsign τ + S • τ` (i.e. `1 - 1/τ` for `Re τ > 0` and
`-1 - 1/τ` for `Re τ < 0`). -/
def blW (τ : ℍ) : ℍ := tsign τ +ᵥ (ModularGroup.S • τ)

/-- The `S`-conjugate of the grazing branch: the second grazing branch. -/
def blV (τ : ℍ) : ℍ := ModularGroup.S • blW τ

lemma blW_coe (τ : ℍ) : ((blW τ : ℍ) : ℂ) = (tsign τ : ℂ) + (-(τ : ℂ))⁻¹ := by
  rw [blW, UpperHalfPlane.coe_vadd, UpperHalfPlane.modular_S_smul]

lemma blW_re (τ : ℍ) : (blW τ).re = tsign τ - τ.re / ‖(τ : ℂ)‖ ^ 2 := by
  rw [← UpperHalfPlane.coe_re, blW_coe, Complex.add_re, Complex.inv_re, Complex.normSq_neg,
    Complex.normSq_eq_norm_sq, Complex.neg_re, UpperHalfPlane.coe_re, Complex.ofReal_re]
  ring

lemma blW_im (τ : ℍ) : (blW τ).im = τ.im / ‖(τ : ℂ)‖ ^ 2 := by
  rw [← UpperHalfPlane.coe_im, blW_coe, Complex.add_im, Complex.ofReal_im, Complex.inv_im,
    Complex.normSq_neg, Complex.normSq_eq_norm_sq, Complex.neg_im, UpperHalfPlane.coe_im]
  ring

lemma tsign_eq_one_or_neg_one (τ : ℍ) : tsign τ = 1 ∨ tsign τ = -1 := by
  unfold tsign; split <;> simp

lemma blW_re_abs (τ : ℍ) : |(blW τ).re| = |blMargin τ| / ‖(τ : ℂ)‖ ^ 2 := by
  have hpos : 0 < ‖(τ : ℂ)‖ ^ 2 := pow_pos (norm_pos_iff.mpr τ.ne_zero) 2
  have hSm : ‖(τ : ℂ)‖ ^ 2 ≠ 0 := ne_of_gt hpos
  rcases lt_or_ge 0 τ.re with h | h
  · have h1 : tsign τ = 1 := by unfold tsign; rw [if_pos h]
    have hnum : (1 : ℝ) - τ.re / ‖(τ : ℂ)‖ ^ 2
        = (‖(τ : ℂ)‖ ^ 2 - τ.re) / ‖(τ : ℂ)‖ ^ 2 := by
      rw [sub_div, div_self hSm]
    rw [blW_re, h1, hnum, abs_div, abs_of_pos hpos, blMargin_eq, abs_of_nonneg h.le]
  · have h1 : tsign τ = -1 := by unfold tsign; rw [if_neg (not_lt.mpr h)]
    have hnum : (-1 : ℝ) - τ.re / ‖(τ : ℂ)‖ ^ 2
        = -((‖(τ : ℂ)‖ ^ 2 + τ.re) / ‖(τ : ℂ)‖ ^ 2) := by
      rw [add_div, div_self hSm]
      ring
    rw [blW_re, h1, hnum, abs_neg, abs_div, abs_of_pos hpos, blMargin_eq, abs_of_nonpos h]
    ring_nf

lemma blV_coe (τ : ℍ) : ((blV τ : ℍ) : ℂ) = (-(blW τ : ℂ))⁻¹ := by
  rw [blV, UpperHalfPlane.modular_S_smul]

lemma blV_re (τ : ℍ) : (blV τ).re = -(blW τ).re / ‖(blW τ : ℂ)‖ ^ 2 := by
  rw [← UpperHalfPlane.coe_re, blV_coe, Complex.inv_re, Complex.normSq_neg,
    Complex.normSq_eq_norm_sq, Complex.neg_re, UpperHalfPlane.coe_re]

lemma blV_im (τ : ℍ) : (blV τ).im = (blW τ).im / ‖(blW τ : ℂ)‖ ^ 2 := by
  rw [← UpperHalfPlane.coe_im, blV_coe, Complex.inv_im, Complex.normSq_neg,
    Complex.normSq_eq_norm_sq, Complex.neg_im, UpperHalfPlane.coe_im]
  ring

lemma blV_re_abs (τ : ℍ) :
    |(blV τ).re| = |blMargin τ| / (‖(τ : ℂ)‖ ^ 2 * ‖(blW τ : ℂ)‖ ^ 2) := by
  have hpos : 0 < ‖(blW τ : ℂ)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (blW τ).ne_zero) 2
  rw [blV_re, abs_div, abs_neg, abs_of_pos hpos, blW_re_abs, div_div]

lemma blW_norm_sq (τ : ℍ) : ‖(blW τ : ℂ)‖ ^ 2 = (blW τ).re ^ 2 + (blW τ).im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, UpperHalfPlane.coe_re,
    UpperHalfPlane.coe_im]
  ring

/-! ## 1. Elementary facts about `blLowSet` -/

lemma blLowSet_normSq_bounds {τ : ℍ} (hτ : blLowSet τ) :
    289 / 400 < ‖(τ : ℂ)‖ ^ 2 ∧ ‖(τ : ℂ)‖ ^ 2 ≤ 5 / 4 := by
  obtain ⟨h1, h2⟩ := blLowSet_re_abs_bounds hτ
  obtain ⟨h3, h4⟩ := blLowSet_im_bounds hτ
  have hsq : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im]
    ring
  have hre1sq : ((3 : ℝ) / 4) ^ 2 < τ.re ^ 2 := by
    have h : ((3 : ℝ) / 4) ^ 2 < |τ.re| ^ 2 := by nlinarith [h1, abs_nonneg τ.re]
    rwa [sq_abs] at h
  have hhim1 : ((2 : ℝ) / 5) ^ 2 ≤ τ.im ^ 2 := by nlinarith [h3, h4, τ.im_pos]
  have hre2sq : τ.re ^ 2 < 1 := by
    have h : |τ.re| ^ 2 < 1 := by nlinarith [h2, abs_nonneg τ.re]
    rwa [sq_abs] at h
  have hhim2 : τ.im ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 := by nlinarith [h3, h4, τ.im_pos]
  constructor
  · rw [hsq]; nlinarith [hre1sq, hhim1]
  · rw [hsq]; nlinarith [hre2sq, hhim2]

lemma blLowSet_blR_bounds {τ : ℍ} (hτ : blLowSet τ) :
    0 < blR τ ∧ blR τ < 1 / 4 := by
  obtain ⟨h1, h2⟩ := blLowSet_re_abs_bounds hτ
  constructor <;> simp only [blR] <;> linarith

lemma blLowSet_margin_pos {τ : ℍ} (hτ : blLowSet τ) : 0 < blMargin τ := by
  obtain ⟨hD, -, -, -⟩ := hτ
  rw [blMargin_eq]
  have hsq : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, UpperHalfPlane.coe_re,
      UpperHalfPlane.coe_im]
    ring
  rw [hsq]
  rcases lt_or_ge 0 τ.re with h | h
  · have h2 : ((1 : ℝ) / 2) ^ 2 < ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 := by
      have := hD.2.2.1
      nlinarith [norm_nonneg ((τ : ℂ) - (1 / 2 : ℂ))]
    have h3 : ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (τ.re - 1 / 2) ^ 2 + τ.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    rw [h3] at h2
    rw [abs_of_nonneg h.le]
    nlinarith [h2]
  · have h2 : ((1 : ℝ) / 2) ^ 2 < ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 := by
      have := hD.2.2.2
      nlinarith [norm_nonneg ((τ : ℂ) + (1 / 2 : ℂ))]
    have h3 : ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (τ.re + 1 / 2) ^ 2 + τ.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
      ring
    rw [h3] at h2
    rw [abs_of_nonpos h]
    nlinarith [h2]

/-! ## 2. The two branches are `j`-invariant -/

lemma jInvariantFun_vadd_neg_one (τ : ℍ) :
    jInvariantFun ((-1 : ℝ) +ᵥ τ) = jInvariantFun τ := by
  have h1 := Work.Kernels.KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ τ)
  rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ by rw [← vadd_assoc]; norm_num] at h1
  exact h1.symm

lemma jInvariantFun_vadd_tsign (τ w : ℍ) :
    jInvariantFun (tsign τ +ᵥ w) = jInvariantFun w := by
  rcases tsign_eq_one_or_neg_one τ with h | h
  · rw [h]; exact Work.Kernels.KernelFacts.jInvariantFun_vadd_one w
  · rw [h]; exact jInvariantFun_vadd_neg_one w

lemma blW_jInvariantFun (τ : ℍ) :
    jInvariantFun (blW τ) = jInvariantFun τ := by
  rw [blW, jInvariantFun_vadd_tsign, Work.Kernels.KernelFacts.jInvariantFun_S_smul]

lemma blV_jInvariantFun (τ : ℍ) :
    jInvariantFun (blV τ) = jInvariantFun τ := by
  rw [blV, Work.Kernels.KernelFacts.jInvariantFun_S_smul, blW_jInvariantFun]

lemma T_inv_smul_eq (z : ℍ) : ModularGroup.T⁻¹ • z = (-1 : ℝ) +ᵥ z := by
  have h1 := UpperHalfPlane.modular_T_smul ((-1 : ℝ) +ᵥ z)
  rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ z) = z by rw [← vadd_assoc]; norm_num] at h1
  calc ModularGroup.T⁻¹ • z = ModularGroup.T⁻¹ • (ModularGroup.T • ((-1 : ℝ) +ᵥ z)) := by
        rw [h1]
    _ = (ModularGroup.T⁻¹ * ModularGroup.T) • ((-1 : ℝ) +ᵥ z) := by rw [mul_smul]
    _ = (-1 : ℝ) +ᵥ z := by rw [inv_mul_cancel, one_smul]

lemma blW_eq_smul {τ : ℍ} (h : 0 < τ.re) :
    blW τ = (ModularGroup.T * ModularGroup.S) • τ := by
  rw [blW, show tsign τ = 1 from by unfold tsign; rw [if_pos h], mul_smul,
    UpperHalfPlane.modular_T_smul]

lemma blW_eq_smul' {τ : ℍ} (h : τ.re ≤ 0) :
    blW τ = (ModularGroup.T⁻¹ * ModularGroup.S) • τ := by
  have hstep : ModularGroup.T⁻¹ • (ModularGroup.S • τ) = (-1 : ℝ) +ᵥ (ModularGroup.S • τ) :=
    T_inv_smul_eq (ModularGroup.S • τ)
  rw [blW, show tsign τ = -1 from by unfold tsign; rw [if_neg (not_lt.mpr h)], ← hstep,
    mul_smul]

lemma blV_eq_smul {τ : ℍ} (h : 0 < τ.re) :
    blV τ = (ModularGroup.S * (ModularGroup.T * ModularGroup.S)) • τ := by
  rw [blV, blW_eq_smul h, ← mul_smul]

lemma blV_eq_smul' {τ : ℍ} (h : τ.re ≤ 0) :
    blV τ = (ModularGroup.S * (ModularGroup.T⁻¹ * ModularGroup.S)) • τ := by
  rw [blV, blW_eq_smul' h, ← mul_smul]

/-! ## 3. The grazing vanishings -/

private lemma S_mul_S : ModularGroup.S * ModularGroup.S = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]

private lemma ST_mul_TinvS : (ModularGroup.S * ModularGroup.T) *
    (ModularGroup.T⁻¹ * ModularGroup.S) = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]

private lemma TST_mul_STS : (ModularGroup.T * ModularGroup.S * ModularGroup.T) *
    (ModularGroup.S * (ModularGroup.T * ModularGroup.S)) = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]

private lemma TSTinv_mul_STinvS : (ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹ *
    (ModularGroup.S * (ModularGroup.T⁻¹ * ModularGroup.S)) = -1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [ModularGroup.coe_S, ModularGroup.coe_T, ModularGroup.coe_T_inv,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The non-vanishing locus of `j'` is dense, so a continuous function which vanishes at every
point of the orbit of a grazing element vanishes identically. -/
private lemma continuous_graze_AfunFun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    Continuous fun w : ℍ => Work.Asymptotics.AfunFun ℓ d (γ • w) w := by
  have hsmul : Continuous fun w : ℍ => γ • w := by
    simpa only [ModularGroup.sl_moeb] using continuous_const_smul (γ : GL (Fin 2) ℝ)
  have hpair : Continuous fun w : ℍ => (γ • w, w) := hsmul.prodMk continuous_id
  have hg : Continuous (fun p : ℍ × ℍ => Work.Asymptotics.AfunFun ℓ d p.1 p.2) :=
    Work.Asymptotics.continuous_AfunFun ℓ d
  have hcomp := Continuous.comp hg hpair
  exact hcomp

theorem KfunClear_graze_eq_zero (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hγ : Work.Asymptotics.Graze.GrazeElem γ) :
    ∀ z : ℍ, Work.Kernels.KfunClear ℓ d (γ • z) z = 0 := by
  have hcont : Continuous fun w : ℍ => AfunFun ℓ d (γ • w) w :=
    continuous_graze_AfunFun ℓ d γ
  have hclosed : IsClosed {w : ℍ | AfunFun ℓ d (γ • w) w = 0} :=
    isClosed_eq hcont continuous_const
  have hsub : {w : ℍ | Work.Residues.jprime w ≠ 0} ⊆ {w : ℍ | AfunFun ℓ d (γ • w) w = 0} := by
    intro w hw
    have h := Work.Asymptotics.Graze.KfunClear_vanish_graze ℓ d hd γ hγ w hw
    rw [Work.Asymptotics.KfunClear_eq_mul_AfunFun] at h
    rcases mul_eq_zero.mp h with h2 | h2
    · exact absurd h2 (mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)
        (pow_ne_zero _ (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero _)))
    · exact h2
  have hdense : Dense {w : ℍ | Work.Residues.jprime w ≠ 0} := by
    rw [Metric.dense_iff]
    intro x r hr
    obtain ⟨y, hy, hjy⟩ := Work.Asymptotics.exists_jprime_ne_zero_near' x r hr
    exact ⟨y, Metric.mem_ball.mpr (dist_comm x y ▸ hy), hjy⟩
  intro z
  have hz : z ∈ closure {w : ℍ | AfunFun ℓ d (γ • w) w = 0} :=
    closure_mono hsub (by rw [hdense.closure_eq]; trivial)
  have hz0 : AfunFun ℓ d (γ • z) z = 0 := hclosed.closure_subset hz
  rw [Work.Asymptotics.KfunClear_eq_mul_AfunFun, hz0, mul_zero]

/-- The cleared kernel vanishes at the first grazing branch `blW τ`. -/
theorem KfunClear_blW (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) : Work.Kernels.KfunClear ℓ d τ (blW τ) = 0 := by
  rcases lt_or_ge 0 τ.re with h | h
  · have h1 : blW τ = (1 : ℝ) +ᵥ (ModularGroup.S • τ) := by
      rw [blW, show tsign τ = 1 from by unfold tsign; rw [if_pos h]]
    rw [h1]
    exact KfunClear_vadd_S ℓ d hd τ
  · rw [blW_eq_smul' h]
    have hv := KfunClear_graze_eq_zero ℓ d hd (ModularGroup.S * ModularGroup.T)
      (Or.inr (Or.inr (Or.inl rfl))) ((ModularGroup.T⁻¹ * ModularGroup.S) • τ)
    rw [← mul_smul, ST_mul_TinvS, SL_neg_smul, one_smul] at hv
    exact hv

/-- The cleared kernel vanishes at the second grazing branch `blV τ`. -/
theorem KfunClear_blV (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) : Work.Kernels.KfunClear ℓ d τ (blV τ) = 0 := by
  rcases lt_or_ge 0 τ.re with h | h
  · rw [blV_eq_smul h]
    have hv := KfunClear_graze_eq_zero ℓ d hd
      (ModularGroup.T * ModularGroup.S * ModularGroup.T)
      (Or.inl rfl) ((ModularGroup.S * (ModularGroup.T * ModularGroup.S)) • τ)
    rw [← mul_smul, TST_mul_STS, SL_neg_smul, one_smul] at hv
    exact hv
  · rw [blV_eq_smul' h]
    have hv := KfunClear_graze_eq_zero ℓ d hd
      (ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹
      (Or.inr (Or.inr (Or.inr rfl)))
      ((ModularGroup.S * (ModularGroup.T⁻¹ * ModularGroup.S)) • τ)
    rw [← mul_smul, TSTinv_mul_STinvS, SL_neg_smul, one_smul] at hv
    exact hv

end Work.Asymptotics.BlLow

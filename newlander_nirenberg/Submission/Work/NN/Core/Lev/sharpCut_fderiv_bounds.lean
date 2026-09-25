/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# First- and second-order bounds for the parametric radial cutoff `sharpCut a b`

`φ = Work.NN.Core.sharpCut a b : ℂ → ℂ` is the smooth radial cutoff
`φ ζ = σ ((b² - ‖ζ‖²)/(b²-a²))` (`σ = Real.smoothTransition`), which is `1` on `‖ζ‖ ≤ a` and
`0` for `b ≤ ‖ζ‖`.  This file proves that the gradient and the second derivative of `φ` are
bounded by explicit expressions in `a` and `b - a`: with `δ = b² - a²`,

* `‖∇φ ζ‖ ≤ 2 C₁ b/δ ≤ 2 C₁/(b-a)`,
* `‖D²φ ζ‖ ≤ 2 C₁/δ + 4 C₂ ‖ζ‖²/δ² ≤ 2 C₁/(a(b-a)) + 4 C₂/(b-a)²`,

where `C₁, C₂` bound `|σ'|` and `|σ''|`
(`Submission/Work/NN/Core/Lev/smoothTransition_deriv_data.lean`).  Both differentials *vanish*
unless `0 < (b²-‖ζ‖²)/δ < 1`, i.e. unless `a < ‖ζ‖ < b`, and on the shell `‖ζ‖ ≤ b`; that is
what makes the estimates uniform.  The bounds on `φ` itself and on `∇φ` as Lipschitz maps
follow by the mean value inequality on `Set.univ`.
-/
import Mathlib
import Submission.Work.NN.Core.sharpCut
import Submission.Work.NN.Core.Lev.smoothTransition_deriv_data

noncomputable section

open scoped ContDiff Topology BigOperators
open Set Filter

namespace Work.NN.Core.Lev

/-- `X ↦ ofRealCLM.comp X` as a continuous linear map, of norm `≤ 1`. -/
def ofRealCompL : (ℂ →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℂ) where
  toFun X := Complex.ofRealCLM.comp X
  map_add' X Y := by ext v; simp
  map_smul' c X := by ext v; simp

/-- `x ↦ (x : ℂ)` does not increase operator norms. -/
lemma opNorm_ofRealCLM_comp_le (X : ℂ →L[ℝ] ℝ) : ‖Complex.ofRealCLM.comp X‖ ≤ ‖X‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun v => ?_
  rw [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.norm_real]
  exact ContinuousLinearMap.le_opNorm X v

lemma norm_ofRealCompL_le : ‖ofRealCompL‖ ≤ (1 : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun X => ?_
  rw [one_mul]
  exact opNorm_ofRealCLM_comp_le X

/-- Normal form for a scalar multiple of a negated double smul. -/
lemma smul_neg_two_smul (c : ℝ) (X : ℂ →L[ℝ] ℝ) : c • (-(2 • X)) = (-(2 * c)) • X := by
  ext v
  simp only [smul_apply, neg_apply, smul_eq_mul]
  ring

/-- Norm of `c.smulRight w` for continuous linear maps. -/
lemma opNorm_smulRight_le (c : ℂ →L[ℝ] ℝ) (w : ℂ →L[ℝ] ℝ) : ‖c.smulRight w‖ ≤ ‖c‖ * ‖w‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [ContinuousLinearMap.smulRight_apply, norm_smul]
  calc ‖c v‖ * ‖w‖ ≤ (‖c‖ * ‖v‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm c v) (norm_nonneg _)
    _ = (‖c‖ * ‖w‖) * ‖v‖ := by ring

/-- **First- and second-order bounds for the parametric cutoff `sharpCut a b`.** -/
theorem sharpCut_fderiv_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ), 0 < a → a < b →
      (∀ x : ℂ, ‖fderiv ℝ (Work.NN.Core.sharpCut a b) x‖ ≤ C * (1 / (b - a))) ∧
      (∀ x y : ℂ, ‖Work.NN.Core.sharpCut a b x - Work.NN.Core.sharpCut a b y‖
          ≤ C * (1 / (b - a)) * ‖x - y‖) ∧
      (∀ x y : ℂ, ‖fderiv ℝ (Work.NN.Core.sharpCut a b) x
            - fderiv ℝ (Work.NN.Core.sharpCut a b) y‖
          ≤ C * (1 / (a * (b - a)) + 1 / (b - a) ^ 2) * ‖x - y‖) := by
  obtain ⟨C₁, C₂, hC₁0, hC₂0, hC₁, hC₂, hC1z, hC1o, hC2z, hC2o⟩ := smoothTransition_deriv_bounds
  refine ⟨max (max (2 * C₁) (4 * C₂)) 1, by positivity, ?_⟩
  intro a b ha hab
  have hbpos : 0 < b := lt_trans ha hab
  have hbapos : 0 < b - a := by linarith
  have hbapos2 : 0 < (b - a) ^ 2 := by positivity
  have habpos : 0 < a * (b - a) := mul_pos ha hbapos
  have hbapos3 : 0 < b + a := by linarith
  set δ : ℝ := b ^ 2 - a ^ 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; nlinarith
  have hδne : δ ≠ 0 := ne_of_gt hδpos
  have hδinv_nn : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδpos.le
  -- elementary inequalities for the reciprocal of δ
  have hinvδ₁ : 1 / δ ≤ 1 / (a * (b - a)) := by
    rw [div_le_div_iff₀ hδpos habpos]
    rw [hδdef]
    nlinarith [ha.le]
  have hinvδ₂ : b / δ ≤ 1 / (b - a) := by
    rw [div_le_div_iff₀ hδpos hbapos]
    rw [hδdef]
    nlinarith [ha.le]
  have hb2 : b ^ 2 / δ ^ 2 ≤ 1 / (b - a) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) hbapos2]
    rw [hδdef]
    nlinarith [ha.le, hbpos.le]
  -- the radial parameter and the "gradient of the quadratic"
  set u : ℂ → ℝ := fun ζ => (b ^ 2 - Complex.normSq ζ) / δ with hudef
  set Λ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) := (-(2 * δ⁻¹)) • (innerSL ℝ) with hΛdef
  have hΛ_apply : ∀ ζ : ℂ, Λ ζ = (-(2 * δ⁻¹)) • ((innerSL ℝ) ζ) := by
    intro ζ
    rw [hΛdef]
    rfl
  -- derivative of `u`
  have hu_fderiv : ∀ ζ : ℂ, HasFDerivAt (𝕜 := ℝ) u (Λ ζ) ζ := by
    intro ζ
    have h1 : HasFDerivAt (𝕜 := ℝ) (fun w : ℂ => Complex.normSq w) (2 • (innerSL ℝ) ζ) ζ :=
      Work.CR.Flat.hasFDerivAt_normSq_aux ζ
    have h2 : HasFDerivAt (𝕜 := ℝ) (fun w : ℂ => b ^ 2 - Complex.normSq w)
        (-(2 • (innerSL ℝ) ζ)) ζ := h1.const_sub (b ^ 2)
    have h3 : HasFDerivAt (𝕜 := ℝ) (δ⁻¹ • (fun w : ℂ => b ^ 2 - Complex.normSq w))
        (δ⁻¹ • (-(2 • (innerSL ℝ) ζ))) ζ := h2.const_smul (δ⁻¹)
    have hder : (δ⁻¹ • (-(2 • (innerSL ℝ) ζ))) = Λ ζ :=
      (smul_neg_two_smul δ⁻¹ ((innerSL ℝ) ζ)).trans (hΛ_apply ζ).symm
    rw [hder] at h3
    convert h3 using 1
    funext w
    simp only [hudef, Pi.smul_apply, smul_eq_mul]
    rw [div_eq_mul_inv]
    ring
  -- the norm of `Λ`
  have hinnerSL : ‖(innerSL ℝ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ))‖ ≤ (1 : ℝ) :=
    norm_innerSL_le (𝕜 := ℝ) (E := ℂ)
  have hΛnorm : ‖Λ‖ ≤ 2 / δ := by
    rw [hΛdef]
    calc ‖(-(2 * δ⁻¹)) • (innerSL ℝ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ))‖
        ≤ ‖(-(2 * δ⁻¹))‖ * ‖(innerSL ℝ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ))‖ :=
          ContinuousLinearMap.opNorm_smul_le _ _
      _ = (2 * δ⁻¹) * ‖(innerSL ℝ : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ))‖ := by
          rw [Real.norm_eq_abs, abs_neg,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * δ⁻¹)]
      _ ≤ (2 * δ⁻¹) * 1 := mul_le_mul_of_nonneg_left hinnerSL (by positivity)
      _ = 2 / δ := by ring
  have hΛapply : ∀ ζ : ℂ, ‖Λ ζ‖ ≤ 2 * ‖ζ‖ / δ := by
    intro ζ
    calc ‖Λ ζ‖ ≤ ‖Λ‖ * ‖ζ‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (2 / δ) * ‖ζ‖ := mul_le_mul_of_nonneg_right hΛnorm (norm_nonneg _)
      _ = 2 * ‖ζ‖ / δ := by ring
  -- derivative of the cutoff
  have hφ_fderiv : ∀ ζ : ℂ, fderiv ℝ (Work.NN.Core.sharpCut a b) ζ
      = Complex.ofRealCLM.comp
        ((deriv Real.smoothTransition (u ζ)) • (Λ ζ)) := by
    intro ζ
    have hσ : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (u ζ)) (u ζ) :=
      ((contDiff_smoothTransition.differentiable (by simp)) (u ζ)).hasDerivAt
    have h1 : HasFDerivAt (𝕜 := ℝ) (Real.smoothTransition ∘ u)
        (deriv Real.smoothTransition (u ζ) • (Λ ζ)) ζ := hσ.comp_hasFDerivAt ζ (hu_fderiv ζ)
    have h2 : HasFDerivAt (𝕜 := ℝ) (fun w : ℂ => (Real.smoothTransition (u w) : ℂ))
        (Complex.ofRealCLM.comp (deriv Real.smoothTransition (u ζ) • (Λ ζ))) ζ :=
      ContinuousLinearMap.hasFDerivAt Complex.ofRealCLM |>.comp ζ h1
    have hfun : (fun w : ℂ => (Real.smoothTransition (u w) : ℂ))
        = Work.NN.Core.sharpCut a b := by
      funext w
      rw [Work.NN.Core.sharpCut, Work.NN.Core.sharpCutReal, hudef, hδdef]
    rw [← hfun]
    exact h2.fderiv
  -- the shell hypothesis implies `‖ζ‖ ≤ b`
  have hshell_le : ∀ ζ : ℂ, u ζ ∈ Set.Ioo (0 : ℝ) 1 → ‖ζ‖ ≤ b := by
    intro ζ hζ
    have h1 : 0 < b ^ 2 - Complex.normSq ζ := by
      have h2 : 0 < u ζ := hζ.1
      rw [hudef] at h2
      have h3 : (b ^ 2 - Complex.normSq ζ) / δ * δ > 0 := mul_pos h2 hδpos
      rwa [div_mul_cancel₀ _ hδne] at h3
    rw [Complex.normSq_eq_norm_sq] at h1
    by_contra hcon
    push_neg at hcon
    have h4 := mul_self_le_mul_self hbpos.le hcon.le
    nlinarith
  have hσ'zero : ∀ ζ : ℂ, u ζ ∉ Set.Ioo (0 : ℝ) 1 → deriv Real.smoothTransition (u ζ) = 0 := by
    intro ζ hζ
    have hz : u ζ ≤ 0 ∨ 1 ≤ u ζ := by
      by_contra hcon
      push_neg at hcon
      exact hζ ⟨hcon.1, hcon.2⟩
    rcases hz with hz | hz
    · exact hC1z (u ζ) hz
    · exact hC1o (u ζ) hz
  have hσ''zero : ∀ ζ : ℂ, u ζ ∉ Set.Ioo (0 : ℝ) 1 →
      deriv (deriv Real.smoothTransition) (u ζ) = 0 := by
    intro ζ hζ
    have hz : u ζ ≤ 0 ∨ 1 ≤ u ζ := by
      by_contra hcon
      push_neg at hcon
      exact hζ ⟨hcon.1, hcon.2⟩
    rcases hz with hz | hz
    · exact hC2z (u ζ) hz
    · exact hC2o (u ζ) hz
  -- first-order bound
  have hfirst : ∀ ζ : ℂ, ‖fderiv ℝ (Work.NN.Core.sharpCut a b) ζ‖ ≤ 2 * C₁ / (b - a) := by
    intro ζ
    rw [hφ_fderiv ζ]
    by_cases hζ : u ζ ∈ Set.Ioo (0 : ℝ) 1
    · have hnorm_lt : ‖ζ‖ ≤ b := hshell_le ζ hζ
      have hσ'le : ‖deriv Real.smoothTransition (u ζ)‖ ≤ C₁ := by
        rw [Real.norm_eq_abs]
        exact hC₁ (u ζ)
      have h2 : ‖Λ ζ‖ ≤ 2 * b / δ := by
        calc ‖Λ ζ‖ ≤ 2 * ‖ζ‖ / δ := hΛapply ζ
          _ = (2 * ‖ζ‖) * δ⁻¹ := by ring
          _ ≤ (2 * b) * δ⁻¹ :=
              mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = 2 * b / δ := by ring
      calc ‖Complex.ofRealCLM.comp ((deriv Real.smoothTransition (u ζ)) • (Λ ζ))‖
          ≤ ‖(deriv Real.smoothTransition (u ζ)) • (Λ ζ)‖ := opNorm_ofRealCLM_comp_le _
        _ = ‖deriv Real.smoothTransition (u ζ)‖ * ‖Λ ζ‖ := norm_smul _ _
        _ ≤ C₁ * (2 * b / δ) := mul_le_mul hσ'le h2 (norm_nonneg _) hC₁0
        _ = 2 * C₁ * (b / δ) := by ring
        _ ≤ 2 * C₁ * (1 / (b - a)) := mul_le_mul_of_nonneg_left hinvδ₂ (by positivity)
        _ = 2 * C₁ / (b - a) := by ring
    · rw [hσ'zero ζ hζ, zero_smul]
      simp only [ContinuousLinearMap.comp_zero, norm_zero]
      positivity
  have hval : ∀ x y : ℂ, ‖Work.NN.Core.sharpCut a b x - Work.NN.Core.sharpCut a b y‖
      ≤ (2 * C₁ / (b - a)) * ‖x - y‖ := by
    intro x y
    have hcd : Differentiable ℝ (Work.NN.Core.sharpCut a b) :=
      (Work.NN.Core.contDiff_sharpCut (a := a) (b := b)).differentiable (by simp)
    exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (f := Work.NN.Core.sharpCut a b) (C := 2 * C₁ / (b - a))
      (fun z _ => hcd.differentiableAt) (fun z _ => hfirst z)
      (x := y) (y := x) (Set.mem_univ _) (Set.mem_univ _)
  -- second derivative
  set Φ : ℂ → (ℂ →L[ℝ] ℝ) := fun ζ => (deriv Real.smoothTransition (u ζ)) • (Λ ζ) with hΦdef
  have hΦ_fderiv : ∀ ζ : ℂ, HasFDerivAt (𝕜 := ℝ) Φ
      ((deriv Real.smoothTransition (u ζ)) • Λ
        + (((deriv (deriv Real.smoothTransition) (u ζ)) • (Λ ζ)).smulRight (Λ ζ))) ζ := by
    intro ζ
    have hc : HasFDerivAt (𝕜 := ℝ) (fun z : ℂ => deriv Real.smoothTransition (u z))
        ((deriv (deriv Real.smoothTransition) (u ζ)) • (Λ ζ)) ζ := by
      have hσ' : HasDerivAt (deriv Real.smoothTransition)
          (deriv (deriv Real.smoothTransition) (u ζ)) (u ζ) :=
        ((contDiff_deriv_smoothTransition.differentiable (by simp)) (u ζ)).hasDerivAt
      exact hσ'.comp_hasFDerivAt ζ (hu_fderiv ζ)
    have hΛd : HasFDerivAt (𝕜 := ℝ) Λ Λ ζ := ContinuousLinearMap.hasFDerivAt Λ
    have h := hc.smul hΛd
    have hfun : ((fun z : ℂ => deriv Real.smoothTransition (u z)) • ⇑Λ) = Φ := by
      funext z
      rw [hΦdef]
      rfl
    rw [hfun] at h
    exact h
  have hfd_eq : (fun w => fderiv ℝ (Work.NN.Core.sharpCut a b) w) = ofRealCompL ∘ Φ := by
    funext w
    rw [hφ_fderiv w, hΦdef]
    rfl
  have hcd2 : Differentiable ℝ (fun w => fderiv ℝ (Work.NN.Core.sharpCut a b) w) := by
    rw [hfd_eq]
    intro z
    exact (ContinuousLinearMap.differentiableAt ofRealCompL).comp z (hΦ_fderiv z).differentiableAt
  have hsecond_fd : ∀ ζ : ℂ, fderiv ℝ (fun w => fderiv ℝ (Work.NN.Core.sharpCut a b) w) ζ
      = ofRealCompL ∘SL
        ((deriv Real.smoothTransition (u ζ)) • Λ
          + (((deriv (deriv Real.smoothTransition) (u ζ)) • (Λ ζ)).smulRight (Λ ζ))) := by
    intro ζ
    rw [hfd_eq]
    exact (ContinuousLinearMap.hasFDerivAt ofRealCompL |>.comp ζ (hΦ_fderiv ζ)).fderiv
  have hsecond : ∀ ζ : ℂ,
      ‖fderiv ℝ (fun w => fderiv ℝ (Work.NN.Core.sharpCut a b) w) ζ‖
        ≤ 2 * C₁ / (a * (b - a)) + 4 * C₂ / (b - a) ^ 2 := by
    intro ζ
    rw [hsecond_fd ζ]
    set A : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) := (deriv Real.smoothTransition (u ζ)) • Λ with hAdef
    set B : ℂ →L[ℝ] (ℂ →L[ℝ] ℝ) :=
      ((deriv (deriv Real.smoothTransition) (u ζ)) • (Λ ζ)).smulRight (Λ ζ) with hBdef
    have hcompAB : ‖ofRealCompL ∘SL (A + B)‖ ≤ ‖A + B‖ := by
      calc ‖ofRealCompL ∘SL (A + B)‖ ≤ ‖ofRealCompL‖ * ‖A + B‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * ‖A + B‖ := mul_le_mul_of_nonneg_right norm_ofRealCompL_le
              (ContinuousLinearMap.opNorm_nonneg (A + B))
        _ = ‖A + B‖ := one_mul _
    by_cases hζ : u ζ ∈ Set.Ioo (0 : ℝ) 1
    · have hnorm_lt : ‖ζ‖ ≤ b := hshell_le ζ hζ
      have hσ'le : ‖deriv Real.smoothTransition (u ζ)‖ ≤ C₁ := by
        rw [Real.norm_eq_abs]; exact hC₁ (u ζ)
      have hσ''le : ‖deriv (deriv Real.smoothTransition) (u ζ)‖ ≤ C₂ := by
        rw [Real.norm_eq_abs]; exact hC₂ (u ζ)
      have hlam : ‖Λ ζ‖ ≤ 2 * b / δ := by
        calc ‖Λ ζ‖ ≤ 2 * ‖ζ‖ / δ := hΛapply ζ
          _ = (2 * ‖ζ‖) * δ⁻¹ := by ring
          _ ≤ (2 * b) * δ⁻¹ :=
              mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = 2 * b / δ := by ring
      have h1 : ‖A‖ ≤ 2 * C₁ / (a * (b - a)) := by
        rw [hAdef]
        calc ‖(deriv Real.smoothTransition (u ζ)) • Λ‖
            ≤ ‖deriv Real.smoothTransition (u ζ)‖ * ‖Λ‖ :=
              ContinuousLinearMap.opNorm_smul_le _ _
          _ ≤ C₁ * (2 / δ) := mul_le_mul hσ'le hΛnorm (ContinuousLinearMap.opNorm_nonneg Λ) hC₁0
          _ = (2 * C₁) * (1 / δ) := by ring
          _ ≤ (2 * C₁) * (1 / (a * (b - a))) := mul_le_mul_of_nonneg_left hinvδ₁ (by positivity)
          _ = 2 * C₁ / (a * (b - a)) := by ring
      have hinner : ‖(deriv (deriv Real.smoothTransition) (u ζ)) • (Λ ζ)‖ ≤ C₂ * (2 * b / δ) := by
        calc ‖(deriv (deriv Real.smoothTransition) (u ζ)) • (Λ ζ)‖
            ≤ ‖deriv (deriv Real.smoothTransition) (u ζ)‖ * ‖Λ ζ‖ :=
              ContinuousLinearMap.opNorm_smul_le _ _
          _ ≤ C₂ * (2 * b / δ) := mul_le_mul hσ''le hlam (ContinuousLinearMap.opNorm_nonneg _) hC₂0
      have h2 : ‖B‖ ≤ 4 * C₂ / (b - a) ^ 2 := by
        rw [hBdef]
        calc ‖((deriv (deriv Real.smoothTransition) (u ζ)) • (Λ ζ)).smulRight (Λ ζ)‖
            ≤ ‖(deriv (deriv Real.smoothTransition) (u ζ)) • (Λ ζ)‖ * ‖Λ ζ‖ :=
              opNorm_smulRight_le _ _
          _ ≤ (C₂ * (2 * b / δ)) * (2 * b / δ) :=
              mul_le_mul hinner hlam (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
          _ = 4 * C₂ * (b ^ 2 / δ ^ 2) := by ring_nf
          _ ≤ 4 * C₂ * (1 / (b - a) ^ 2) := mul_le_mul_of_nonneg_left hb2 (by positivity)
          _ = 4 * C₂ / (b - a) ^ 2 := by ring
      calc ‖ofRealCompL ∘SL (A + B)‖ ≤ ‖A + B‖ := hcompAB
        _ ≤ ‖A‖ + ‖B‖ := norm_add_le A B
        _ ≤ 2 * C₁ / (a * (b - a)) + 4 * C₂ / (b - a) ^ 2 := add_le_add h1 h2
    · have hA0 : ‖A‖ ≤ 0 := by
        rw [hAdef, hσ'zero ζ hζ]
        calc ‖(0 : ℝ) • Λ‖ ≤ ‖(0 : ℝ)‖ * ‖Λ‖ := ContinuousLinearMap.opNorm_smul_le _ _
          _ = 0 := by norm_num
      have hB0 : ‖B‖ ≤ 0 := by
        rw [hBdef, hσ''zero ζ hζ]
        calc ‖((0 : ℝ) • (Λ ζ)).smulRight (Λ ζ)‖ ≤ ‖(0 : ℝ) • (Λ ζ)‖ * ‖Λ ζ‖ :=
              opNorm_smulRight_le _ _
          _ ≤ (‖(0 : ℝ)‖ * ‖Λ ζ‖) * ‖Λ ζ‖ :=
              mul_le_mul_of_nonneg_right
                (ContinuousLinearMap.opNorm_smul_le (0 : ℝ) (Λ ζ)) (ContinuousLinearMap.opNorm_nonneg _)
          _ = 0 := by norm_num
      calc ‖ofRealCompL ∘SL (A + B)‖ ≤ ‖A + B‖ := hcompAB
        _ ≤ ‖A‖ + ‖B‖ := norm_add_le A B
        _ ≤ 0 + 0 := add_le_add hA0 hB0
        _ = 0 := by norm_num
        _ ≤ 2 * C₁ / (a * (b - a)) + 4 * C₂ / (b - a) ^ 2 := by positivity
  have hgrad : ∀ x y : ℂ, ‖fderiv ℝ (Work.NN.Core.sharpCut a b) x
        - fderiv ℝ (Work.NN.Core.sharpCut a b) y‖
      ≤ (2 * C₁ / (a * (b - a)) + 4 * C₂ / (b - a) ^ 2) * ‖x - y‖ := by
    intro x y
    exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (f := fun w => fderiv ℝ (Work.NN.Core.sharpCut a b) w)
      (C := 2 * C₁ / (a * (b - a)) + 4 * C₂ / (b - a) ^ 2)
      (fun z _ => hcd2.differentiableAt) (fun z _ => hsecond z)
      (x := y) (y := x) (Set.mem_univ _) (Set.mem_univ _)
  refine ⟨?_, ?_, ?_⟩
  · intro ζ
    have hCge1 : 2 * C₁ ≤ max (max (2 * C₁) (4 * C₂)) 1 :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    have hnn : 0 ≤ 1 / (b - a) := by positivity
    calc ‖fderiv ℝ (Work.NN.Core.sharpCut a b) ζ‖ ≤ 2 * C₁ / (b - a) := hfirst ζ
      _ = (2 * C₁) * (1 / (b - a)) := by ring
      _ ≤ max (max (2 * C₁) (4 * C₂)) 1 * (1 / (b - a)) :=
          mul_le_mul_of_nonneg_right hCge1 hnn
  · intro x y
    have hCge1 : 2 * C₁ ≤ max (max (2 * C₁) (4 * C₂)) 1 :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    have hnn : 0 ≤ 1 / (b - a) := by positivity
    have hxy : 0 ≤ ‖x - y‖ := norm_nonneg _
    calc ‖Work.NN.Core.sharpCut a b x - Work.NN.Core.sharpCut a b y‖
        ≤ (2 * C₁ / (b - a)) * ‖x - y‖ := hval x y
      _ = ((2 * C₁) * (1 / (b - a))) * ‖x - y‖ := by ring
      _ ≤ (max (max (2 * C₁) (4 * C₂)) 1 * (1 / (b - a))) * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCge1 hnn) hxy
      _ = max (max (2 * C₁) (4 * C₂)) 1 * (1 / (b - a)) * ‖x - y‖ := by ring
  · intro x y
    have hCge1 : 2 * C₁ ≤ max (max (2 * C₁) (4 * C₂)) 1 :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    have hCge2 : 4 * C₂ ≤ max (max (2 * C₁) (4 * C₂)) 1 :=
      le_trans (le_max_right _ _) (le_max_left _ _)
    have hxy : 0 ≤ ‖x - y‖ := norm_nonneg _
    have h2C : 2 * C₁ / (a * (b - a))
        ≤ max (max (2 * C₁) (4 * C₂)) 1 * (1 / (a * (b - a))) := by
      rw [mul_one_div]
      exact mul_le_mul_of_nonneg_right hCge1 (by positivity)
    have h4C : 4 * C₂ / (b - a) ^ 2
        ≤ max (max (2 * C₁) (4 * C₂)) 1 * (1 / (b - a) ^ 2) := by
      rw [mul_one_div]
      exact mul_le_mul_of_nonneg_right hCge2 (by positivity)
    have hkey : 2 * C₁ / (a * (b - a)) + 4 * C₂ / (b - a) ^ 2
        ≤ max (max (2 * C₁) (4 * C₂)) 1
          * (1 / (a * (b - a)) + 1 / (b - a) ^ 2) := by
      calc 2 * C₁ / (a * (b - a)) + 4 * C₂ / (b - a) ^ 2
          ≤ max (max (2 * C₁) (4 * C₂)) 1 * (1 / (a * (b - a)))
            + max (max (2 * C₁) (4 * C₂)) 1 * (1 / (b - a) ^ 2) := add_le_add h2C h4C
        _ = max (max (2 * C₁) (4 * C₂)) 1
              * (1 / (a * (b - a)) + 1 / (b - a) ^ 2) := by ring
    calc ‖fderiv ℝ (Work.NN.Core.sharpCut a b) x
          - fderiv ℝ (Work.NN.Core.sharpCut a b) y‖
        ≤ (2 * C₁ / (a * (b - a)) + 4 * C₂ / (b - a) ^ 2) * ‖x - y‖ := hgrad x y
      _ ≤ (max (max (2 * C₁) (4 * C₂)) 1
            * (1 / (a * (b - a)) + 1 / (b - a) ^ 2)) * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right hkey hxy
      _ = max (max (2 * C₁) (4 * C₂)) 1
            * (1 / (a * (b - a)) + 1 / (b - a) ^ 2) * ‖x - y‖ := by ring

end Work.NN.Core.Lev

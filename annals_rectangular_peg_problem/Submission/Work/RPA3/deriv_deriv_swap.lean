import Mathlib

namespace Work.RPA3

open Filter
open scoped Topology

/-- The partial derivative of `f : ℝ × ℝ → E` in its first variable, at the point `a`,
with the second variable held at `b`, equals `f' (1, 0)` where `f'` is the Fréchet
derivative of `f` at `(a, b)`. -/
lemma deriv_prodMk_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → E} {f' : ℝ × ℝ →L[ℝ] E} {a b : ℝ}
    (hf : HasFDerivAt f f' (a, b)) :
    deriv (fun σ => f (σ, b)) a = f' (1, 0) := by
  have h1 : HasFDerivAt (fun σ : ℝ => (σ, b)) (ContinuousLinearMap.inl ℝ ℝ ℝ) a :=
    hasFDerivAt_prodMk_left a b
  have h2 : HasFDerivAt (fun σ : ℝ => f (σ, b))
      (f'.comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) a := by
    simpa [Function.comp_def] using hf.comp a h1
  rw [h2.hasDerivAt.deriv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

/-- The partial derivative of `f : ℝ × ℝ → E` in its second variable, at the point `b`,
with the first variable held at `a`, equals `f' (0, 1)`. -/
lemma deriv_prodMk_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → E} {f' : ℝ × ℝ →L[ℝ] E} {a b : ℝ}
    (hf : HasFDerivAt f f' (a, b)) :
    deriv (fun y => f (a, y)) b = f' (0, 1) := by
  have h1 : HasFDerivAt (fun y : ℝ => (a, y)) (ContinuousLinearMap.inr ℝ ℝ ℝ) b :=
    hasFDerivAt_prodMk_right a b
  have h2 : HasFDerivAt (fun y : ℝ => f (a, y))
      (f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) b := by
    simpa [Function.comp_def] using hf.comp b h1
  rw [h2.hasDerivAt.deriv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- Second-variable differentiation commutes with evaluation: for a family of continuous
linear maps `f`, the derivative of `y ↦ f (a, y) v` at `b` is `(fderiv f (a,b) (0,1)) v`. -/
lemma deriv_prodMk_right_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] E}
    {f' : ℝ × ℝ →L[ℝ] ((ℝ × ℝ) →L[ℝ] E)} {a b : ℝ}
    (hf : HasFDerivAt f f' (a, b)) (v : ℝ × ℝ) :
    deriv (fun y => f (a, y) v) b = f' (0, 1) v := by
  have h : HasFDerivAt (fun z => f z v) (((ContinuousLinearMap.apply ℝ E) v).comp f') (a, b) :=
    ((ContinuousLinearMap.apply ℝ E) v).hasFDerivAt.comp (a, b) hf
  have := deriv_prodMk_right h
  simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] using this

/-- First-variable differentiation commutes with evaluation. -/
lemma deriv_prodMk_left_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] E}
    {f' : ℝ × ℝ →L[ℝ] ((ℝ × ℝ) →L[ℝ] E)} {a b : ℝ}
    (hf : HasFDerivAt f f' (a, b)) (v : ℝ × ℝ) :
    deriv (fun σ => f (σ, b) v) a = f' (1, 0) v := by
  have h : HasFDerivAt (fun z => f z v) (((ContinuousLinearMap.apply ℝ E) v).comp f') (a, b) :=
    ((ContinuousLinearMap.apply ℝ E) v).hasFDerivAt.comp (a, b) hf
  have := deriv_prodMk_left h
  simpa [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] using this

/-- Schwarz's theorem for the iterated partial derivatives of a `C²` function
`G : ℝ × ℝ → E`: the mixed second partial derivatives commute. -/
theorem deriv_deriv_swap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : ℝ × ℝ → E} {a b : ℝ} (hG : ContDiffAt ℝ 2 G (a, b)) :
    deriv (fun y => deriv (fun σ => G (σ, y)) a) b
      = deriv (fun σ => deriv (fun y => G (σ, y)) b) a := by
  let F : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] E := fderiv ℝ G
  have hF : HasFDerivAt F (fderiv ℝ F (a, b)) (a, b) := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ G) (a, b) :=
      hG.fderiv_right (m := 1) (by norm_num)
    exact (h1.differentiableAt (by norm_num)).hasFDerivAt
  have hGev : ∀ᶠ z in 𝓝 (a, b), ContDiffAt ℝ 2 G z := hG.eventually (by norm_num)
  have htendL : Tendsto (fun y : ℝ => (a, y)) (𝓝 b) (𝓝 (a, b)) :=
    (continuous_const.prodMk continuous_id).tendsto b
  have hGevL : ∀ᶠ y in 𝓝 b, ContDiffAt ℝ 2 G (a, y) := htendL.eventually hGev
  have heqL : (fun y => deriv (fun σ => G (σ, y)) a) =ᶠ[𝓝 b]
      (fun y => F (a, y) (1, 0)) := by
    filter_upwards [hGevL] with y hy
    exact deriv_prodMk_left ((hy.differentiableAt (by norm_num)).hasFDerivAt)
  have htendR : Tendsto (fun σ : ℝ => (σ, b)) (𝓝 a) (𝓝 (a, b)) :=
    (continuous_id.prodMk continuous_const).tendsto a
  have hGevR : ∀ᶠ σ in 𝓝 a, ContDiffAt ℝ 2 G (σ, b) := htendR.eventually hGev
  have heqR : (fun σ => deriv (fun y => G (σ, y)) b) =ᶠ[𝓝 a]
      (fun σ => F (σ, b) (0, 1)) := by
    filter_upwards [hGevR] with σ hσ
    exact deriv_prodMk_right ((hσ.differentiableAt (by norm_num)).hasFDerivAt)
  rw [heqL.deriv_eq, heqR.deriv_eq, deriv_prodMk_right_apply hF (1, 0),
    deriv_prodMk_left_apply hF (0, 1)]
  exact (hG.isSymmSndFDerivAt (by simp) (1, 0) (0, 1)).symm

end Work.RPA3

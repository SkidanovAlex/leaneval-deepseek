import Mathlib
import Submission.Work.Morse.Transfer

namespace Work.Morse

open scoped Manifold ContDiff Topology

/-! ## The analysis input

Before transferring `HasNondegHessian` across a change of model we record the two
elementary facts about precomposing a function `g : E → ℝ` with the inverse of a
continuous linear equivalence `L : E ≃L[ℝ] E'`.

The point is that these two facts are *unconditional*: they hold even when `g` is
not differentiable, because `ContinuousLinearEquiv.comp_right_fderiv` and
`ContinuousLinearEquiv.comp_fderiv` are stated for `fderiv` without a
differentiability hypothesis (the two "bad" cases are both `0`).
-/

/-- The first derivative of `g ∘ L.symm` at `L a`. -/
private lemma fderiv_comp_symm_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (L : E ≃L[ℝ] E') (g : E → ℝ) (a : E) :
    fderiv ℝ (fun z : E' => g (L.symm z)) (L a)
      = (fderiv ℝ g a).comp (L.symm : E' →L[ℝ] E) := by
  rw [show (fun z : E' => g (L.symm z)) = (g ∘ ⇑(L.symm)) from rfl]
  rw [ContinuousLinearEquiv.comp_right_fderiv (iso := L.symm) (f := g) (x := L a)]
  simp

/-- The second derivative of `g ∘ L.symm` at `L a`, applied to a pair of vectors, is the second
derivative of `g` at `a` applied to the images under `L.symm`. -/
private lemma fderiv_fderiv_comp_symm_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (L : E ≃L[ℝ] E') (g : E → ℝ) (a : E) (v w : E') :
    (fderiv ℝ (fderiv ℝ (fun z : E' => g (L.symm z))) (L a)) v w =
      (fderiv ℝ (fderiv ℝ g) a) (L.symm v) (L.symm w) := by
  -- `ρ` is the continuous linear equivalence `φ ↦ φ ∘ L.symm`; it is the `arrowCongr` of `L` with
  -- the identity of `ℝ`.
  let ρ : (E →L[ℝ] ℝ) ≃L[ℝ] (E' →L[ℝ] ℝ) :=
    ContinuousLinearEquiv.arrowCongr L (ContinuousLinearEquiv.refl ℝ ℝ)
  have hρ : ∀ φ : E →L[ℝ] ℝ, ρ φ = φ.comp (L.symm : E' →L[ℝ] E) := by
    intro φ; ext x
    show (ContinuousLinearEquiv.arrowCongr L (ContinuousLinearEquiv.refl ℝ ℝ)) φ x = _
    simp [ContinuousLinearEquiv.arrowCongr]
  have h1 : fderiv ℝ (fun z : E' => g (L.symm z)) = fun z => ρ (fderiv ℝ g (L.symm z)) := by
    funext z
    rw [show (fun z : E' => g (L.symm z)) = (g ∘ ⇑(L.symm)) from rfl]
    rw [ContinuousLinearEquiv.comp_right_fderiv (iso := L.symm) (f := g) (x := z)]
    rw [hρ]
  have hk : fderiv ℝ (fun z : E' => fderiv ℝ g (L.symm z)) (L a) =
      ((fderiv ℝ (fderiv ℝ g) a)).comp (L.symm : E' →L[ℝ] E) := by
    rw [show (fun z : E' => fderiv ℝ g (L.symm z)) = ((fderiv ℝ g) ∘ ⇑(L.symm)) from rfl]
    rw [ContinuousLinearEquiv.comp_right_fderiv (iso := L.symm) (f := fderiv ℝ g) (x := L a)]
    simp
  have key : fderiv ℝ (fderiv ℝ (fun z : E' => g (L.symm z))) (L a) =
      ρ.toContinuousLinearMap.comp (((fderiv ℝ (fderiv ℝ g) a)).comp (L.symm : E' →L[ℝ] E)) := by
    rw [h1]
    rw [show (fun z : E' => ρ (fderiv ℝ g (L.symm z)))
        = (⇑ρ ∘ fun z : E' => fderiv ℝ g (L.symm z)) from rfl]
    rw [ContinuousLinearEquiv.comp_fderiv (𝕜 := ℝ) (E := E →L[ℝ] ℝ) (F := E' →L[ℝ] ℝ)
      (G := E') ρ (f := fun z : E' => fderiv ℝ g (L.symm z)) (x := L a)]
    rw [hk]
  rw [key]
  rw [show (ρ.toContinuousLinearMap.comp
        (((fderiv ℝ (fderiv ℝ g) a)).comp (L.symm : E' →L[ℝ] E)) : E' →L[ℝ] (E' →L[ℝ] ℝ)) v
      = ρ ((fderiv ℝ (fderiv ℝ g) a) (L.symm v)) from by
    simp [ContinuousLinearMap.comp_apply]]
  rw [hρ]
  rw [ContinuousLinearMap.comp_apply]
  rfl

/-- `HasNondegHessian` is invariant under pushing the atlas of `M` forward along
`Work.Morse.modelHomeo I L` (`Submission.Work.Morse.Transfer`): apply the chart
`Work.Morse.pushChart (Work.Morse.modelHomeo I L) e` to a chart `e` witnessing the Hessian
condition; it lies in the pushed maximal atlas by `Work.Morse.mem_maximalAtlas_push`, and its chart
expression is the original one composed with `L.symm`, so the chain rule (twice) identifies the
first and second derivatives with those of the original expression precomposed with `L.symm`; since
`L.symm` is an equivalence the nondegeneracy transfers. -/
theorem hasNondegHessian_push {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    (L : E ≃L[ℝ] E') [IsManifold I ∞ M] {f : M → ℝ} {x : M}
    (h : HasNondegHessian (I := I) (n := ∞) f x) :
    (letI : ChartedSpace E' M := Work.Morse.pushChartedSpace (Work.Morse.modelHomeo I L);
      letI : IsManifold (𝓘(ℝ,E')) ∞ M := Work.Morse.push_isManifold L;
      HasNondegHessian (I := 𝓘(ℝ,E')) (n := ∞) f x) := by
  letI : ChartedSpace E' M := pushChartedSpace (modelHomeo I L)
  letI : IsManifold (𝓘(ℝ,E')) ∞ M := push_isManifold L
  obtain ⟨e, he, hx, hd, hnd⟩ := h
  -- The chart expression of `f` in the original model, and the same hypothesis read off through it.
  let g : E → ℝ := fun y => f (e.symm (I.symm y))
  have hd' : fderiv ℝ g (I (e x)) = 0 := hd
  have hnd' : ∀ v : E, (∀ w, ((fderiv ℝ (fderiv ℝ g) (I (e x))) v) w = 0) → v = 0 := hnd
  -- The chart expression of `f` in the pushed model is `g ∘ L.symm` …
  have hfun : (fun x : E' => f ((pushChart (modelHomeo I L) e).symm ((𝓘(ℝ,E')).symm x)))
      = fun z : E' => g (L.symm z) := by
    funext y
    simp only [modelWithCornersSelf_coe_symm, id_eq]
    rw [show (pushChart (modelHomeo I L) e).symm y = e.symm (I.symm (L.symm y)) from by
      simp [pushChart, modelHomeo_symm_apply]]
  -- … and its point of evaluation is `L (I (e x))`, the image under `L` of the original one.
  have hpt : (𝓘(ℝ,E')) (pushChart (modelHomeo I L) e x) = L (I (e x)) := by
    simp [pushChart]
  refine ⟨pushChart (modelHomeo I L) e, ?_, ?_, ?_, ?_⟩
  · exact mem_maximalAtlas_push L he
  · rw [pushChart_source]; exact hx
  · rw [hfun, hpt, fderiv_comp_symm_apply L g (I (e x)), hd']
    simp
  · rw [hfun, hpt]
    intro v hv
    -- evaluate the nondegeneracy hypothesis of `g` on `L.symm v`
    have hA : (fderiv ℝ (fderiv ℝ g) (I (e x))) (L.symm v) = 0 := by
      ext u
      have h1 := hv (L u)
      rw [fderiv_fderiv_comp_symm_apply L g (I (e x)) v (L u)] at h1
      simpa using h1
    have h2 := hnd' (L.symm v) (fun w => by rw [hA]; simp)
    rw [show v = L (L.symm v) from (L.apply_symm_apply v).symm, h2, map_zero]

end Work.Morse

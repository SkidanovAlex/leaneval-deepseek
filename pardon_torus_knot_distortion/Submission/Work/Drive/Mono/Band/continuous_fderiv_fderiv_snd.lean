import Mathlib

namespace Work.Drive.Mono.Band

/-- The continuous linear map `L ↦ L.comp g` (post-composition with a fixed continuous
linear map). -/
private noncomputable def preComp {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : E →L[ℝ] F) : (F →L[ℝ] G) →L[ℝ] (E →L[ℝ] G) :=
  (ContinuousLinearMap.compL ℝ E F G).flip g

private lemma preComp_apply {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (g : E →L[ℝ] F) (f : F →L[ℝ] G) :
    preComp g f = f.comp g := by
  rw [preComp, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]

/-- Chain rule for the slice of a map `α × (ℝ × ℝ) → β` in the second variable. -/
private lemma fderiv_slice {α β : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    [NormedAddCommGroup β] [NormedSpace ℝ β]
    (X : α × (ℝ × ℝ) → β) (a : α) (q : ℝ × ℝ) (hX : DifferentiableAt ℝ X (a, q)) :
    fderiv ℝ (fun q' : ℝ × ℝ => X (a, q')) q =
      (fderiv ℝ X (a, q)).comp (ContinuousLinearMap.inr ℝ α (ℝ × ℝ)) := by
  have hg : DifferentiableAt ℝ (fun q' : ℝ × ℝ => (a, q')) q :=
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) a q).differentiableAt
  have h := fderiv_comp (𝕜 := ℝ) (x := q) (f := fun q' : ℝ × ℝ => (a, q')) (g := X) hX hg
  rw [(hasFDerivAt_prodMk_right (𝕜 := ℝ) a q).fderiv] at h
  simpa [Function.comp_def] using h

/-- **Joint continuity of the second derivative in the second variable.**  If `H : α × (ℝ × ℝ) → ℝ`
is `C²` then the map `v ↦ fderiv ℝ (fderiv ℝ (fun q => H (v.1, q))) v.2`, which sends a point `v` to
the Hessian of the function `q ↦ H (v.1, q)` at `v.2`, is continuous.  (Namespace
`Work.Drive.Mono.Band`, file `Submission/Work/Drive/Mono/Band/continuous_fderiv_fderiv_snd.lean`,
importing Mathlib only.)

Intended proof: put `G p := (fderiv ℝ H p) ∘L ContinuousLinearMap.inr ℝ α (ℝ × ℝ)`, so that
`fderiv ℝ (fun q => H (v.1, q)) = fun q => G (v.1, q)`.  If `H` is `C²` then `fderiv ℝ H` is `C¹`,
hence `G` is `C¹` (it is `fderiv ℝ H` followed by the continuous linear `· ∘L inr`), hence
`fderiv ℝ G` is continuous; and
`fderiv ℝ (fderiv ℝ (fun q => H (v.1,q))) v.2 = (fderiv ℝ G v) ∘L inr`, which is continuous as a
function of `v`. -/
theorem continuous_fderiv_fderiv_snd {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    {H : α × (ℝ × ℝ) → ℝ} (hH : ContDiff ℝ 2 H) :
    Continuous (fun v : α × (ℝ × ℝ) =>
      fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => H (v.1, q))) v.2) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ H) := hH.fderiv_right (m := 1) (by norm_num)
  have hHdiff : Differentiable ℝ H := hH.differentiable (by norm_num)
  have h1diff : Differentiable ℝ (fderiv ℝ H) := h1.differentiable (by norm_num)
  have hD2 : Continuous (fun v : α × (ℝ × ℝ) => fderiv ℝ (fderiv ℝ H) v) :=
    h1.continuous_fderiv (by norm_num)
  -- The second derivative of the slice is the second derivative of `H`, twice restricted
  -- to the second coordinate.
  have key : ∀ v : α × (ℝ × ℝ),
      fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => H (v.1, q))) v.2
        = (preComp (ContinuousLinearMap.inr ℝ α (ℝ × ℝ))).comp
            ((fderiv ℝ (fderiv ℝ H) v).comp (ContinuousLinearMap.inr ℝ α (ℝ × ℝ))) := by
    intro v
    have hslice : DifferentiableAt ℝ (fun q : ℝ × ℝ => (v.1, q)) v.2 :=
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) v.1 v.2).differentiableAt
    have hΨd' : DifferentiableAt ℝ (fun q : ℝ × ℝ => fderiv ℝ H (v.1, q)) v.2 :=
      DifferentiableAt.comp v.2 (h1diff.differentiableAt) hslice
    -- the slice of the derivative is the derivative of the slice
    have hstep1 : fderiv ℝ (fun q : ℝ × ℝ => H (v.1, q))
        = (preComp (ContinuousLinearMap.inr ℝ α (ℝ × ℝ)))
            ∘ (fun q : ℝ × ℝ => fderiv ℝ H (v.1, q)) := by
      funext q
      rw [fderiv_slice H v.1 q (hHdiff.differentiableAt)]
      exact (preComp_apply _ _).symm
    have hPhid : DifferentiableAt ℝ (⇑(preComp (ContinuousLinearMap.inr ℝ α (ℝ × ℝ))))
        (fderiv ℝ H (v.1, v.2)) :=
      (preComp (ContinuousLinearMap.inr ℝ α (ℝ × ℝ))).differentiableAt (x := fderiv ℝ H (v.1, v.2))
    have hcomp := fderiv_comp (𝕜 := ℝ) (x := v.2)
      (g := ⇑(preComp (ContinuousLinearMap.inr ℝ α (ℝ × ℝ)))) hPhid hΨd'
    rw [hstep1, hcomp, ContinuousLinearMap.fderiv]
    congr 1
    exact fderiv_slice (fderiv ℝ H) v.1 v.2 h1diff.differentiableAt
  -- and that expression is continuous in `v`
  refine Continuous.congr ?_ (fun v => (key v).symm)
  have hX : Continuous (fun v : α × (ℝ × ℝ) =>
      (fderiv ℝ (fderiv ℝ H) v).comp (ContinuousLinearMap.inr ℝ α (ℝ × ℝ))) := by
    have h : Continuous (fun v : α × (ℝ × ℝ) =>
        preComp (ContinuousLinearMap.inr ℝ α (ℝ × ℝ)) (fderiv ℝ (fderiv ℝ H) v)) :=
      (preComp (ContinuousLinearMap.inr ℝ α (ℝ × ℝ))).continuous.comp hD2
    exact h.congr (fun v => preComp_apply _ _)
  refine ((ContinuousLinearMap.compL ℝ (ℝ × ℝ) ((α × (ℝ × ℝ)) →L[ℝ] ℝ)
    ((ℝ × ℝ) →L[ℝ] ℝ)) (preComp (ContinuousLinearMap.inr ℝ α (ℝ × ℝ)))).continuous.comp hX
      |>.congr ?_
  intro v
  simp only [Function.comp_apply, ContinuousLinearMap.compL_apply]

end Work.Drive.Mono.Band

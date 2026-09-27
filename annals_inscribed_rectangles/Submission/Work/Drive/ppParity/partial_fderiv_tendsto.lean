import Mathlib

namespace Work.Drive.ppParity

/-- **Continuity of a partial derivative in the remaining variable.**
If `F : X × Y → Z` is smooth at `(x, y)`, then for `v` close to `x` the slice
`y' ↦ F (v, y')` is differentiable at `y`, and its derivative converges to that of the slice at
`x`.  (Only `C¹` is really used: the proof feeds `ContDiffAt.continuousAt_fderiv`, i.e. the
continuity of `p ↦ fderiv ℝ F p` at `(x, y)`, through the composite `v ↦ (v, y)` and the
precomposition with `ContinuousLinearMap.inr ℝ X Y`.) -/
theorem partial_fderiv_tendsto
    {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {F : X × Y → Z} {x : X} {y : Y}
    (hF : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (x, y)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v : X, ‖v - x‖ < δ →
      DifferentiableAt ℝ (fun y' : Y => F (v, y')) y ∧
      DifferentiableAt ℝ (fun y' : Y => F (x, y')) y ∧
      ‖fderiv ℝ (fun y' : Y => F (v, y')) y - fderiv ℝ (fun y' : Y => F (x, y')) y‖ < ε := by
  intro ε hε
  -- `F` is `C¹`, hence in particular differentiable on a neighbourhood of `(x, y)`.
  have hF1 : ContDiffAt ℝ (1 : WithTop ℕ∞) F (x, y) := hF.of_le (by simp)
  have hd : ∀ᶠ z : X × Y in nhds (x, y), DifferentiableAt ℝ F z := by
    filter_upwards [hF1.eventually (by simp)] with z hz
    exact hz.differentiableAt_one
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.eventually_nhds_iff.mp hd
  -- the derivative `fderiv ℝ F` is continuous at `(x, y)`, so its value along `v ↦ (v, y)` is.
  have hfd : ContinuousAt (fun v : X => fderiv ℝ F (v, y)) x := by
    have hg : ContinuousAt (fun p : X × Y => fderiv ℝ F p) (x, y) :=
      hF.continuousAt_fderiv (by simp)
    have hc : ContinuousAt (fun v : X => (v, y)) x :=
      continuousAt_id.prodMk (continuousAt_const : ContinuousAt (fun _ : X => y) x)
    exact hg.comp (f := fun v : X => (v, y)) hc
  -- ... and so is its composition with the fixed linear map `inr`, which is the slice's derivative.
  have hcont : ContinuousAt
      (fun v : X => (fderiv ℝ F (v, y)).comp (ContinuousLinearMap.inr ℝ X Y)) x := by
    have h2 := ((ContinuousLinearMap.compL ℝ Y (X × Y) Z).flip
      (ContinuousLinearMap.inr ℝ X Y)).continuous.continuousAt.comp hfd
    simpa [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
      Function.comp_def] using h2
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.continuousAt_iff.mp hcont ε hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, fun v hv => ?_⟩
  have hv1 : ‖v - x‖ < δ₁ := lt_of_lt_of_le hv (min_le_left _ _)
  have hv2 : ‖v - x‖ < δ₂ := lt_of_lt_of_le hv (min_le_right _ _)
  have hdv : DifferentiableAt ℝ F (v, y) := by
    refine hδ₂ ?_
    simpa [Prod.dist_eq, dist_eq_norm] using hv2
  have hdx : DifferentiableAt ℝ F (x, y) := by
    refine hδ₂ ?_
    simpa using hδ₂pos
  -- the chain rule computes the derivative of each slice and gives its differentiability
  have slicev : HasFDerivAt (fun y' : Y => F (v, y'))
      ((fderiv ℝ F (v, y)).comp (ContinuousLinearMap.inr ℝ X Y)) y := by
    have h := hdv.hasFDerivAt.comp y (hasFDerivAt_prodMk_right v y)
    simpa [Function.comp_def] using h
  have slicex : HasFDerivAt (fun y' : Y => F (x, y'))
      ((fderiv ℝ F (x, y)).comp (ContinuousLinearMap.inr ℝ X Y)) y := by
    have h := hdx.hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)
    simpa [Function.comp_def] using h
  refine ⟨slicev.differentiableAt, slicex.differentiableAt, ?_⟩
  rw [slicev.fderiv, slicex.fderiv]
  simpa [dist_eq_norm] using hδ₁ (by simpa [dist_eq_norm] using hv1)

end Work.Drive.ppParity

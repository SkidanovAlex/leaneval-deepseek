import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The `fderiv`/`mfderiv` transport at a chart which is the identity (site glue **G4**)

At a collar point `x` of the level set of the source construction the region chart `extChartAt x` is the
ambient identity (`Work.ThomBordism.sourceRegionMk_extChartAt_apply_of_phi_neg`) and the perturbed
level function `w` agrees with the raw field `vSrc` on the collar slab.  Consequently

* the manifold derivative of `w` at `x` *is* the ordinary derivative of `vSrc` at `x.1.1`
  (`Work.ThomBordism.mfderiv_eq_fderiv_of_eventuallyEq`) — the range inclusion **G3** of
  `LeadChapter/ASSEMBLY.md` reduces to `range (mfderiv w x) = range (fderiv vSrc x.1.1)`;
* the chart reading `u ↦ w ((extChartAt x).symm u)` has derivative `mfderiv w x`
  (`Work.ThomBordism.hasFDerivAt_chartSymm_of_mdifferentiableAt`) and hence derivative
  `fderiv vSrc x.1.1` (`Work.ThomBordism.hasFDerivAt_chartSymm_eq_fderiv`), which is the `hLv`
  hypothesis of S1 (`chapter_K1det`) and the derivative hypothesis of S3 (`chapter_tubeDet`);
* the same eventual equality transported backwards gives `HasFDerivAt (vSrc) (mfderiv w x) x.1.1`,
  which is the `Lv` that S3's conclusion quantifies over.

No `sorry`, no new axioms.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.ThomBordism

/-- **The manifold derivative of a function read in the chart at `x`.**  If `x` is an interior point
of the model's range then `mfderiv I 𝓘 w x` is the ordinary derivative at `(extChartAt I x) x` of the
chart reading `u ↦ w ((extChartAt I x).symm u)` (both are `E →L F'`). -/
theorem mfderiv_eq_fderiv_of_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {w : M → F'} {v : E → F'} {x : M}
    (hw : MDifferentiableAt I (𝓘(ℝ, F')) w x)
    (hint : (extChartAt I x) x ∈ interior (range I))
    (h : (fun u => w ((extChartAt I x).symm u)) =ᶠ[𝓝 ((extChartAt I x) x)] v) :
    mfderiv I (𝓘(ℝ, F')) w x = fderiv ℝ v ((extChartAt I x) x) := by
  have hwr : writtenInExtChartAt I (𝓘(ℝ, F')) x w
      = (fun u => w ((extChartAt I x).symm u)) := by
    ext u; simp only [writtenInExtChartAt, Function.comp_apply]; rfl
  have h1 : fderivWithin ℝ (writtenInExtChartAt I (𝓘(ℝ, F')) x w) (range I) ((extChartAt I x) x)
      = fderiv ℝ v ((extChartAt I x) x) := by
    rw [hwr, fderivWithin_of_mem_nhds (mem_interior_iff_mem_nhds.mp hint)]
    exact h.fderiv_eq
  rw [hw.mfderiv, h1]
  ext y
  rfl

/-- **The chart reading has the manifold derivative.** -/
theorem hasFDerivAt_chartSymm_of_mdifferentiableAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {w : M → F'} {x : M}
    (hw : MDifferentiableAt I (𝓘(ℝ, F')) w x)
    (hint : (extChartAt I x) x ∈ interior (range I)) :
    HasFDerivAt (fun u => w ((extChartAt I x).symm u)) (mfderiv I (𝓘(ℝ, F')) w x)
      ((extChartAt I x) x) := by
  have h2 : HasFDerivWithinAt (writtenInExtChartAt I (𝓘(ℝ, F')) x w)
      (mfderiv I (𝓘(ℝ, F')) w x) (range I) ((extChartAt I x) x) := hw.hasMFDerivAt.2
  rw [show writtenInExtChartAt I (𝓘(ℝ, F')) x w
      = (fun u => w ((extChartAt I x).symm u)) from by
    ext u; simp only [writtenInExtChartAt, Function.comp_apply]; rfl] at h2
  exact h2.hasFDerivAt (mem_interior_iff_mem_nhds.mp hint)

/-- **The chart reading has the derivative of the comparison function.** -/
theorem hasFDerivAt_chartSymm_eq_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {w : M → F'} {v : E → F'} {x : M}
    (hw : MDifferentiableAt I (𝓘(ℝ, F')) w x)
    (hint : (extChartAt I x) x ∈ interior (range I))
    (h : (fun u => w ((extChartAt I x).symm u)) =ᶠ[𝓝 ((extChartAt I x) x)] v) :
    HasFDerivAt (fun u => w ((extChartAt I x).symm u)) (fderiv ℝ v ((extChartAt I x) x))
      ((extChartAt I x) x) :=
  (hasFDerivAt_chartSymm_of_mdifferentiableAt I hw hint).congr_fderiv
    (mfderiv_eq_fderiv_of_eventuallyEq I hw hint h)

/-- **The comparison function has the manifold derivative** (the eventual equality transported
backwards). -/
theorem hasFDerivAt_of_chartSymm_eventuallyEq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {w : M → F'} {v : E → F'} {x : M}
    (hw : MDifferentiableAt I (𝓘(ℝ, F')) w x)
    (hint : (extChartAt I x) x ∈ interior (range I))
    (h : (fun u => w ((extChartAt I x).symm u)) =ᶠ[𝓝 ((extChartAt I x) x)] v) :
    HasFDerivAt v (mfderiv I (𝓘(ℝ, F')) w x) ((extChartAt I x) x) :=
  (hasFDerivAt_chartSymm_of_mdifferentiableAt I hw hint).congr_of_eventuallyEq h.symm

/-- **The range of the manifold derivative is the range of the comparison derivative.** -/
theorem range_mfderiv_eq_range_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {w : M → F'} {v : E → F'} {x : M}
    (hw : MDifferentiableAt I (𝓘(ℝ, F')) w x)
    (hint : (extChartAt I x) x ∈ interior (range I))
    (h : (fun u => w ((extChartAt I x).symm u)) =ᶠ[𝓝 ((extChartAt I x) x)] v) :
    Set.range (mfderiv I (𝓘(ℝ, F')) w x)
      = Set.range (fderiv ℝ v ((extChartAt I x) x)) :=
  congrArg (fun L : E →L[ℝ] F' => Set.range (L : E → F'))
    (mfderiv_eq_fderiv_of_eventuallyEq I hw hint h)

end Work.ThomBordism

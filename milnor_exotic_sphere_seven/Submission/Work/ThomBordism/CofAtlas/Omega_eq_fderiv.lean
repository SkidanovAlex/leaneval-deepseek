import Mathlib
import Submission.Work.ThomBordism.CofAtlas.Signs
import Submission.Work.ThomBordism.CofAtlas.Tdom_comp_Delta
import Submission.Work.PTGeometric.FDerivInChart

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The coframing `Ω` of a chart is the derivative of the level function in that chart

`Work.ThomBordism.CofAtlas.Omega_eq_fderiv`: for `D : Cof k n M` (a coframed level set in `M`),
`x` a point of the level set and `q` a point of the source of the chart at `x` lying over an
interior point of `M`,

`Ω_x(q) = fderiv ℝ (z ↦ ℓ (jx x) (D.v ((domExt x).symm z))) (domExt x q)`

i.e. the coframing of the level set at `q`, read in the normal-form coordinates of the chart at
`x`, is *by definition unfolding* the derivative of the level function `v` written in those
coordinates.

`Ω_x(q)` is defined (`Cof/Signs.lean`) as `ℓ (jx x) ∘ mfderiv v q ∘ Cx x q`, where `Cx x q` is
the derivative at `domExt x q` of the chart change `domChart x → ambChart q` (the coordinates in
which `mfderiv v q` is written).  The content of the statement is therefore the chain rule

`fderiv (v ∘ (domExt x)⁻¹) (domExt x q) = mfderiv v q ∘ fderiv (domChart x → ambChart q) (domExt x q)`

which is the statement that `mfderiv` may be read in *any* chart of the maximal atlas, not only in
the preferred chart of the source point.  The general form of that chain rule is
`hasFDerivAt_comp_extend_symm` below (a gap in Mathlib: `Work.PTGeometric.hasFDerivWithinAt_comp_extChartAt_symm`
proves the `fderivWithin` version in the preferred chart, with the outer chart removed).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter ModelWithCorners
open Work.PTGeometric

namespace Work.ThomBordism.CofAtlas

noncomputable section

/-! ## Reading `mfderiv` in an arbitrary chart of the maximal atlas -/

/-- **`mfderiv` read in an arbitrary chart of the maximal atlas.**  Let `f : M → E'` be
differentiable at `p`, let `e` be a chart of the maximal atlas around `p`, and let `e.extend I p`
be an interior point of the model.  Then the model-space function
`z ↦ f ((e.extend I).symm z)` has ordinary derivative

`mfderiv f p ∘ d(I.extendCoordChange e (chartAt H p)) (e.extend I p)`

at `(e.extend I) p`.  (The change of charts `I.extendCoordChange e (chartAt H p)` is the transition
from the coordinates of `e` to the preferred coordinates at `p`; it is differentiable at
`e.extend I p` because the latter is an interior point.) -/
theorem hasFDerivAt_comp_extend_symm
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {n : ℕ∞ω} [IsManifold I n M]
    {f : M → E'} {p : M} (hf : MDifferentiableAt I 𝓘(𝕜, E') f p)
    {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I n M) (hp : p ∈ e.source) (hn : n ≠ 0)
    (hz : (e.extend I) p ∈ interior (range I))
    (hz' : (extChartAt I p) p ∈ interior (range I)) :
    HasFDerivAt (fun z : E => f ((e.extend I).symm z))
      ((mfderiv I 𝓘(𝕜, E') f p).comp
        (fderiv 𝕜 (I.extendCoordChange e (chartAt H p)) ((e.extend I) p)) : E →L[𝕜] E')
      ((e.extend I) p) := by
  -- the chart change `domChart x → ambChart p` is differentiable at the image of `p`
  have hφ : HasFDerivAt (I.extendCoordChange e (chartAt H p))
      (fderiv 𝕜 (I.extendCoordChange e (chartAt H p)) ((e.extend I) p)) ((e.extend I) p) :=
    (tcD_differentiableAt I hn he (IsManifold.chart_mem_maximalAtlas p) hp
      (mem_chart_source H p) hz).hasFDerivAt
  -- `f` in the preferred chart at `p`: derivative `mfderiv f p`, within `range I`
  have hw : HasFDerivWithinAt (fun z : E => f ((extChartAt I p).symm z))
      (mfderiv I 𝓘(𝕜, E') f p) (range I) ((extChartAt I p) p) :=
    hasFDerivWithinAt_comp_extChartAt_symm hf
  have hg : HasFDerivAt (fun z : E => f ((extChartAt I p).symm z))
      ((mfderiv I 𝓘(𝕜, E') f p) : E →L[𝕜] E') ((extChartAt I p) p) :=
    hw.hasFDerivAt (mem_of_superset (isOpen_interior.mem_nhds hz') interior_subset)
  -- the chart change at the base point is the image of `p` in the preferred chart
  have hval : (I.extendCoordChange e (chartAt H p)) ((e.extend I) p) = (extChartAt I p) p :=
    tcD_apply_extend I e (chartAt H p) hp
  have hg' : HasFDerivAt (fun z : E => f ((extChartAt I p).symm z))
      ((mfderiv I 𝓘(𝕜, E') f p) : E →L[𝕜] E')
      ((I.extendCoordChange e (chartAt H p)) ((e.extend I) p)) := hval.symm ▸ hg
  have hcomp : HasFDerivAt
      (fun z : E => f ((extChartAt I p).symm ((I.extendCoordChange e (chartAt H p)) z)))
      (((mfderiv I 𝓘(𝕜, E') f p).comp
        (fderiv 𝕜 (I.extendCoordChange e (chartAt H p)) ((e.extend I) p))) : E →L[𝕜] E')
      ((e.extend I) p) := hg'.comp ((e.extend I) p) hφ
  -- the two functions agree near `(e.extend I) p`
  have hlt : ((e.extend I).symm ((e.extend I) p)) ∈ (chartAt H p).source := by
    rw [OpenPartialHomeomorph.extend_left_inv e hp]
    exact mem_chart_source H p
  have hcont : ContinuousAt ((e.extend I).symm : E → M) ((e.extend I) p) :=
    OpenPartialHomeomorph.continuousAt_extend_symm e hp
  have hmem : ((e.extend I).symm ⁻¹' (chartAt H p).source) ∈ 𝓝 ((e.extend I) p) :=
    hcont.preimage_mem_nhds ((chartAt H p).open_source.mem_nhds hlt)
  have hev : (fun z : E => f ((e.extend I).symm z))
      =ᶠ[𝓝 ((e.extend I) p)]
        (fun z : E => f ((extChartAt I p).symm ((I.extendCoordChange e (chartAt H p)) z))) := by
    filter_upwards [hmem] with z hzmem
    refine congrArg f ?_
    have hzmem' : e.symm (I.symm z) ∈ (chartAt H p).source := by
      simpa only [OpenPartialHomeomorph.extend_coe_symm, Function.comp_apply, Set.mem_preimage]
        using hzmem
    simp only [mfld_simps]
    exact (OpenPartialHomeomorph.left_inv _ hzmem').symm
  exact hcomp.congr_of_eventuallyEq hev

/-! ## The level function in the normal-form chart -/

variable {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanHalfSpace (NN k)) M]
  [IsManifold (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M]

/-- **The level function of the coframed data in the normal-form chart**: the derivative of
`z ↦ D.v ((domExt x).symm z)` at `domExt x q` is `mfderiv D.v q` transported by `Cx x q`, the
derivative of the change of coordinates from the normal-form chart at `x` to the ambient chart
at `q`. -/
theorem hasFDerivAt_comp_domExt (D : Cof k n M) (x : D.S.Pre) {q : D.S.Pre}
    (hx : q ∈ D.S.chartSource x)
    (hint : (q : M) ∈ (𝓡∂ (NN k)).interior M) :
    HasFDerivAt (fun z : ModN k => D.v ((D.domExt x).symm z))
      (((mfderiv (𝓡∂ (NN k)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) D.v (q : M)).comp (D.Cx x (q : M)))
        : ModN k →L[ℝ] EuclideanSpace ℝ (Fin n))
      (D.domExt x (q : M)) := by
  have hn : (((⊤ : ENat) : WithTop ENat) : ℕ∞ω) ≠ 0 := by simp
  have hdomx : D.domChart x ∈ IsManifold.maximalAtlas (𝓡∂ (NN k)) ((⊤ : ENat) : WithTop ENat) M :=
    Lvl.Setup.domChartAt_mem_maximalAtlas D.S x
  have hxsrc : (q : M) ∈ (D.domChart x).source := hx.1
  have hz : (D.domChart x).extend (𝓡∂ (NN k)) (q : M) ∈ interior (range (𝓡∂ (NN k))) :=
    tcD_mem_interior_range (𝓡∂ (NN k)) hn hdomx hxsrc hint
  have hf : MDifferentiableAt (𝓡∂ (NN k)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) D.v (q : M) :=
    (D.hvsm (q : M)).mdifferentiableAt hn
  exact hasFDerivAt_comp_extend_symm (𝕜 := ℝ) (I := 𝓡∂ (NN k))
    (n := ((⊤ : ENat) : WithTop ENat)) (f := D.v) (p := (q : M)) hf
    (e := D.domChart x) hdomx hxsrc hn hz hint

/-! ## The target -/

theorem Omega_eq_fderiv
    {k n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)) ((⊤ : ENat) : WithTop ENat) M]
    (D : Work.ThomBordism.CofAtlas.Cof k n M) (x : D.S.Pre) {q : D.S.Pre}
    (hx : q ∈ D.S.chartSource x)
    (hint : (q : M) ∈ (modelWithCornersEuclideanHalfSpace ((8 + k) + 1)).interior M) :
    D.Omega x (q : M)
      = fderiv ℝ (fun z : EuclideanSpace ℝ (Fin ((8 + k) + 1)) =>
          D.ℓ (D.jx x) (D.v ((D.domExt x).symm z))) (D.domExt x (q : M)) := by
  have hinner : HasFDerivAt (fun z : ModN k => D.v ((D.domExt x).symm z))
      (((mfderiv (𝓡∂ (NN k)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) D.v (q : M)).comp (D.Cx x (q : M)))
        : ModN k →L[ℝ] EuclideanSpace ℝ (Fin n)) (D.domExt x (q : M)) :=
    hasFDerivAt_comp_domExt D x hx hint
  have houter : HasFDerivAt (fun z : ModN k => D.ℓ (D.jx x) (D.v ((D.domExt x).symm z)))
      ((D.ℓ (D.jx x)).comp
        ((mfderiv (𝓡∂ (NN k)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) D.v (q : M)).comp
          (D.Cx x (q : M))))
      (D.domExt x (q : M)) :=
    (D.ℓ (D.jx x)).hasFDerivAt.comp (D.domExt x (q : M)) hinner
  rw [houter.fderiv]
  rfl

end

end Work.ThomBordism.CofAtlas

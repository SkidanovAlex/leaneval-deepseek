import Mathlib
import Submission.Work.Diff.EXT.ricPhiPartialDefs
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.T.mvfderiv_frameVector_real
import Submission.Work.Diff.GE.smooth_onframe_pairing
import Submission.Work.Diff.EXT.contDiffAt_chartMat_of_jointSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Koszul pairing of the chart frame is the scalar `1`-jet of the chart matrix

Fix a smooth metric `g` on `M`, a chart centre `x₀` and a chart coordinate `y` in the target of the
extended chart at `x₀`.  Write `σᵢ = frameVector x₀ · (bB i)` for the coordinate frame of the
chart, and
`chartMatFun g x₀ y i j = g.inner p (σᵢ) (σⱼ)` with `p = (extChartAt I x₀).symm y` for its matrix
in that frame, a function `E → MatE`.

The main result of this file is that the *geometric* Koszul pairing
`koszulPair g x₀ a b c 0 p = ½(∂_a g_{bc} + ∂_b g_{ca} − ∂_c g_{ab})` of the Levi-Civita
connection of `g` in the coordinate frame, whose three terms are manifold derivatives of metric
components along coordinate fields, agrees with the *purely scalar* expression

`sKz (dJet1 g x₀ y) a b c = ½(∂_a g_{bc} + ∂_b g_{ac} − ∂_c g_{ab})`

built from the first coordinate partial derivatives `dJet1 g x₀ y k = fderiv ℝ (chartMatFun g x₀) y (bB k)`
of the chart matrix.  This is the bridge that lets the chart Ricci matrix be read off from the
scalar `2`-jet of `chartMatFun`.

The proof has three ingredients, each a lemma below.

* `Work.Diff.EXT.kz_mvfderiv_metricComp_eq`: the manifold derivative of a metric component in a
  coordinate direction is the corresponding Fréchet derivative of `chartMatFun`, i.e.
  `mvfderiv I (fun z ↦ g.inner z (σᵢ z) (σⱼ z)) p (σₖ p) = (fderiv ℝ (chartMatFun g x₀) y (bB k)) i j`.
  This is `Work.Diff.T.mvfderiv_frameVector_real`, valid because the metric pairing of the
  coordinate frame is smooth (`Work.Diff.GE.smooth_onframe_pairing`), followed by the
  identification of the composed function with `chartMatFun`.
* `Work.Diff.EXT.kz_fderiv_chartMatFun_apply`: the matrix coefficients of `fderiv ℝ (chartMatFun g x₀) y`
  are the Fréchet derivatives of the matrix coefficients (`fderiv_apply`).
* `Work.Diff.EXT.kz_chartMatFun_swap`: `chartMatFun` is symmetric, so the matrix of its derivative
  is symmetric in the two matrix indices.
-/

namespace Work.Diff.EXT

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- The chart matrix `chartMatFun g x₀` of a smooth metric is `C^∞` at every chart coordinate `y`
in the target of the extended chart at `x₀`.  The proof pairs the coordinate frame vectors of the
chart (smooth at `(extChartAt I x₀).symm y`) against `g` and composes with the chart inverse. -/
theorem kz_contDiffAt_chartMatFun
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (chartMatFun (I := I) g x₀) y := by
  have hp : (extChartAt I x₀).symm y ∈ (chartAt H' x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    exact PartialEquiv.map_target (extChartAt I x₀) hy
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x₀).symm y :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x₀).contMDiffAt
      ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hy)
  have hframe : ∀ k : Fin (Module.finrank ℝ E),
      ContMDiffAt I I.tangent ∞
        (T% (fun z : M => Submission.Geodesic.frameVector (I := I) x₀ z (bB (E := E) k)))
        ((extChartAt I x₀).symm y) :=
    fun k => contMDiffAt_frameVector x₀ (bB (E := E) k) hp
  refine contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => ?_))
  have hΦ : ContMDiffAt I 𝓘(ℝ,ℝ) ∞
      (fun z : M => g.inner z
        (Submission.Geodesic.frameVector (I := I) x₀ z (bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ z (bB (E := E) j)))
      ((extChartAt I x₀).symm y) :=
    Work.Diff.GE.smooth_onframe_pairing g _ (hframe i) (hframe j)
  have hcomp : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ,ℝ) ∞
      (fun x : E => g.inner ((extChartAt I x₀).symm x)
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm x) (bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm x) (bB (E := E) j))) y :=
    hΦ.comp y hsymm
  have := contMDiffAt_iff_contDiffAt.mp hcomp
  simpa only [chartMatFun] using this

/-- The matrix coefficients of the Fréchet derivative of the chart matrix are the Fréchet
derivatives of the matrix coefficients. -/
theorem kz_fderiv_chartMatFun_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (k i j : Fin (Module.finrank ℝ E)) :
    (fderiv ℝ (chartMatFun (I := I) g x₀) y (bB (E := E) k)) i j
      = fderiv ℝ (fun x : E => chartMatFun (I := I) g x₀ x i j) y (bB (E := E) k) := by
  have hd : DifferentiableAt ℝ (chartMatFun (I := I) g x₀) y :=
    (kz_contDiffAt_chartMatFun g x₀ hy).differentiableAt (by simp)
  have h1 := fderiv_apply (𝕜 := ℝ) hd i
  have hd2 : DifferentiableAt ℝ (fun x : E => chartMatFun (I := I) g x₀ x i) y :=
    (differentiableAt_pi.mp hd) i
  have h2 := fderiv_apply (𝕜 := ℝ) hd2 j
  simp only [h2, h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]

/-- The chart matrix of a Riemannian metric is symmetric, hence so is the matrix of its Fréchet
derivative at every chart coordinate in the target of the chart. -/
theorem kz_chartMatFun_swap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (k i j : Fin (Module.finrank ℝ E)) :
    (fderiv ℝ (chartMatFun (I := I) g x₀) y (bB (E := E) k)) i j
      = (fderiv ℝ (chartMatFun (I := I) g x₀) y (bB (E := E) k)) j i := by
  have hfun : (fun x : E => chartMatFun (I := I) g x₀ x i j)
      = (fun x : E => chartMatFun (I := I) g x₀ x j i) := by
    funext z
    exact g.symm ((extChartAt I x₀).symm z) _ _
  rw [kz_fderiv_chartMatFun_apply g x₀ hy k i j,
      kz_fderiv_chartMatFun_apply g x₀ hy k j i,
      hfun]

/-- **The bridge between the manifold derivative of a metric component and the scalar `1`-jet of
the chart matrix.**  In the coordinate frame, the derivative of the metric component `g_{ij}` in
the coordinate direction `k` is the corresponding Fréchet derivative of `chartMatFun`. -/
theorem kz_mvfderiv_frameVector_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (i j k : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun z : M => g.inner z
        (Submission.Geodesic.frameVector (I := I) x₀ z (bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ z (bB (E := E) j)))
      ((extChartAt I x₀).symm y)
      (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm y) (bB (E := E) k))
      = (fderiv ℝ (chartMatFun (I := I) g x₀) y (bB (E := E) k)) i j := by
  set p : M := (extChartAt I x₀).symm y with hpdef
  have hp : p ∈ (chartAt H' x₀).source := by
    rw [hpdef, ← extChartAt_source (I := I) x₀]
    exact PartialEquiv.map_target (extChartAt I x₀) hy
  have hpy : (extChartAt I x₀) p = y := by
    rw [hpdef]
    exact PartialEquiv.right_inv (extChartAt I x₀) hy
  have hframe : ∀ m : Fin (Module.finrank ℝ E),
      ContMDiffAt I I.tangent ∞
        (T% (fun z : M => Submission.Geodesic.frameVector (I := I) x₀ z (bB (E := E) m))) p :=
    fun m => contMDiffAt_frameVector x₀ (bB (E := E) m) hp
  have hsm : ContMDiffAt I 𝓘(ℝ,ℝ) ∞
      (fun z : M => g.inner z
        (Submission.Geodesic.frameVector (I := I) x₀ z (bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ z (bB (E := E) j))) p :=
    Work.Diff.GE.smooth_onframe_pairing g p (hframe i) (hframe j)
  have hmd : MDifferentiableAt I 𝓘(ℝ,ℝ)
      (fun z : M => g.inner z
        (Submission.Geodesic.frameVector (I := I) x₀ z (bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ z (bB (E := E) j))) p :=
    hsm.mdifferentiableAt (by simp)
  have h1 := Work.Diff.T.mvfderiv_frameVector_real x₀ hp hmd (bB (E := E) k)
  rw [hpy] at h1
  rw [h1]
  have hfun : (fun x : E => g.inner ((extChartAt I x₀).symm x)
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm x) (bB (E := E) i))
        (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm x) (bB (E := E) j)))
      = (fun x : E => chartMatFun (I := I) g x₀ x i j) := rfl
  rw [hfun, kz_fderiv_chartMatFun_apply g x₀ hy k i j]

/-- The same bridge, written with the coordinate-frame shorthand `cFrame` of
`Work.Diff.GE.norms_defs` (which is definitionally the coordinate frame vector). -/
theorem kz_mvfderiv_metricComp_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (i j k : Fin (Module.finrank ℝ E)) :
    mvfderiv I (fun z : M => g.inner z
        (Work.Diff.GE.cFrame (I := I) x₀ i z)
        (Work.Diff.GE.cFrame (I := I) x₀ j z))
      ((extChartAt I x₀).symm y)
      (Work.Diff.GE.cFrame (I := I) x₀ k ((extChartAt I x₀).symm y))
      = (fderiv ℝ (chartMatFun (I := I) g x₀) y (bB (E := E) k)) i j := by
  have h := kz_mvfderiv_frameVector_pairing (I := I) (M := M) g x₀ hy i j k
  simpa only [Work.Diff.GE.cFrame_apply] using h

theorem koszulPair_eq_sKz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (g : Submission.Diff.SMet I M) (x₀ : M) {y : E} (hy : y ∈ (extChartAt I x₀).target)
    (a b c : Fin (Module.finrank ℝ E)) :
    Work.Diff.GE.koszulPair (I := I) (fun _ : ℝ => g) x₀ a b c 0 ((extChartAt I x₀).symm y)
      = Work.Diff.EXT.sKz (Work.Diff.EXT.dJet1 g x₀ y) a b c := by
  simp only [Work.Diff.GE.koszulPair, sKz, dJet1]
  rw [kz_mvfderiv_metricComp_eq g x₀ hy b c a, kz_mvfderiv_metricComp_eq g x₀ hy c a b,
    kz_mvfderiv_metricComp_eq g x₀ hy a b c, kz_chartMatFun_swap g x₀ hy b a c]

end Work.Diff.EXT

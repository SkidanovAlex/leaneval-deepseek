import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.B3.BPairSmooth
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.Man.exists_sMet_of_chartData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the localised components of a section with smooth chart matrix

`Work.Diff.STE.B3Data.R i h a b` is the periodisable localised component
`ψ i · √(dens i) · mat i h a b` of a section `h : Bil I M = Π x, TₓM →L TₓM →L ℝ`, where the
matrix `mat i h a b` is taken in the `g₀`-orthonormal frame `D.e i a` of the Layer B3 data.

The Fourier estimate of Layer B3 (`BNorm_J_le`, …) needs `∀ i a b, ContDiff ℝ ⊤ (R i h a b)` as its
regularity hypothesis, while the users of Layer D only provide `Work.Diff.STE.D.ChartData h` — the
smoothness of the matrix of `h` in the *coordinate* frame of every chart.  This file bridges the
two, via the general lemma `Work.Diff.STE.Man.section_contMDiffAt_of_frameMat` (frame data of a
section ⟹ smoothness of the section of the bundle of bilinear forms) applied to the frame data
obtained from `ChartData`, and then `ContMDiffWithinAt.clm_bundle_apply₂` against the globally
smooth frame fields `D.e i a`.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE.B3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]

/-- **Chart data gives smoothness of the frame matrix at the chart centre.**  This is the first half
of the `contMDiff` field of `Work.Diff.STE.D.smetOf`
(`Work.Diff.STE.Man.exists_sMet_of_chartData`), recorded in the form needed here: neither symmetry
nor positivity of `h` is involved. -/
lemma frameMat_contMDiffAt_of_chartData
    {h : Work.Diff.STE.Bil (I := I) (M := M)}
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (x₀ : M) :
    ContMDiffAt I (𝓘(ℝ, Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun x : M => Work.Diff.EXT.frameMat (I := I) x₀ x (h x)) x₀ := by
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : E => Work.Diff.EXT.frameMat (I := I) x₀ ((extChartAt I x₀).symm y)
        (h ((extChartAt I x₀).symm y))) ((extChartAt I x₀) x₀) :=
    (hh x₀).contDiffAt (extChartAt_target_mem_nhds x₀)
  have h2 : ContMDiffAt (𝓘(ℝ, E)) (𝓘(ℝ, Work.Diff.EXT.MatE (E := E))) (⊤ : ℕ∞)
      (fun y : E => Work.Diff.EXT.frameMat (I := I) x₀ ((extChartAt I x₀).symm y)
        (h ((extChartAt I x₀).symm y))) ((extChartAt I x₀) x₀) := h1.contMDiffAt
  have h3 := h2.comp x₀ (contMDiffAt_extChartAt (I := I) (x := x₀))
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [IsOpen.mem_nhds (chartAt H x₀).open_source (mem_chart_source H x₀)]
    with x hx
  have hx' : x ∈ (extChartAt I x₀).source := by rwa [extChartAt_source]
  simp only [Function.comp_apply]
  rw [show (extChartAt I x₀).symm ((extChartAt I x₀) x) = x
    from (extChartAt I x₀).left_inv hx']

/-- **Chart data gives smoothness of the section of the bundle of bilinear forms.**  The frame data
`frameMat_contMDiffAt_of_chartData` is turned into the smoothness of `x ↦ ⟨x, h x⟩` by
`Work.Diff.STE.Man.section_contMDiffAt_of_frameMat`. -/
lemma section_contMDiffAt_of_chartData
    {h : Work.Diff.STE.Bil (I := I) (M := M)}
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (x₀ : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun x : M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (h x)) x₀ :=
  Work.Diff.STE.Man.section_contMDiffAt_of_frameMat (I := I) (x₀ := x₀) (γ := h)
    (frameMat_contMDiffAt_of_chartData hh x₀)

/-- **The chart components of a section are smooth whenever its chart matrix in the coordinate
frame is smooth.**

`Work.Diff.STE.D.ChartData h` is the smoothness hypothesis of the section
`h : Bil I M = Π x, TₓM →L[ℝ] TₓM →L[ℝ] ℝ` used by Layer D (`D.smetOf`, `D.deTurckSec`): it says
that for every chart centre `x₀` the matrix of `h x` in the coordinate frame
`Submission.Geodesic.frameVector x₀ x (Work.Diff.EXT.bB i)` is `C^∞` on the chart target as a
function of the chart coordinate.

Layer B3's components `D.R i h a b = D.psi i z · √(D.dens i z) · D.mat i h a b z` are the chart
matrix of `h` in the *other* frame `D.e i a` (the `g₀`-orthonormal frame of `B3Data`), localised by
the cut-off.  This statement upgrades `ChartData` to smoothness of those components, so that the
Fourier estimate `Work.Diff.STE.B3.BNorm_J_le*` — which has
`∀ i a b, ContDiff ℝ ⊤ (D.R i h a b)` as its regularity hypothesis — applies to sections given only
by `ChartData`.

Route:

* `Work.Diff.STE.B3Data.R_contDiff` (`B3/CompSmooth.lean`) already reduces the claim to
  `D.DensGood i` and `ContDiffOn ℝ ⊤ (D.matChart i h a b) (extChartAt I (D.x₀ i)).target`;
  the first is `Work.Diff.STE.B3.densGood D i` (proved), so only the second is left.
* From `hh : ChartData h`, as in `Work.Diff.STE.D.smetOf` / `Man.exists_sMet_of_chartData`
  (the block computing `hframe`), get for every `x₀` the smoothness of
  `x ↦ Work.Diff.EXT.frameMat x₀ x (h x)` at `x₀`, and then, with
  `Work.Diff.STE.Man.section_contMDiffAt_of_frameMat`, that the section
  `x ↦ (⟨x, h x⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ) (E := fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))`
  is `ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ⊤` at every `x₀` (no positivity is needed,
  unlike in `smetOf`).
* `D.hesm i a : CMDiff ∞ (T% (D.e i a))`, i.e. `Work.Diff.EXT.SmoothFieldAt I M (D.e i a) x` for
  every `x`, and `h` is `CLM`-valued at each point (`Bil` is
  `Π x, TₓM →L[ℝ] TₓM →L[ℝ] ℝ`), so `ContMDiffWithinAt.clm_bundle_apply₂` (as used in
  `Work.Diff.STE.B3.contMDiffAt_metric_pairing'`) gives
  `ContMDiffAt I 𝓘(ℝ,ℝ) ⊤ (fun x => h x (D.e i a x) (D.e i b x)) x`.
* Compose with `(extChartAt I (D.x₀ i)).symm` (`contMDiffOn_extChartAt_symm`, whose domain is the
  open target) to obtain `ContDiffOn ℝ ⊤ (D.matChart i h a b) (extChartAt I (D.x₀ i)).target`
  — `D.matChart i h a b y` is by definition `h ((extChartAt I x₀).symm y) (D.e i a (")) (D.e i b ("))`.

Intended full name: `Work.Diff.STE.B3.R_contDiff_of_chartData` (namespace `Work.Diff.STE.B3`). -/
theorem R_contDiff_of_chartData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) :
    ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b) := by
  intro i a b
  -- the section `h` is smooth as a section of the bundle of bilinear forms
  have hsec : ∀ x : M, ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun x : M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (h x)) x :=
    fun x => section_contMDiffAt_of_chartData (I := I) (M := M) hh x
  -- ... hence the matrix of `h` in the globally smooth frame `D.e i` is smooth everywhere
  have hmat : ContMDiffOn I 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun x : M => h x (D.e i a x) (D.e i b x)) univ := by
    intro x _
    have hψ := (hsec x).contMDiffWithinAt (s := univ)
    have hv : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞) (T% (D.e i a)) univ x :=
      (D.hesm i a).contMDiffAt.contMDiffWithinAt
    have hw : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞) (T% (D.e i b)) univ x :=
      (D.hesm i b).contMDiffAt.contMDiffWithinAt
    have hres := hψ.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hv hw
    simp only [contMDiffWithinAt_totalSpace] at hres
    exact hres.2
  -- read that matrix in the chart coordinate of the chart at `D.x₀ i`
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun y : E => h ((extChartAt I (D.x₀ i)).symm y)
        (D.e i a ((extChartAt I (D.x₀ i)).symm y))
        (D.e i b ((extChartAt I (D.x₀ i)).symm y))) (extChartAt I (D.x₀ i)).target :=
    hmat.comp (contMDiffOn_extChartAt_symm (I := I) (x := D.x₀ i) (n := (⊤ : ℕ∞)))
      (fun y _ => mem_univ _)
  have hsm : ContDiffOn ℝ (⊤ : ℕ∞) (D.matChart i h a b) (extChartAt I (D.x₀ i)).target :=
    hcomp.contDiffOn
  exact D.R_contDiff i h a b (Work.Diff.STE.B3.densGood (I := I) (M := M) D i) hsm

end Work.Diff.STE.B3

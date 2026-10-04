import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.EXT.ricCore
import Submission.Work.Diff.EXT.contMDiffAt_metric_pairing
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contDiffOn_chartSpray

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: smoothness of the chart-matrix coefficients, without boundary or Hausdorff hypotheses

`Work.Diff.EXT.contMDiffAt_metric_coeff` states that the metric coefficients in the coordinate frame
of a chart are smooth at every point of that chart, but its statement carries the section
hypotheses `[I.Boundaryless] [T2Space M]` of its file (and so does
`Work.Diff.EXT.smoothFieldAt_cvec`).  The B3 adjunction `BPair_Rstar` has no such hypotheses, so
this file records `T2`- and boundary-free versions, by copying the proofs verbatim.
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
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M]

/-- The constant family of a smooth metric is jointly smooth (without boundary hypotheses). -/
lemma jointSmooth_const' (g : Submission.Diff.SMet I M) :
    Submission.Diff.JointSmooth (fun _ : ℝ => g) Set.univ := by
  have h : ContMDiff (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      ((fun b : M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) b (g.inner b)) ∘
        (Prod.snd : ℝ × M → M)) :=
    g.contMDiff.comp contMDiff_snd
  simpa only [Submission.Diff.JointSmooth, Set.univ_prod_univ, Function.comp_def] using
    h.contMDiffOn

/-- The coordinate-frame vector field of the chart at `x₀` is smooth at every point of the chart
(no Hausdorff assumption). -/
lemma smoothFieldAt_frameVector' (x₀ : M) (v : E) {p : M}
    (hp : p ∈ (chartAt H x₀).source) :
    Work.Diff.EXT.SmoothFieldAt I M
      (fun q : M => Submission.Geodesic.frameVector (I := I) x₀ q v) p :=
  (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contMDiffOn_trivializationAt_symmL_section
    (I := I) x₀ v).contMDiffAt ((chartAt H x₀).open_source.mem_nhds hp)

/-- **Joint smoothness of a metric pairing along a jointly smooth family** (no Hausdorff
assumption). -/
theorem contMDiffAt_metric_pairing'
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) {x : M}
    {Y Z : Π y : M, TangentSpace I y}
    (hY : Work.Diff.EXT.SmoothFieldAt I M Y x)
    (hZ : Work.Diff.EXT.SmoothFieldAt I M Z x) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (G p.1).inner p.2 (Y p.2) (Z p.2)) (t₀, x) := by
  have hmem : J ×ˢ (univ : Set M) ∈ 𝓝 (t₀, x) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (hJ.mem_nhds ht₀) Filter.univ_mem
  have hψ : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun m : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (Prod.snd m)
        ((G m.1).inner (Prod.snd m))) (t₀, x) := hG.contMDiffAt hmem
  have hYc : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E)) ∞
      ((T% Y) ∘ (Prod.snd : ℝ × M → M)) (t₀, x) :=
    hY.comp (t₀, x) contMDiffAt_snd
  have hZc : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E)) ∞
      ((T% Z) ∘ (Prod.snd : ℝ × M → M)) (t₀, x) :=
    hZ.comp (t₀, x) contMDiffAt_snd
  have hmain : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun m : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (Prod.snd m)
        ((G m.1).inner (Prod.snd m) (Y (Prod.snd m)) (Z (Prod.snd m))))
      univ (t₀, x) :=
    ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x)
      (E₃ := Bundle.Trivial M ℝ) (b := fun m : ℝ × M => Prod.snd m)
      (v := fun m : ℝ × M => Y (Prod.snd m)) (w := fun m : ℝ × M => Z (Prod.snd m))
      (ψ := fun m : ℝ × M => (G m.1).inner (Prod.snd m)) (s := univ) (x := (t₀, x))
      hψ hYc hZc
  simp only [contMDiffWithinAt_totalSpace] at hmain
  exact hmain.2

/-- **Smoothness of the metric coefficients in the coordinate frame of a chart** (no Hausdorff or
boundary assumptions). -/
theorem contMDiffAt_gmat_coeff' (g : Submission.Diff.SMet I M) (x₀ : M) {p : M}
    (hp : p ∈ (chartAt H x₀).source) (a b : Fin (Module.finrank ℝ E)) :
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat)
      (fun q : M => g.inner q
        (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E a))
        (Submission.Geodesic.frameVector (I := I) x₀ q (Module.finBasis ℝ E b))) p := by
  have hres := contMDiffAt_metric_pairing' (I := I) (G := fun _ : ℝ => g)
    (J := Set.univ) isOpen_univ (jointSmooth_const' g) (Set.mem_univ (0 : ℝ))
    (smoothFieldAt_frameVector' (I := I) x₀ (Module.finBasis ℝ E a) hp)
    (smoothFieldAt_frameVector' (I := I) x₀ (Module.finBasis ℝ E b) hp)
  have hc : ContMDiffAt I (𝓘(ℝ, ℝ).prod I) ((⊤ : ENat) : WithTop ENat)
      (fun q : M => ((0 : ℝ), q)) p :=
    (contMDiffAt_const : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) _
      (fun _ : M => (0 : ℝ)) p).prodMk contMDiffAt_id
  simpa only [Function.comp_def] using hres.comp p hc

end Work.Diff.STE.B3

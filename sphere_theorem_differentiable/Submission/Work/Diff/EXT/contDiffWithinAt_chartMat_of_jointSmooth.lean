import Mathlib
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.EXT.contDiffAt_chartMat_of_jointSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the chart matrix of a jointly smooth family of metrics, within a time set

`Work.Diff.EXT.chartMat G x₀ t y` is the matrix of the metric `G t` in the coordinate frame of the
chart at `x₀`, evaluated at the chart coordinate `y`.  The companion file
`contDiffAt_chartMat_of_jointSmooth.lean` proves that this is `C^∞` at `(t₀, y)` whenever `J` is
**open** and `G` is jointly smooth on `J × M`.

Here we prove the boundary version needed for the restart/splice step of the continuation theorem:
if `G` is jointly smooth on an *arbitrary* time set `J` (for the continuation theorem,
`J = [0, T)`, so the smoothness in time is one-sided at `t = 0`), then `(t, y) ↦ chartMat G x₀ t y`
is `C^∞` **within** the set `{p | p.1 ∈ J ∧ p.2 ∈ (extChartAt I x₀).target}` at the point
`(t₀, (extChartAt I x₀) x₀)`.  Concretely, the chart matrix restricted to that set agrees near the
point with a function that is `C^∞` (in the ordinary two-sided sense) at the point.

The proof is the same as in the open case, with every `ContMDiffAt` replaced by its
`ContMDiffWithinAt` analogue relative to the set `J ×ˢ univ` (or `J ×ˢ target` in coordinates).

The general form (arbitrary chart coordinate `y` in the target, not just the centre of the chart) is
recorded as `contDiffWithinAt_chartMat_of_jointSmooth_gen` and the requested statement is the
special case `y = (extChartAt I x₀) x₀`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]

/-- **Smoothness of the chart matrix within a time set (general point).**  If the family of metrics
`G` is jointly smooth on `J × M`, then in the chart at `x₀` the chart matrix is `C^∞` within
`J ×ˢ (extChartAt I x₀).target` at every point `(t₀, y)` with `t₀ ∈ J` and `y` in the target of the
extended chart.  No openness of `J` is needed: the smoothness in the time variable is one-sided at
the endpoints of `J`, exactly as in `JointSmooth`. -/
theorem contDiffWithinAt_chartMat_of_jointSmooth_gen
    [I.Boundaryless]
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ}
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2)
      (J ×ˢ (extChartAt I x₀).target) (t₀, y) := by
  -- the section of bilinear forms is smooth within `J ×ˢ univ`
  have hG' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((G p.1).inner p.2)) (J ×ˢ univ) := hG
  -- notation: `x` is the point of `M` of which `y` is the chart coordinate
  set x : M := (extChartAt I x₀).symm y with hxdef
  have hx : x ∈ (chartAt H' x₀).source := by
    rw [← extChartAt_source (I := I) x₀]
    exact PartialEquiv.map_target (extChartAt I x₀) hy
  have hxy : (extChartAt I x₀) x = y := PartialEquiv.right_inv (extChartAt I x₀) hy
  -- the coordinate frame vectors are smooth at `x`
  have hframe : ∀ k : Fin (Module.finrank ℝ E),
      CMDiffAt ∞ (T% (fun y : M => Submission.Geodesic.frameVector (I := I) x₀ y (bB k))) x :=
    fun k => contMDiffAt_frameVector x₀ (bB k) hx
  -- localised pairing of a jointly smooth family of bilinear forms with two smooth sections,
  -- within the time set `J`
  have pairing : ∀ (Y Z : Π y : M, TangentSpace I y),
      CMDiffAt ∞ (T% Y) x → CMDiffAt ∞ (T% Z) x →
      ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => (G p.1).inner p.2 (Y p.2) (Z p.2)) (J ×ˢ univ) (t₀, x) := by
    intro Y Z hY hZ
    have hψ : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun m : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (Prod.snd m)
          ((G m.1).inner (Prod.snd m))) (J ×ˢ univ) (t₀, x) :=
      hG' (t₀, x) ⟨ht₀, mem_univ x⟩
    have hYc : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E)) ∞
        ((T% Y) ∘ (Prod.snd : ℝ × M → M)) (J ×ˢ univ) (t₀, x) :=
      ((hY.comp (t₀, x) contMDiffAt_snd)).contMDiffWithinAt
    have hZc : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E)) ∞
        ((T% Z) ∘ (Prod.snd : ℝ × M → M)) (J ×ˢ univ) (t₀, x) :=
      ((hZ.comp (t₀, x) contMDiffAt_snd)).contMDiffWithinAt
    have hmain : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (Prod.snd m)
          ((G m.1).inner (Prod.snd m) (Y (Prod.snd m)) (Z (Prod.snd m))))
        (J ×ˢ univ) (t₀, x) :=
      ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x)
        (E₃ := Bundle.Trivial M ℝ) (b := fun m : ℝ × M => Prod.snd m)
        (v := fun m : ℝ × M => Y (Prod.snd m)) (w := fun m : ℝ × M => Z (Prod.snd m))
        (ψ := fun m : ℝ × M => (G m.1).inner (Prod.snd m)) (s := J ×ˢ univ) (x := (t₀, x))
        hψ hYc hZc
    simp only [contMDiffWithinAt_totalSpace] at hmain
    exact hmain.2
  -- smoothness of the chart inverse, and hence of `(t, y) ↦ (t, (extChartAt I x₀).symm y)`
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x₀).symm y :=
    (contMDiffOn_extChartAt_symm (I := I) (n := ∞) x₀).contMDiffAt
      ((isOpen_extChartAt_target (I := I) x₀).mem_nhds hy)
  have hκ : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) ((𝓘(ℝ, ℝ)).prod I) ∞
      (fun p : ℝ × E => (p.1, (extChartAt I x₀).symm p.2))
      (J ×ˢ (extChartAt I x₀).target) (t₀, y) :=
    (contMDiffAt_fst.prodMk (hsymm.comp (t₀, y) contMDiffAt_snd)).contMDiffWithinAt
  have hmap : MapsTo (fun p : ℝ × E => (p.1, (extChartAt I x₀).symm p.2))
      (J ×ˢ (extChartAt I x₀).target) (J ×ˢ (univ : Set M)) :=
    fun p hp => ⟨hp.1, mem_univ _⟩
  -- componentwise smoothness of the chart matrix
  have hcompij : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiffWithinAt ℝ ∞ (fun p : ℝ × E => chartMat G x₀ p.1 p.2 i j)
        (J ×ˢ (extChartAt I x₀).target) (t₀, y) := by
    intro i j
    have hΛij : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => (G p.1).inner p.2
          (Submission.Geodesic.frameVector (I := I) x₀ p.2 (bB i))
          (Submission.Geodesic.frameVector (I := I) x₀ p.2 (bB j))) (J ×ˢ univ) (t₀, x) :=
      pairing _ _ (hframe i) (hframe j)
    have hcomp : ContMDiffWithinAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => (G p.1).inner ((extChartAt I x₀).symm p.2)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm p.2) (bB i))
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm p.2) (bB j)))
        (J ×ˢ (extChartAt I x₀).target) (t₀, y) :=
      hΛij.comp_of_eq hκ hmap (by
        show ((t₀, (extChartAt I x₀).symm y) : ℝ × M) = (t₀, x)
        rw [hxdef])
    have h' : ContMDiffWithinAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => (G p.1).inner ((extChartAt I x₀).symm p.2)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm p.2) (bB i))
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm p.2) (bB j)))
        (J ×ˢ (extChartAt I x₀).target) (t₀, y) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact hcomp
    have hcont : ContDiffWithinAt ℝ ∞
        (fun p : ℝ × E => (G p.1).inner ((extChartAt I x₀).symm p.2)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm p.2) (bB i))
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm p.2) (bB j)))
        (J ×ˢ (extChartAt I x₀).target) (t₀, y) :=
      contMDiffWithinAt_iff_contDiffWithinAt.mp h'
    simpa only [chartMat, chartMatFun] using hcont
  -- assemble the matrix components
  refine contDiffWithinAt_pi.mpr (fun i => contDiffWithinAt_pi.mpr (fun j => ?_))
  exact hcompij i j

/-- **Smoothness of the chart matrix within a time set, at the centre of the chart.**  This is
`contDiffWithinAt_chartMat_of_jointSmooth_gen` at the point `y = (extChartAt I x₀) x₀` of the
target of the chart at `x₀` (the chart coordinate of the chart centre). -/
theorem contDiffWithinAt_chartMat_of_jointSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless]
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hG : Submission.Diff.JointSmooth G J)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x₀ : M) :
    ContDiffWithinAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2)
      {p : ℝ × E | p.1 ∈ J ∧ p.2 ∈ (extChartAt I x₀).target} (t₀, (extChartAt I x₀) x₀) := by
  have hy : (extChartAt I x₀) x₀ ∈ (extChartAt I x₀).target :=
    PartialEquiv.map_source (extChartAt I x₀) (mem_extChartAt_source (I := I) x₀)
  exact contDiffWithinAt_chartMat_of_jointSmooth_gen hG ht₀ x₀ hy

end Work.Diff.EXT

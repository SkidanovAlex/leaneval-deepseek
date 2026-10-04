import Mathlib
import Submission.Work.Diff.EXT.splice_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Smoothness of the chart matrix of a jointly smooth family of metrics

`Work.Diff.EXT.chartMat G x₀ t y` is the matrix of the metric `G t` in the coordinate frame of
the chart at `x₀`, evaluated at the chart coordinate `y`.  This file proves that it is `C^∞` in
`(t, y)` at `(t₀, (extChartAt I x₀) x₀)` as soon as `G` is jointly smooth in `(t, x)` on a
neighbourhood of the time `t₀`.

The proof has three steps.

* `contMDiffAt_frameVector`: the coordinate frame vector `y ↦ frameVector x₀ y v` is a smooth
  section of the tangent bundle at every point of the chart at `x₀`.  (The seeded library has this
  as `Submission.Geodesic.contMDiffAt_frameSection`, but that statement carries the instance
  metric and `T2Space M` as hypotheses; here the statement is metric-free, which is what working
  with an explicit family `G : ℝ → SMet I M` requires.)
* the *localised pairing*: for sections `Y`, `Z` of the tangent bundle that are smooth at a point
  `x`, the function `(t, x) ↦ (G t).inner x (Y x) (Z x)` is `C^∞` at `(t₀, x)`.
* composing with the chart inverse `(t, y) ↦ (t, (extChartAt I x₀).symm y)` and applying the chart
  differential `contDiffAt_pi` component by component.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}

/-- The section of the tangent bundle with constant coordinates `v` in the chart at `x₀` is smooth
at every point of that chart.  Stated without the instance Riemannian metric, so that it applies to
explicit metric families. -/
lemma contMDiffAt_frameVector {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]
    [IsManifold I (⊤ : ℕ∞) M] (x₀ : M) (v : E) {x : M} (hx : x ∈ (chartAt H' x₀).source) :
    CMDiffAt ∞ (T% (fun y : M => Submission.Geodesic.frameVector (I := I) x₀ y v)) x := by
  rw [Trivialization.contMDiffAt_section_iff (trivializationAt E (TangentSpace I) x₀)
    (by simpa using hx)]
  refine (contMDiffAt_const (c := v)).congr_of_eventuallyEq ?_
  filter_upwards [(trivializationAt E (TangentSpace I) x₀).open_baseSet.mem_nhds
    (by simpa using hx)] with y hy
  rw [show Submission.Geodesic.frameVector (I := I) x₀ y v
      = (trivializationAt E (TangentSpace I) x₀).symmL ℝ y v from rfl]
  rw [Trivialization.symmL_apply (e := trivializationAt E (TangentSpace I) x₀) (R := ℝ) hy v]
  exact congrArg Prod.snd ((trivializationAt E (TangentSpace I) x₀).apply_mk_symm hy v)

theorem contDiffAt_chartMat_of_jointSmooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless]
    {G : ℝ → Submission.Diff.SMet I M} {J : Set ℝ} (hJ : IsOpen J)
    (hG : Submission.Diff.JointSmooth G J) {t₀ : ℝ} (ht₀ : t₀ ∈ J) (x₀ : M) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun p : ℝ × E => Work.Diff.EXT.chartMat G x₀ p.1 p.2)
      (t₀, (extChartAt I x₀) x₀) := by
  -- `G` as a smooth section of the bilinear-form bundle, and the neighbourhood of `(t₀, x₀)`
  have hG' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((G p.1).inner p.2)) (J ×ˢ univ) := hG
  have hmem : J ×ˢ (univ : Set M) ∈ 𝓝 (t₀, x₀) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod (hJ.mem_nhds ht₀) Filter.univ_mem
  -- the coordinate frame vectors are smooth at `x₀`
  have hframe : ∀ k : Fin (Module.finrank ℝ E),
      CMDiffAt ∞ (T% (fun y : M => Submission.Geodesic.frameVector (I := I) x₀ y (bB k))) x₀ :=
    fun k => contMDiffAt_frameVector x₀ (bB k) (mem_chart_source H' x₀)
  -- localised pairing of a jointly smooth family of bilinear forms with two smooth sections
  have pairing : ∀ (Y Z : Π x : M, TangentSpace I x),
      CMDiffAt ∞ (T% Y) x₀ → CMDiffAt ∞ (T% Z) x₀ →
      ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => (G p.1).inner p.2 (Y p.2) (Z p.2)) (t₀, x₀) := by
    intro Y Z hY hZ
    have hψ : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun m : ℝ × M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (Prod.snd m)
          ((G m.1).inner (Prod.snd m))) (t₀, x₀) := hG'.contMDiffAt hmem
    have hYc : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E)) ∞
        ((T% Y) ∘ (Prod.snd : ℝ × M → M)) (t₀, x₀) :=
      hY.comp (t₀, x₀) contMDiffAt_snd
    have hZc : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) (I.prod 𝓘(ℝ, E)) ∞
        ((T% Z) ∘ (Prod.snd : ℝ × M → M)) (t₀, x₀) :=
      hZ.comp (t₀, x₀) contMDiffAt_snd
    have hmain : ContMDiffWithinAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : ℝ × M => TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) (Prod.snd m)
          ((G m.1).inner (Prod.snd m) (Y (Prod.snd m)) (Z (Prod.snd m))))
        univ (t₀, x₀) :=
      ContMDiffWithinAt.clm_bundle_apply₂ (𝕜 := ℝ) (B := M) (F₁ := E) (F₂ := E) (F₃ := ℝ)
        (E₁ := fun x : M => TangentSpace I x) (E₂ := fun x : M => TangentSpace I x)
        (E₃ := Bundle.Trivial M ℝ) (b := fun m : ℝ × M => Prod.snd m)
        (v := fun m : ℝ × M => Y (Prod.snd m)) (w := fun m : ℝ × M => Z (Prod.snd m))
        (ψ := fun m : ℝ × M => (G m.1).inner (Prod.snd m)) (s := univ) (x := (t₀, x₀))
        hψ hYc hZc
    simp only [contMDiffWithinAt_totalSpace] at hmain
    exact hmain.2
  -- smoothness of the chart inverse, and hence of `(t, y) ↦ (t, (extChartAt I x₀).symm y)`
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x₀).symm ((extChartAt I x₀) x₀) := by
    have h := contMDiffWithinAt_extChartAt_symm_range_self (I := I) (x := x₀) (n := ∞)
    rw [ModelWithCorners.Boundaryless.range_eq_univ, contMDiffWithinAt_univ] at h
    exact h
  have hleft : (extChartAt I x₀).symm ((extChartAt I x₀) x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source x₀)
  have hκ : ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) ((𝓘(ℝ, ℝ)).prod I) ∞
      (fun p : ℝ × E => (p.1, (extChartAt I x₀).symm p.2)) (t₀, (extChartAt I x₀) x₀) :=
    contMDiffAt_fst.prodMk
      (hsymm.comp (t₀, (extChartAt I x₀) x₀) contMDiffAt_snd)
  -- componentwise smoothness of the chart matrix
  have hcompij : ∀ i j : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ ∞ (fun p : ℝ × E => chartMat G x₀ p.1 p.2 i j)
        (t₀, (extChartAt I x₀) x₀) := by
    intro i j
    have hΛij : ContMDiffAt ((𝓘(ℝ, ℝ)).prod I) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => (G p.1).inner p.2
          (Submission.Geodesic.frameVector (I := I) x₀ p.2 (bB i))
          (Submission.Geodesic.frameVector (I := I) x₀ p.2 (bB j))) (t₀, x₀) :=
      pairing _ _ (hframe i) (hframe j)
    have hcomp : ContMDiffAt ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => (G p.1).inner ((extChartAt I x₀).symm p.2)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm p.2) (bB i))
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm p.2) (bB j)))
        (t₀, (extChartAt I x₀) x₀) :=
      hΛij.comp_of_eq hκ (by
        show (t₀, (extChartAt I x₀).symm ((extChartAt I x₀) x₀)) = (t₀, x₀)
        rw [hleft])
    have h' : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => (G p.1).inner ((extChartAt I x₀).symm p.2)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm p.2) (bB i))
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm p.2) (bB j)))
        (t₀, (extChartAt I x₀) x₀) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact hcomp
    have hcont : ContDiffAt ℝ ∞
        (fun p : ℝ × E => (G p.1).inner ((extChartAt I x₀).symm p.2)
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm p.2) (bB i))
          (Submission.Geodesic.frameVector (I := I) x₀ ((extChartAt I x₀).symm p.2) (bB j)))
        (t₀, (extChartAt I x₀) x₀) :=
      contMDiffAt_iff_contDiffAt.mp h'
    simpa only [chartMat, chartMatFun] using hcont
  -- assemble the matrix components
  refine contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => ?_))
  exact hcompij i j

end Work.Diff.EXT

import Submission.Work.RiemLib.JacobiAtSystem
import Submission.Work.RiemLib.SecondVarGlobal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Jacobi
open Submission.ChartCurv
open Submission.Rauch
open Submission.JacobiTensor
open Submission.RauchGlobal
open Submission.IntrinsicVariation
open Submission.GExpFlow


/-!
# `C^∞` chart coordinates of a Jacobi field, locally

`Submission.JacobiAtSystem` turns the `C¹`-level `IsJacobiAt` data into the first-order Jacobi
system and derives `C^∞` of the field's coordinates **provided** the base curve's coordinates are
`C^∞`.  This module performs the remaining bookkeeping for the application to a *smooth* curve
(e.g. a `GExp`-ray, which is what `CutConjInequality` needs):

* `chartCoords x₀ γ J` — the chart coordinates of the field `J` along `γ` in the chart at `x₀`
  (a *global* definition, via the tangential trivialisation);
* `frameVector_chartCoords` — the frame vector of those coordinates is the field;
* **`exists_chartCoords_contDiffOn`** — for a curve smooth on a neighbourhood of `s` and a Jacobi
  field `J` there (`IsJacobiAt`), there are a chart `x₀` and a radius `η > 0` such that the chart
  coordinates `chartCoords x₀ γ J` are `C^∞` on `Icc (s-η) (s+η)` and represent `J` there.

Together with a finite subcover of the parametrising interval and
`Commons.Topology.Order.exists_partition_subordinate_Icc`, this produces the per-piece `C^∞` chart
data consumed by `Submission.SecondVarGlobal.energy_second_deriv_piece` (Roadmap §100.8, item 1).
-/

namespace Submission.JacobiCoords

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- The chart coordinates of a tangent vector field along a curve, in the chart at `x₀`. -/
noncomputable def chartCoords (x₀ : M) (γ : ℝ → M) (J : (t : ℝ) → TangentSpace I (γ t)) :
    ℝ → E :=
  fun t => (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ (γ t) (J t)

lemma frameVector_chartCoords {x₀ : M} {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)}
    {t : ℝ} (hsrc : γ t ∈ (chartAt H x₀).source) :
    frameVector (I := I) x₀ (γ t) (chartCoords (I := I) x₀ γ J t) = J t :=
  frameVector_clm (I := I) (by rwa [extChartAt_source]) (J t)

/-- **Local `C^∞` chart coordinates of a Jacobi field.** -/
theorem exists_chartCoords_contDiffOn (htor : cov.torsion = 0)
    {γ : ℝ → M} {J : (t : ℝ) → TangentSpace I (γ t)} {s ε : ℝ} (hε : 0 < ε)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (s - ε) (s + ε))) (hJ : IsJacobiAt cov γ J s) :
    ∃ (x₀ : M) (η : ℝ), 0 < η ∧ η ≤ ε ∧
      (∀ t ∈ Icc (s - η) (s + η), γ t ∈ (chartAt H x₀).source) ∧
      ContDiffOn ℝ ∞ (chartCoords (I := I) x₀ γ J) (Icc (s - η) (s + η)) ∧
      (∀ t ∈ Icc (s - η) (s + η), frameVector (I := I) x₀ (γ t)
        (chartCoords (I := I) x₀ γ J t) = J t) := by
  obtain ⟨x₀, u, w, y, ρ, hρ, htgt, huu, hγeq, hJeq, hunit, hy, hyz, hjac⟩ :=
    exists_local_data (cov := cov) hJ
  -- `γ s` is in the chart source
  have hsρ : s ∈ Ioo (s - ρ) (s + ρ) := ⟨by linarith, by linarith⟩
  have hsrc_s : γ s ∈ (chartAt H x₀).source := by
    have h2 : γ s = (extChartAt I x₀).symm (u s) := hγeq s hsρ
    rw [h2]
    exact mem_source_chartCurve (I := I) (htgt s hsρ)
  -- `γ` stays in the chart source near `s`
  have hsε : s ∈ Ioo (s - ε) (s + ε) := ⟨by linarith, by linarith⟩
  have hcont : ContinuousAt γ s :=
    hγ.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hsε)
  have hsrc_ev : ∀ᶠ t in 𝓝 s, γ t ∈ (chartAt H x₀).source :=
    hcont.preimage_mem_nhds ((chartAt H x₀).open_source.mem_nhds hsrc_s)
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hsrc_ev
  -- the working radius
  set η : ℝ := min (min (ρ / 3) (δ / 3)) (ε / 3) with hηdef
  have hη : 0 < η := by
    rw [hηdef]
    exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hηρ : η < ρ := by
    rw [hηdef]
    have := min_le_left (ρ / 3) (δ / 3)
    have h2 : min (ρ / 3) (δ / 3) ≤ ρ / 3 := min_le_left _ _
    linarith [min_le_left (min (ρ / 3) (δ / 3)) (ε / 3)]
  have hηδ : η < δ := by
    rw [hηdef]
    have h2 : min (ρ / 3) (δ / 3) ≤ δ / 3 := min_le_right _ _
    have h3 : min (min (ρ / 3) (δ / 3)) (ε / 3) ≤ min (ρ / 3) (δ / 3) := min_le_left _ _
    linarith
  have hηε : η ≤ ε := by
    rw [hηdef]
    have h3 : min (min (ρ / 3) (δ / 3)) (ε / 3) ≤ ε / 3 := min_le_right _ _
    linarith
  -- membership lemmas for the working interval
  have hsub_ρ : ∀ t : ℝ, t ∈ Ioo (s - η) (s + η) → t ∈ Ioo (s - ρ) (s + ρ) :=
    fun t ht => ⟨by linarith [ht.1, hηρ], by linarith [ht.2, hηρ]⟩
  have hsub_ε : ∀ t : ℝ, t ∈ Ioo (s - η) (s + η) → t ∈ Ioo (s - ε) (s + ε) :=
    fun t ht => ⟨by linarith [ht.1, hηε], by linarith [ht.2, hηε]⟩
  have hsub_src : ∀ t : ℝ, t ∈ Ioo (s - η) (s + η) → γ t ∈ (chartAt H x₀).source := by
    intro t ht
    refine hδsub ?_
    rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_lt]
    exact ⟨by linarith [ht.1, hηδ], by linarith [ht.2, hηδ]⟩
  -- `u` is the chart coordinate curve and `w` its derivative
  have hueq : ∀ t ∈ Ioo (s - η) (s + η), u t = chartCoord (I := I) x₀ γ t := by
    intro t ht
    have htρ : t ∈ Ioo (s - ρ) (s + ρ) := hsub_ρ t ht
    have h1 : u t ∈ (extChartAt I x₀).target := htgt t htρ
    have h2 : γ t = (extChartAt I x₀).symm (u t) := hγeq t htρ
    show u t = (extChartAt I x₀) (γ t)
    rw [h2]
    exact (PartialEquiv.right_inv (extChartAt I x₀) h1).symm
  have hweq : ∀ t ∈ Ioo (s - η) (s + η), w t = deriv (chartCoord (I := I) x₀ γ) t := by
    intro t ht
    have htρ : t ∈ Ioo (s - ρ) (s + ρ) := hsub_ρ t ht
    have hev : chartCoord (I := I) x₀ γ =ᶠ[𝓝 t] u := by
      refine Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ht) ?_
      intro r hr
      exact (hueq r hr).symm
    have h1 : HasDerivAt (chartCoord (I := I) x₀ γ) (w t) t :=
      (huu t htρ).congr_of_eventuallyEq hev
    exact h1.deriv.symm
  -- smoothness of the base curve's coordinates
  have hγI : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo (s - η) (s + η)) :=
    hγ.mono (fun t ht => hsub_ε t ht)
  have hcoord : ContDiffOn ℝ ∞ (chartCoord (I := I) x₀ γ) (Ioo (s - η) (s + η)) :=
    Submission.SecondVarGlobal.contDiffOn_chartCoord (I := I) (z₀ := x₀) hγI
      (fun t ht => hsub_src t ht)
  have hderivcoord : ContDiffOn ℝ ∞ (deriv (chartCoord (I := I) x₀ γ)) (Ioo (s - η) (s + η)) :=
    hcoord.deriv_of_isOpen isOpen_Ioo (le_of_eq (by simp))
  -- the system hypotheses, transferred to the chart coordinate functions
  have hφ : ∀ t : ℝ, t ∈ Ioo (s - η) (s + η) →
      chartCovDeriv cov x₀ u w y t
        = chartCovDeriv cov x₀ (chartCoord (I := I) x₀ γ) (deriv (chartCoord (I := I) x₀ γ)) y t := by
    intro t ht
    have h1 := hueq t ht
    have h2 := hweq t ht
    have htgt' : u t ∈ (extChartAt I x₀).target := htgt t (hsub_ρ t ht)
    have htgts : chartCoord (I := I) x₀ γ t ∈ (extChartAt I x₀).target :=
      (extChartAt I x₀).map_source (by rw [extChartAt_source]; exact hsub_src t ht)
    rw [chartCovDeriv_apply (cov := cov) htgt', chartCovDeriv_apply (cov := cov) htgts, h1, h2]
  -- the system on a smaller open interval
  set A₀ : ℝ := s - η / 2 with hAdef
  set B₀ : ℝ := s + η / 2 with hBdef
  have hAB : Ioo A₀ B₀ ⊆ Ioo (s - η) (s + η) := by
    intro t ht
    rw [hAdef] at ht
    rw [hBdef] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  set a : ℝ := s - η / 4 with hadef
  set b : ℝ := s + η / 4 with hbdef
  have hab : a < b := by rw [hadef, hbdef]; linarith
  have habt : Icc a b ⊆ Ioo A₀ B₀ := by
    intro t ht
    rw [hadef] at ht
    rw [hbdef] at ht
    rw [hAdef, hBdef]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hABtgt : ∀ t : ℝ, t ∈ Ioo A₀ B₀ → t ∈ Ioo (s - ρ) (s + ρ) :=
    fun t ht => hsub_ρ t (hAB ht)
  have hycd : ContDiffOn ℝ ∞ y (Icc a b) := by
    refine Submission.JacobiAtSystem.contDiffOn_of_isJacobiSystem (cov := cov) (w := w) htor hab habt
      (fun t ht => htgt t (hABtgt t ht)) ?_ ?_ ?_ ?_ ?_ ?_
    · exact (hcoord.congr (fun t ht => hueq t ht)).mono hAB
    · exact (hderivcoord.congr (fun t ht => hweq t ht)).mono hAB
    · intro t ht
      exact hy t (hABtgt t ht)
    · intro t ht
      exact hyz t (hABtgt t ht)
    · intro t ht
      exact hjac t (hABtgt t ht)
    · refine (isOpen_Ioo.continuousOn_iff.mpr (fun t ht => (hy t (hABtgt t ht)).continuousAt)).mono habt
  -- transfer to the global chart coordinates
  have hcoords_eq : ∀ t ∈ Icc a b, y t = chartCoords (I := I) x₀ γ J t := by
    intro t ht
    have hsrc : γ t ∈ (chartAt H x₀).source := hsub_src t (hAB (habt ht))
    have h1 : frameVector (I := I) x₀ (γ t) (y t) = J t := hJeq t (hABtgt t (habt ht))
    have h2 : frameVector (I := I) x₀ (γ t) (chartCoords (I := I) x₀ γ J t) = J t :=
      frameVector_chartCoords (I := I) hsrc
    have h3 : frameVector (I := I) x₀ (γ t) (y t - chartCoords (I := I) x₀ γ J t) = 0 := by
      rw [frameVector_sub, h1, h2, sub_self]
    exact sub_eq_zero.mp (Submission.GExpSmooth.frameVector_eq_zero (I := I) (by rwa [extChartAt_source]) h3)
  refine ⟨x₀, η / 4, by linarith, by linarith, ?_, ?_, ?_⟩
  · intro t ht
    exact hsub_src t (hAB (habt ht))
  · exact hycd.congr (fun t ht => (hcoords_eq t ht).symm)
  · intro t ht
    exact frameVector_chartCoords (I := I) (hsub_src t (hAB (habt ht)))

end

end Submission.JacobiCoords

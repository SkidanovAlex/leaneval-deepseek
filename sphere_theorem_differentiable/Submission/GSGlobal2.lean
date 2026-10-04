import Submission.GSGlobal
import Submission.GSStep1
import Submission.Commons.Geometry.Manifold.Tangent.contMDiff_finset_sum_smul_section
import Submission.Commons.Geometry.Manifold.exists_contMDiff_sum_one_of_isCompact

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The continuous gradient-like field of `d(p,·)` on compact sets

`Submission/GSGlobal.lean` shows that the local ascent directions produced by
`GSField.exists_open_ascent_field` can be glued into a *pointwise* ascent field.  This file carries
out Grove--Shiohama's step 3(a) properly: on a **compact** set `t` the gluing produces a field that
is an ascent direction at every point of `t` **and** whose section of the tangent bundle is
continuous (in fact `C^∞`), which is what the flow argument of step 3(b) needs.

The ingredients are

* `exists_fin_subcover_of_isCompact` — a finite subcover indexed by `Fin n` (from
  `IsCompact.elim_finite_subcover`);
* `Commons.Geometry.Manifold.exists_contMDiff_sum_one_of_isCompact` — a *smooth* partition of unity
  subordinate to a finite open cover of a compact set (the manifold Urysohn lemma);
* `isAscentAt_finsum_of_partition` (`Submission/GSGlobal`) — a convex combination of ascent
  directions with a partition of unity is an ascent direction;
* `Commons.Geometry.Manifold.Tangent.contMDiff_finset_sum_smul_section` — a finite sum of smooth
  sections of the tangent bundle with smooth coefficients is smooth.

Main results:

* `exists_ascent_field_continuous_of_isCompact` — the gluing, from abstract local data;
* `exists_continuous_ascent_field_of_diam` — the instantiation in the restricted Grove--Shiohama
  range (`diam ≤ 2π/3`) on a compact piece of `M \ {p,q}`, from
  `GSField.exists_open_ascent_field_of_diam`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.GlobalExp
open Submission.GSCritical
open Submission.GSField
open Submission.Distance
open Submission.Gauss
open Submission.GSGlobal

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GSGlobal2

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **A finite subcover indexed by `Fin n`.** -/
theorem exists_fin_subcover_of_isCompact {X : Type*} [TopologicalSpace X] {ι : Type*} {t : Set X}
    (ht : IsCompact t) (U : ι → Set X) (ho : ∀ i, IsOpen (U i))
    (hc : ∀ x ∈ t, ∃ i, x ∈ U i) :
    ∃ (n : ℕ) (g : Fin n → ι), t ⊆ ⋃ i, U (g i) := by
  classical
  obtain ⟨F, hF⟩ := ht.elim_finite_subcover U ho (fun x hx => mem_iUnion.mpr (hc x hx))
  refine ⟨F.card, fun i => (F.equivFin.symm i).1, fun x hx => ?_⟩
  obtain ⟨i, hiF, hix⟩ := mem_iUnion₂.mp (hF hx)
  refine mem_iUnion.mpr ⟨F.equivFin ⟨i, hiF⟩, ?_⟩
  simpa using hix

/-- **A continuous ascent field on a compact set.**  In the restricted Grove--Shiohama range, a
compact piece of `M \ {p,q}` carries a field which is an ascent direction for `d(p,·)` at every
point of it and whose section of the tangent bundle is continuous.

The local data `hloc` is what `GSField.exists_open_ascent_field` provides. -/
theorem exists_ascent_field_continuous_of_isCompact
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) [PathConnectedSpace M]
    [RegularSpace M] {p : M} {s t : Set M} (ht : IsCompact t) (hts : t ⊆ s)
    (hloc : ∀ x ∈ s, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ ∃ (x₀ : M) (v : E),
      U ⊆ (chartAt H x₀).source ∧
      ∀ y ∈ U, IsAscentAt (cov := cov) hmet p y (frameVector (I := I) x₀ y v)) :
    ∃ V : (y : M) → TangentSpace I y,
      (∀ y ∈ t, IsAscentAt (cov := cov) hmet p y (V y)) ∧
      ContinuousOn (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))) t ∧
      ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
        (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))) := by
  classical
  have hch : ∀ i : {x : M // x ∈ s}, ∃ (U : Set M) (x₀ : M) (v : E),
      IsOpen U ∧ (i : M) ∈ U ∧ U ⊆ (chartAt H x₀).source ∧
        ∀ y ∈ U, IsAscentAt (cov := cov) hmet p y (frameVector (I := I) x₀ y v) := by
    intro i
    obtain ⟨U, hUo, hiU, x₀, v, hUsrc, hasc⟩ := hloc i i.2
    exact ⟨U, x₀, v, hUo, hiU, hUsrc, hasc⟩
  choose U x₀ vv hUo hUm hUsrc hasc using hch
  obtain ⟨n, g, hg⟩ := exists_fin_subcover_of_isCompact ht U hUo
    (fun x hx => ⟨⟨x, hts hx⟩, hUm ⟨x, hts hx⟩⟩)
  obtain ⟨φ, hφsm, hφtsup, hφnn, hφsum⟩ :=
    Commons.Geometry.Manifold.exists_contMDiff_sum_one_of_isCompact (I := I)
      (s := fun i : Fin n => U (g i)) ht (fun i => hUo (g i)) hg
  have hsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, ∑ i, φ i y • frameVector (I := I) (x₀ (g i)) y (vv (g i))⟩ :
        Bundle.TotalSpace E (TangentSpace I))) :=
    Commons.Geometry.Manifold.Tangent.contMDiff_finset_sum_smul_section (I := I) (M := M) (F := Finset.univ)
      (f := fun i y => φ i y)
      (W := fun i y => frameVector (I := I) (x₀ (g i)) y (vv (g i)))
      (V := fun i => U (g i)) (fun i => hUo (g i))
      (fun i _ => hφsm i) (fun i _ => hφtsup i) (fun i _ =>
        (contMDiffOn_frameVector (x₀ (g i)) (vv (g i))).mono (hUsrc (g i)))
  refine ⟨fun y => ∑ i, φ i y • frameVector (I := I) (x₀ (g i)) y (vv (g i)), ?_, ?_, ?_⟩
  · intro y hy
    have hsum : ∑ i, φ i y = 1 := by
      have h := hφsum hy
      simpa only [Finset.sum_apply, Pi.one_apply] using h
    refine isAscentAt_finsum_of_partition (U := fun i => U (g i))
      (V := fun i z => frameVector (I := I) (x₀ (g i)) z (vv (g i)))
      (φ := fun i z => φ i z) (y := y) (fun i z hz => hasc (g i) z hz)
      (fun i z => hφnn i z) (fun i => ?_) hsum
    exact subset_closure.trans (hφtsup i)
  · exact (hsm.continuous).continuousOn
  · exact hsm

/-- **A continuous ascent field on a compact piece of `M \ {p,q}`** in the restricted
Grove--Shiohama range (`diam ≤ 2π/3`): the local existence of ascent directions
(`GSField.exists_open_ascent_field_of_diam`) upgraded to a *continuous* global field on `t`, via a
smooth partition of unity subordinate to a finite subcover. -/
theorem exists_continuous_ascent_field_of_diam
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    [PathConnectedSpace M] [RegularSpace M] {p q : M} {D : ℝ}
    (hdiam : ∀ r s : M, Manifold.riemannianEDist I r s ≤ ENNReal.ofReal D)
    (hDgt : Real.pi / 2 < D) (hDlt : D < Real.pi)
    (hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D)
    {t : Set M} (ht : IsCompact t) (htp : ∀ x ∈ t, x ≠ p) (htq : ∀ x ∈ t, x ≠ q) :
    ∃ V : (y : M) → TangentSpace I y,
      (∀ y ∈ t, IsAscentAt (cov := cov) hmet p y (V y)) ∧
      ContinuousOn (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))) t ∧
      ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
        (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))) := by
  classical
  refine exists_ascent_field_continuous_of_isCompact (cov := cov) hmet htor
    (s := {x : M | x ≠ p ∧ x ≠ q}) ht (fun x hx => ⟨htp x hx, htq x hx⟩) (fun x hx => ?_)
  obtain ⟨v, hv1, hv⟩ := exists_isAscentAt_off_pq (cov := cov) hmet htor hpinch hdiam hDgt hDlt
    hpq hx.1 hx.2
  have hxsrc : x ∈ (extChartAt I x).source := by
    rw [extChartAt_source]; exact mem_chart_source H x
  let vv : E := (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v
  have hfv : IsAscentAt (cov := cov) hmet p x (frameVector (I := I) x x vv) := by
    rw [Submission.GExpFlow.frameVector_clm (I := I) hxsrc v]
    exact hv
  obtain ⟨U, hUo, hxU, hUa⟩ := exists_open_ascent_field (cov := cov) hmet htor hx.1 hfv
  exact ⟨U ∩ (chartAt H x).source, hUo.inter (chartAt H x).open_source,
    ⟨hxU, mem_chart_source H x⟩, x, vv, Set.inter_subset_right, fun y hy => hUa y hy.1⟩

end

end Submission.GSGlobal2

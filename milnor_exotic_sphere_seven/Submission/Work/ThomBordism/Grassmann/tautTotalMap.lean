import Mathlib
import Submission.Work.ThomBordism.Grassmann.EvalBundle
import Submission.Work.ThomBordism.Grassmann.PlaneEval
import Submission.Work.ThomBordism.Grassmann.PlaneAct
import Submission.Work.ThomBordism.Grassmann.PlaneCoord

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000

open scoped Topology

namespace Work.ThomBordism.Grassmann

noncomputable section

/-- **The incidence parametrisation of the tautological bundle is continuous.**  The point of the
total space of the tautological bundle whose plane is `q.1` and whose vector is `q.2` depends
continuously on `(q.1, q.2)` on the incidence locus `memPlane q.1 q.2`.

This is the same statement as `continuousOn_toE_underlying` without the hypothesis `q.2 ≠ 0`: the
proof only ever uses `memPlane` (`localTriv_mkTotal` needs nothing else), so it applies verbatim. -/
theorem continuousOn_mkTotal_toECoordAt {k m : ℕ} :
    ContinuousOn (fun q : OG k m × Amb (k + m) =>
      mkTotal q.1 (toECoordAt ((tautologicalBundle k m).indexAt q.1) q.1 q.2))
      {q : OG k m × Amb (k + m) | memPlane q.1 q.2} := by
  intro x hx
  set S := (tautologicalBundle k m).indexAt x.1 with hS
  let e := (tautologicalBundle k m).localTriv S
  let U : Set (OG k m × Amb (k + m)) := {q | q.1 ∈ (tautologicalBundle k m).baseSet S}
  let s : Set (OG k m × Amb (k + m)) := {q | memPlane q.1 q.2}
  have hxS : x.1 ∈ (tautologicalBundle k m).baseSet S := (tautologicalBundle k m).mem_baseSet_at x.1
  have hU : U ∈ 𝓝 x := ((isOpen_baseSet S).preimage continuous_fst).mem_nhds hxS
  have hsource : ∀ q : OG k m × Amb (k + m), q.1 ∈ (tautologicalBundle k m).baseSet S →
      mkTotal q.1 (toECoordAt ((tautologicalBundle k m).indexAt q.1) q.1 q.2) ∈ e.source := by
    intro q hq
    rw [VectorBundleCore.mem_localTriv_source]
    exact hq
  have htarget : ∀ q : OG k m × Amb (k + m), q.1 ∈ (tautologicalBundle k m).baseSet S →
      (q.1, toECoordAt S q.1 q.2) ∈ e.target := by
    intro q hq
    rw [VectorBundleCore.mem_localTriv_target]
    exact hq
  have hg : ContinuousOn (fun q : OG k m × Amb (k + m) =>
      e.toOpenPartialHomeomorph.symm (q.1, toECoordAt S q.1 q.2)) U :=
    (OpenPartialHomeomorph.continuousOn_symm e.toOpenPartialHomeomorph).comp
      (continuousOn_fst.prodMk (continuousOn_toECoordAt S)) htarget
  have hfilter : 𝓝[U ∩ s] x = 𝓝[s] x := nhdsWithin_inter_of_mem (nhdsWithin_le_nhds hU)
  have hmain : ContinuousWithinAt (fun q : OG k m × Amb (k + m) =>
      mkTotal q.1 (toECoordAt ((tautologicalBundle k m).indexAt q.1) q.1 q.2)) (U ∩ s) x := by
    refine ((hg.continuousWithinAt hxS).mono Set.inter_subset_left).congr_of_eventuallyEq ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with q hq
      rw [← localTriv_mkTotal S q.1 hq.1 q.2 hq.2]
      exact (e.left_inv' (hsource q hq.1)).symm
    · rw [← localTriv_mkTotal S x.1 hxS x.2 hx]
      exact (e.left_inv' (hsource x hxS)).symm
  show Filter.Tendsto (fun q : OG k m × Amb (k + m) =>
      mkTotal q.1 (toECoordAt ((tautologicalBundle k m).indexAt q.1) q.1 q.2)) (𝓝[s] x)
      (𝓝 (mkTotal x.1 (toECoordAt ((tautologicalBundle k m).indexAt x.1) x.1 x.2)))
  rw [← hfilter]
  exact hmain

theorem tautTotalMap {X : Type*} [TopologicalSpace X] {k m : ℕ}
    (P : C(X, Work.ThomBordism.Grassmann.OG k m))
    (W : C(X, Work.ThomBordism.Grassmann.Amb (k + m)))
    (hW : ∀ x, Work.ThomBordism.Grassmann.memPlane (P x) (W x)) :
    ∃ G : C(X, (Work.ThomBordism.Grassmann.tautologicalBundle k m).TotalSpace),
      (∀ x, (Work.ThomBordism.Grassmann.tautologicalBundle k m).proj (G x) = P x) ∧
      (∀ x, Work.ThomBordism.Grassmann.evalVec (G x) = W x) := by
  refine ⟨⟨fun x => mkTotal (P x)
      (toECoordAt ((tautologicalBundle k m).indexAt (P x)) (P x) (W x)), ?_⟩, fun x => ?_,
    fun x => ?_⟩
  · exact ((continuousOn_mkTotal_toECoordAt (k := k) (m := m)).comp_continuous
      (P.continuous.prodMk W.continuous) (fun x => hW x)).congr (fun x => rfl)
  · rfl
  · show evalVec (mkTotal (P x)
      (toECoordAt ((tautologicalBundle k m).indexAt (P x)) (P x) (W x))) = W x
    rw [evalVec_mkTotal]
    exact evalChartO_toECoordAt _ (P x)
      ((tautologicalBundle k m).mem_baseSet_at (P x)) (W x) (hW x)

end

end Work.ThomBordism.Grassmann

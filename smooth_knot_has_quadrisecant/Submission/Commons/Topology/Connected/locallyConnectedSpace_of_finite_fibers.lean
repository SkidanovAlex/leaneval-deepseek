import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Commons.Topology.Plane.componentIn_of_finite_fibers

namespace Commons.Topology.Connected

open Set Metric
open scoped _root_.Topology

/-- **A compact connected metric space admitting a continuous finite-to-one map into `ℝ` is
locally connected.** The construction is local: given `p` and a neighbourhood `U` of `p`, choose a
ball `B(p, ε) ⊆ U` small enough that it meets the fibre `f⁻¹(f p)` only in `p`; the already-known
lemma `componentIn_of_finite_fibers` then shows that the connected component of `p` in `B(p, ε)`
is a neighbourhood of `p`, and it is preconnected and contained in `U`. -/
theorem locallyConnectedSpace_of_finite_fibers {X : Type*} [MetricSpace X] [CompactSpace X] [ConnectedSpace X] (f : X → ℝ) (hf : Continuous f) (hfin : ∀ c : ℝ, {x : X | f x = c}.Finite) (hfin2 : ∀ p : X, ∀ t r : ℝ, {x : X | f x = t ∧ dist x p = r}.Finite) : LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro p U hU
  -- Separate `p` from the rest of its fibre `f ⁻¹' {f p}` while staying inside `U`.
  have hLfin : ({x : X | f x = f p}).Finite := hfin (f p)
  have hAclosed : IsClosed ({x : X | f x = f p} \ {p}) := hLfin.sdiff.isClosed
  have hnhds : U ∩ ({x : X | f x = f p} \ {p})ᶜ ∈ 𝓝 p :=
    Filter.inter_mem hU (hAclosed.isOpen_compl.mem_nhds (by simp))
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hnhds
  have hballU : Metric.ball p ε ⊆ U := fun x hx => (hεsub hx).1
  have hsep : ({x : X | f x = f p} ∩ Metric.ball p ε) = {p} := by
    apply Set.Subset.antisymm
    · rintro y ⟨hyL, hyb⟩
      by_contra hyne
      exact (hεsub hyb).2 ⟨hyL, hyne⟩
    · intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact ⟨rfl, Metric.mem_ball_self hεpos⟩
  obtain ⟨δ, hδpos, hδ⟩ :=
    Commons.Topology.Plane.componentIn_of_finite_fibers p f hf hfin (hfin2 p) hεpos hsep
  exact ⟨connectedComponentIn (Metric.ball p ε) p,
    Filter.mem_of_superset (Metric.ball_mem_nhds p hδpos)
      (fun q hq => hδ q (Metric.mem_ball.mp hq)),
    isPreconnected_connectedComponentIn,
    (connectedComponentIn_subset (Metric.ball p ε) p).trans hballU⟩

end Commons.Topology.Connected
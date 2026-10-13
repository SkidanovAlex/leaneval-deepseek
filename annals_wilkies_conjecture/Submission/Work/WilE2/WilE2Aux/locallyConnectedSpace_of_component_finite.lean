/-
# A closed set whose local balls have finitely many components is locally connected

`Work.WilE2.WilE2Aux.locallyConnectedSpace_of_component_finite`

Let `X` be a closed subset of a metric space such that for every `x ∈ X` and every `δ > 0`
the set `X ∩ closedBall x δ` has only **finitely many connected components**.  Then `X`, with
the subspace topology, is locally connected.

The proof is the following.  Fix `x ∈ X` and `δ > 0`, put `S = X ∩ closedBall x δ` and let
`C = connectedComponentIn S x` be the component of `x`.  Since `S` is closed, every component
of `S` is closed (`isClosed_connectedComponentIn`), and by hypothesis only finitely many
components occur.  Hence the union `T` of all components of `S` *other* than `C` is a finite
union of closed sets, so closed (`sUnion_connectedComponentIn_sdiff_isClosed`); and `x ∉ T`,
because a component containing `x` equals `C`.  A closed set avoiding `x` keeps a small ball
away from `x`, so `X ∩ ball x η ⊆ C` for some `η > 0`: the component `C` is a preconnected
neighbourhood of `x` in `X` (pulled back to the subspace along `Subtype.val`, using
`isPreconnected_preimage_subtype_val`), and the components `C` obtained this way (as `δ`
shrinks) form a local basis.  This is `locallyConnectedSpace_iff_connected_subsets`.
-/
import Mathlib
import Submission.Work.WilE2.WilE2Aux.isClosed_connectedComponentIn
import Submission.Work.WilE2.WilE2Aux.sUnion_connectedComponentIn_sdiff_isClosed
import Submission.Work.WilE2.WilE2Aux.isPreconnected_preimage_subtype_val

namespace Work.WilE2.WilE2Aux

/-- **Key lemma.**  Let `X` be closed in a metric space, `x ∈ X` and `δ > 0`, and suppose that
`X ∩ closedBall x δ` has only finitely many connected components.  Then the component `C` of
`x` in `X ∩ closedBall x δ` contains a relative ball around `x`: there is `η > 0` with
`X ∩ ball x η ⊆ C`. -/
theorem exists_ball_subset_connectedComponentIn {α : Type*} [MetricSpace α] {X : Set α}
    (hX : IsClosed X) {x : α} (hx : x ∈ X) {δ : ℝ} (hδ : 0 < δ)
    (hfin : (Set.range (connectedComponentIn (X ∩ Metric.closedBall x δ))).Finite) :
    ∃ η : ℝ, 0 < η ∧ X ∩ Metric.ball x η ⊆ connectedComponentIn (X ∩ Metric.closedBall x δ) x := by
  set S : Set α := X ∩ Metric.closedBall x δ with hS
  have hfin' : (Set.range (connectedComponentIn S)).Finite := by simpa only [hS] using hfin
  have hSclosed : IsClosed S := by rw [hS]; exact hX.inter Metric.isClosed_closedBall
  have hxS : x ∈ S := ⟨hx, Metric.mem_closedBall_self hδ.le⟩
  have hkey := sUnion_connectedComponentIn_sdiff_isClosed
    (S := S) (fun y => isClosed_connectedComponentIn hSclosed y) hfin' x
  set T : Set α := ⋃₀ (Set.range (connectedComponentIn S) \ {connectedComponentIn S x}) with hT
  have hTclosed : IsClosed T := hkey.1
  have hxT : x ∉ T := hkey.2
  obtain ⟨ε, hεpos, hεT⟩ := Metric.mem_nhds_iff.mp (hTclosed.isOpen_compl.mem_nhds hxT)
  refine ⟨min ε δ, lt_min hεpos hδ, ?_⟩
  intro y ⟨hyX, hyball⟩
  have hyball' : dist y x < min ε δ := Metric.mem_ball.mp hyball
  have hyS : y ∈ S :=
    ⟨hyX, Metric.mem_closedBall.mpr (le_of_lt (lt_of_lt_of_le hyball' (min_le_right _ _)))⟩
  have hyT : y ∉ T := by
    intro hyT
    exact (hεT (Metric.mem_ball.mpr (lt_of_lt_of_le hyball' (min_le_left _ _)))) hyT
  have hymem : y ∈ connectedComponentIn S y := mem_connectedComponentIn hyS
  by_cases hC : connectedComponentIn S y = connectedComponentIn S x
  · rw [hS] at hC
    rw [hC] at hymem
    simpa only [hS] using hymem
  · exact absurd (by
      rw [Set.mem_sUnion]
      exact ⟨connectedComponentIn S y, ⟨Set.mem_range_self y, hC⟩, hymem⟩) hyT

theorem locallyConnectedSpace_of_component_finite {α : Type*} [MetricSpace α] {X : Set α}
    (hX : IsClosed X)
    (h : ∀ x ∈ X, ∀ δ : ℝ, 0 < δ →
      (Set.range (connectedComponentIn (X ∩ Metric.closedBall x δ))).Finite) :
    LocallyConnectedSpace ↥X := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x U hU
  obtain ⟨ε, hεpos, hεU⟩ := Metric.mem_nhds_iff.mp hU
  have hhalf : (0 : ℝ) < ε / 2 := by linarith
  obtain ⟨η, hηpos, hηsub⟩ :=
    exists_ball_subset_connectedComponentIn (X := X) (x := (x : α)) hX x.2 (δ := ε / 2) hhalf
      (h (x : α) x.2 (ε / 2) hhalf)
  refine ⟨Subtype.val ⁻¹' connectedComponentIn (X ∩ Metric.closedBall (x : α) (ε / 2)) (x : α),
    ?_, ?_, ?_⟩
  · refine Filter.mem_of_superset (Metric.ball_mem_nhds x hηpos) ?_
    intro y hy
    have hyb : dist (y : α) (x : α) < η := by
      have h1 : dist y x < η := Metric.mem_ball.mp hy
      rwa [Subtype.dist_eq] at h1
    exact hηsub ⟨y.2, Metric.mem_ball.mpr hyb⟩
  · exact isPreconnected_preimage_subtype_val
      ((connectedComponentIn_subset _ _).trans Set.inter_subset_left)
      isPreconnected_connectedComponentIn
  · intro y hy
    have hyC : (y : α) ∈ connectedComponentIn (X ∩ Metric.closedBall (x : α) (ε / 2)) (x : α) := hy
    have hle : dist (y : α) (x : α) ≤ ε / 2 :=
      Metric.mem_closedBall.mp (connectedComponentIn_subset _ _ hyC).2
    apply hεU
    rw [Metric.mem_ball, Subtype.dist_eq]
    linarith

end Work.WilE2.WilE2Aux

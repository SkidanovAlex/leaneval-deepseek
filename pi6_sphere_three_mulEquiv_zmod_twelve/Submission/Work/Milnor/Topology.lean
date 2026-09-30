import Mathlib
import Submission.Work.Milnor.Clutch
import Submission.Work.Glue.glued_compactSpace
import Submission.Work.Glue.glued_t2space
import Submission.Work.Milnor.graph_closed_clutchMap

set_option synthInstance.maxHeartbeats 400000

/-!
# Topological properties of Milnor's manifold `M_k`

`Submission.Work.Milnor.Clutch` realises Milnor's `M_k` as the quotient
`Mk k = (clutchData k).Glued` of two copies of `ℝ⁴ × S³` glued along `{x ≠ 0}` by the clutching
map `φ(x, y) = (x/‖x‖², u^{-k} y u^{-1})`.

Here we prove that `Mk k` is a **compact** Hausdorff space (compactness uses that the two `ℝ⁴`
charts are glued at infinity: the two "unit balls" `{‖x‖ ≤ 1}` already cover all of `Mk k`).

Hausdorffness is proved separately:
* `Work.Glue.glued_t2space` (delegated) reduces it to closedness of the graph of the gluing map;
* `Work.Milnor.graph_closed_clutchMap` (delegated) proves that the graph of `clutchMap k` is
  closed, the essential point being that `φ` blows up as `x → 0`.
-/

open scoped Manifold ContDiff Topology
open TopologicalSpace Set

namespace Submission.Milnor

noncomputable section

/-- The unit ball over the base `ℝ⁴`, as a subset of the ambient space `ℝ⁴ × S³`. -/
def baseBall : Set MSpace := {p : MSpace | ‖p.1‖ ≤ 1}

lemma isCompact_baseBall : IsCompact baseBall := by
  have h : baseBall = Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1 ×ˢ (univ : Set QS3) := by
    ext p
    simp [baseBall, Metric.mem_closedBall, dist_zero_right]
  rw [h]
  exact IsCompact.prod (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 4)) 1) isCompact_univ

/-- The images of the unit ball under the two open embeddings cover `Mk k`: every point of `Mk k`
is represented either by a point of the unit ball of the first chart, or by a point of the unit
ball of the second chart (the two charts are glued at infinity). -/
lemma cover_baseBall (k : ℤ) :
    (clutchData k).ιX '' baseBall ∪ (clutchData k).ιY '' baseBall = univ := by
  rw [eq_univ_iff_forall]
  intro z
  refine Quotient.inductionOn z ?_
  intro a
  rcases a with p | p
  · by_cases hp : ‖p.1‖ ≤ 1
    · exact Or.inl ⟨p, hp, rfl⟩
    · push Not at hp
      have hp0 : p.1 ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hp
        linarith
      refine Or.inr ⟨clutchMap k p, ?_, ?_⟩
      · show ‖(invBase p.1)‖ ≤ 1
        rw [norm_invBase]
        exact inv_le_one_of_one_le₀ (le_of_lt hp)
      · exact ((clutchData k).ιX_eq_ιY_iff.mpr ⟨hp0, rfl⟩).symm
  · by_cases hp : ‖p.1‖ ≤ 1
    · exact Or.inr ⟨p, hp, rfl⟩
    · push Not at hp
      have hp0 : p.1 ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hp
        linarith
      refine Or.inl ⟨clutchMapInv k p, ?_, ?_⟩
      · show ‖(invBase p.1)‖ ≤ 1
        rw [norm_invBase]
        exact inv_le_one_of_one_le₀ (le_of_lt hp)
      · refine (clutchData k).ιX_eq_ιY_iff.mpr ⟨?_, ?_⟩
        · show (invBase p.1) ≠ 0
          exact invBase_ne_zero hp0
        · show clutchMap k (clutchMapInv k p) = p
          exact clutchMap_clutchMapInv k p hp0

/-- **Milnor's `M_k` is compact.** -/
instance (k : ℤ) : CompactSpace (Mk k) := by
  rw [← isCompact_univ_iff, ← cover_baseBall k]
  exact (isCompact_baseBall.image (clutchData k).continuous_ιX).union
    (isCompact_baseBall.image (clutchData k).continuous_ιY)


/-- A base point of `MSpace = ℝ⁴ × S³` whose first coordinate is nonzero. -/
def basePoint : MSpace :=
  (Quaternion.linearIsometryEquivTuple (1 : Quaternion ℝ), ⟨(1 : Quaternion ℝ), by simp⟩)

lemma basePoint_ne : basePoint.1 ≠ 0 := by
  have h1 : ‖basePoint.1‖ = 1 := by
    show ‖Quaternion.linearIsometryEquivTuple (1 : Quaternion ℝ)‖ = 1
    rw [Quaternion.linearIsometryEquivTuple.norm_map]; norm_num
  intro h
  rw [h, norm_zero] at h1
  norm_num at h1

lemma basePoint_mem : basePoint ∈ (clutchOpens : Set MSpace) := basePoint_ne

/-- The unit quaternions are connected (they form a sphere of dimension `3 > 0`). -/
instance : ConnectedSpace QS3 := by
  have hr : (1 : Cardinal) < Module.rank ℝ (Quaternion ℝ) := by
    rw [← Module.finrank_eq_rank', Fact.out (p := Module.finrank ℝ (Quaternion ℝ) = 3 + 1)]
    norm_num
  exact isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := Quaternion ℝ) hr (0 : Quaternion ℝ) (by norm_num))

/-- **Milnor's `M_k` is Hausdorff.**  This follows from the closedness of the graph of the
gluing map `clutchMap k` (`Work.Milnor.graph_closed_clutchMap`), which is exactly the hypothesis
of the general criterion `Work.Glue.glued_t2space`. -/
instance (k : ℤ) : T2Space (Mk k) := by
  refine Work.Glue.glued_t2space (clutchData k) ?_
  have h : {z : MSpace × MSpace | z.1 ∈ (clutchData k).U ∧ ((clutchData k).φ z.1 : MSpace) = z.2}
      = {z : MSpace × MSpace | z.1 ∈ (clutchOpens : Set MSpace) ∧ z.2 = clutchMap k z.1} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩
  rw [h]
  exact Work.Milnor.graph_closed_clutchMap k

instance (k : ℤ) : Nonempty (Mk k) := ⟨(clutchData k).ιX basePoint⟩

/-- **Milnor's `M_k` is connected**: it is the union of the images of the two (connected) copies
of `ℝ⁴ × S³`, which meet along the glued region. -/
instance (k : ℤ) : ConnectedSpace (Mk k) := by
  rw [connectedSpace_iff_univ, ← (clutchData k).range_ιX_union_range_ιY]
  exact IsConnected.union
    ⟨(clutchData k).ιX basePoint, ⟨basePoint, rfl⟩,
      ⟨clutchMap k basePoint, ((clutchData k).ιX_eq_ιY_iff.mpr ⟨basePoint_mem, rfl⟩).symm⟩⟩
    (isConnected_range (clutchData k).continuous_ιX)
    (isConnected_range (clutchData k).continuous_ιY)

end

end Submission.Milnor

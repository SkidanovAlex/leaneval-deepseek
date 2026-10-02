import Mathlib
import Submission.Work.Cohomology.StageSplitDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Cohomology

open Set

/-- If a finite family of closed connected sets `B i` (`i ∈ s`) has connected union, then any two
indices `a, b ∈ s` are joined by a chain of indices in `s` whose consecutive sets intersect.

The proof separates `s` into the indices reachable from `a` (in the "intersection graph") and the
rest; the corresponding unions of `B i` are two disjoint nonempty closed sets covering the
connected union, a contradiction. -/
theorem union_ball_chain {N : ℕ} {ι : Type} (s : Finset ι)
    (B : ι → Set (EuclideanSpace ℝ (Fin N)))
    (hclosed : ∀ i ∈ s, IsClosed (B i)) (hconn : ∀ i ∈ s, IsConnected (B i))
    (hU : IsConnected (⋃ i ∈ s, B i)) {a b : ι} (ha : a ∈ s) (hb : b ∈ s) :
    Relation.ReflTransGen (fun i j => i ∈ s ∧ j ∈ s ∧ (B i ∩ B j).Nonempty) a b := by
  classical
  let R : ι → ι → Prop := fun i j => i ∈ s ∧ j ∈ s ∧ (B i ∩ B j).Nonempty
  change Relation.ReflTransGen R a b
  by_contra hcon
  -- `C` = indices reachable from `a`, `D` = the remaining indices of `s`.
  set C : Finset ι := s.filter (fun i => Relation.ReflTransGen R a i) with hC
  set D : Finset ι := s.filter (fun i => ¬ Relation.ReflTransGen R a i) with hD
  set U : Set (EuclideanSpace ℝ (Fin N)) := ⋃ i ∈ C, B i with hUdef
  set V : Set (EuclideanSpace ℝ (Fin N)) := ⋃ i ∈ D, B i with hVdef
  have haC : a ∈ C := by rw [hC, Finset.mem_filter]; exact ⟨ha, Relation.ReflTransGen.refl⟩
  have hbD : b ∈ D := by rw [hD, Finset.mem_filter]; exact ⟨hb, hcon⟩
  have hBa : (B a).Nonempty := (hconn a ha).nonempty
  have hBb : (B b).Nonempty := (hconn b hb).nonempty
  -- `U` and `V` are finite unions of closed sets, hence closed.
  have hUc : IsClosed U := by
    rw [hUdef]
    exact isClosed_biUnion_finset
      (fun i hi => hclosed i (by rw [hC, Finset.mem_filter] at hi; exact hi.1))
  have hVc : IsClosed V := by
    rw [hVdef]
    exact isClosed_biUnion_finset
      (fun i hi => hclosed i (by rw [hD, Finset.mem_filter] at hi; exact hi.1))
  -- Every `B i` with `i ∈ s` lies in `U ∪ V`.
  have hsub : (⋃ i ∈ s, B i) ⊆ U ∪ V := by
    intro x hx
    simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨i, his, hxi⟩ := hx
    rw [hUdef, hVdef]
    by_cases hP : Relation.ReflTransGen R a i
    · left
      exact mem_iUnion.mpr
        ⟨i, mem_iUnion.mpr ⟨by rw [hC, Finset.mem_filter]; exact ⟨his, hP⟩, hxi⟩⟩
    · right
      exact mem_iUnion.mpr
        ⟨i, mem_iUnion.mpr ⟨by rw [hD, Finset.mem_filter]; exact ⟨his, hP⟩, hxi⟩⟩
  -- `U` and `V` are disjoint, by the definition of reachability.
  have hdisj : Disjoint U V := by
    rw [Set.disjoint_left]
    intro x hxU hxV
    rw [hUdef] at hxU
    rw [hVdef] at hxV
    simp only [mem_iUnion, exists_prop] at hxU hxV
    obtain ⟨i, hiC, hxi⟩ := hxU
    obtain ⟨j, hjD, hxj⟩ := hxV
    rw [hC, Finset.mem_filter] at hiC
    rw [hD, Finset.mem_filter] at hjD
    exact hjD.2 (hiC.2.tail ⟨hiC.1, hjD.1, ⟨x, hxi, hxj⟩⟩)
  -- Separation of the connected union `⋃ i ∈ s, B i` by the two closed disjoint sets `U`, `V`.
  have hs0cl : IsClosed (⋃ i ∈ s, B i) := isClosed_biUnion_finset hclosed
  have hsep := (isPreconnected_iff_subset_of_fully_disjoint_closed hs0cl).mp
      hU.isPreconnected U V hUc hVc hsub hdisj
  rcases hsep with hsubU | hsubV
  · obtain ⟨x, hxBb⟩ := hBb
    have hxU : x ∈ U := hsubU (mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hb, hxBb⟩⟩)
    have hxV : x ∈ V := by
      rw [hVdef]
      exact mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨hbD, hxBb⟩⟩
    exact (Set.disjoint_left.mp hdisj hxU) hxV
  · obtain ⟨x, hxBa⟩ := hBa
    have hxV : x ∈ V := hsubV (mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨ha, hxBa⟩⟩)
    have hxU : x ∈ U := by
      rw [hUdef]
      exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨haC, hxBa⟩⟩
    exact (Set.disjoint_left.mp hdisj hxU) hxV

end Work.Cohomology

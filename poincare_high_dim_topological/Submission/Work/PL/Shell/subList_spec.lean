import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Shell.Basic

/-!
# `Work.PL.Shell.subList_spec`

Basic facts about the vertex list `subList σ T = (T ∩ σ) ++ (σ \ T)` of a simplex `σ` with
splitting `T`, and about the induced rank `subRank σ T x = (subList σ T).idxOf x`.

These are the order-theoretic properties used to run the shelling argument: the list is
duplicate-free and enumerates exactly `σ`, the ranks increase along the list, and every
`T`-vertex is ranked below every vertex of `σ \ T`.
-/

namespace Work.PL.Shell

noncomputable section

variable {N : ℕ}

/-- For a nodup list `l`, the ranks of the elements of `l` (their positions in `l`) are
strictly increasing along `l`. -/
theorem pairwise_idxOf_self {α : Type*} [BEq α] [LawfulBEq α] {l : List α} (h : l.Nodup) :
    (l.map (fun x => l.idxOf x)).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [List.length_map] at hi hj
  rw [List.getElem_map, List.getElem_map]
  change List.idxOf (l.get ⟨i, hi⟩) l < List.idxOf (l.get ⟨j, hj⟩) l
  rw [List.get_idxOf h ⟨i, hi⟩, List.get_idxOf h ⟨j, hj⟩]
  exact hij

theorem subList_spec {σ T : Finset (PL.E N)} :
    (Work.PL.Shell.subList σ T).Nodup ∧ (Work.PL.Shell.subList σ T).toFinset = σ ∧
    ((Work.PL.Shell.subList σ T).map (Work.PL.Shell.subRank σ T)).Pairwise (· < ·) ∧
    (∀ u ∈ T, u ∈ σ → ∀ w ∈ σ, w ∉ T → Work.PL.Shell.subRank σ T u < Work.PL.Shell.subRank σ T w) := by
  set A : List (PL.E N) := (T.filter (fun x => x ∈ σ)).toList with hA
  set B : List (PL.E N) := (σ \ T).toList with hB
  -- `subList σ T` is the concatenation of the `T`-vertices with the remaining vertices.
  have hL : Work.PL.Shell.subList σ T = A ++ B := by
    simp only [Work.PL.Shell.subList]
    rw [← hA, ← hB]
  -- `subRank σ T x` is the position of `x` in that concatenation.
  have hLrank : ∀ x, Work.PL.Shell.subRank σ T x = (A ++ B).idxOf x := by
    intro x
    simp only [Work.PL.Shell.subRank, hL]
  have hAnodup : A.Nodup := by rw [hA]; exact Finset.nodup_toList _
  have hBnodup : B.Nodup := by rw [hB]; exact Finset.nodup_toList _
  -- The two blocks are disjoint: `A` consists of `T`-vertices, `B` of non-`T`-vertices.
  have hABdisj : ∀ a ∈ A, a ∉ B := by
    intro a ha hb
    rw [hA] at ha
    rw [hB] at hb
    rw [Finset.mem_toList, Finset.mem_filter] at ha
    rw [Finset.mem_toList, Finset.mem_sdiff] at hb
    exact hb.2 ha.1
  have hLnodup : (A ++ B).Nodup :=
    List.nodup_append.2 ⟨hAnodup, hBnodup, fun a ha b hb h => hABdisj a ha (h ▸ hb)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hL]; exact hLnodup
  · -- the underlying sets of the two blocks are `T ∩ σ` and `σ \ T`, whose union is `σ`.
    rw [hL, List.toFinset_append, hA, hB, Finset.toList_toFinset, Finset.toList_toFinset]
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
    tauto
  · -- the ranks are exactly the indices in the duplicate-free list `A ++ B`.
    rw [hL]
    have hmap : (A ++ B).map (Work.PL.Shell.subRank σ T) =
        (A ++ B).map (fun x => (A ++ B).idxOf x) :=
      List.map_congr_left (fun x _ => hLrank x)
    rw [hmap]
    exact pairwise_idxOf_self hLnodup
  · intro u huT huσ w hwσ hwT
    have huA : u ∈ A := by
      rw [hA, Finset.mem_toList, Finset.mem_filter]; exact ⟨huT, huσ⟩
    have hwB : w ∈ B := by
      rw [hB, Finset.mem_toList, Finset.mem_sdiff]; exact ⟨hwσ, hwT⟩
    have hwA : w ∉ A := by
      intro hw
      rw [hA, Finset.mem_toList, Finset.mem_filter] at hw
      exact hwT hw.1
    -- `u` sits in the first block, `w` in the second, so the rank of `u` is smaller.
    rw [hLrank u, hLrank w]
    rw [List.idxOf_append_of_mem huA, List.idxOf_append_of_notMem hwA]
    have h1 : A.idxOf u < A.length := List.idxOf_lt_length_of_mem huA
    omega

end

end Work.PL.Shell

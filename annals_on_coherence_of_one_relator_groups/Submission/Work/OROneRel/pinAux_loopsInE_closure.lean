/-
Copyright: subproject `OROneRel` -- one-relator combinatorics.

# Elementary bookkeeping for the decoration by the running weight

Small, self-contained list lemmas about `decor`, `lsig` and `coverEdge` that the "loop class
generation" and "pin" files use.  They complement `exists_treeGauge.decor_append'`,
`exists_treeGauge.decor_cons'` and `decor_invRev`.

* `decor_invRev_edges` : the edges of the reverse word, read from the level at which it starts, are
  the reversed edges of the original walk (in particular the *set* of edges is the same);
* `mem_decor_invRev` : its membership form;
* `mem_decor_append` : the decoration constraint is stable under concatenation.
-/
import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.bandLoopsDefs
import Submission.Work.OROneRel.decor_invRev

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The edges of the reverse word, read from the level at which it starts, are the reversed edges of
the original walk. -/
theorem decor_invRev_edges (c : α → ℤ) (W : List (α × Bool)) :
    (decor c (lsig c W) (FreeGroup.invRev W)).map coverEdge =
      ((decor c 0 W).map coverEdge).reverse := by
  have h := decor_invRev c (0 : ℤ) W
  rw [zero_add] at h
  rw [h, List.map_map, List.map_reverse]
  rfl

/-- Membership form of `decor_invRev_edges`. -/
theorem mem_decor_invRev {c : α → ℤ} {W : List (α × Bool)} {E : Set (α × ℤ)}
    (hW : ∀ p ∈ decor c 0 W, coverEdge p ∈ E) :
    ∀ p ∈ decor c (lsig c W) (FreeGroup.invRev W), coverEdge p ∈ E := by
  intro p hp
  have h : coverEdge p ∈ (decor c (lsig c W) (FreeGroup.invRev W)).map coverEdge :=
    List.mem_map.mpr ⟨p, hp, rfl⟩
  rw [decor_invRev_edges, List.mem_reverse, List.mem_map] at h
  obtain ⟨q, hq, hqe⟩ := h
  rw [← hqe]
  exact hW q hq

/-- Concatenation of the decoration constraints. -/
theorem mem_decor_append {c : α → ℤ} {E : Set (α × ℤ)} {i : ℤ} {L₁ L₂ : List (α × Bool)}
    (h₁ : ∀ p ∈ decor c i L₁, coverEdge p ∈ E)
    (h₂ : ∀ p ∈ decor c (i + lsig c L₁) L₂, coverEdge p ∈ E) :
    ∀ p ∈ decor c i (L₁ ++ L₂), coverEdge p ∈ E := by
  intro p hp
  rw [decor_append'] at hp
  rcases List.mem_append.mp hp with h | h
  · exact h₁ p h
  · exact h₂ p h

end Work.OROneRel

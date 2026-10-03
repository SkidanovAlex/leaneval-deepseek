import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.bandLoopsDefs
import Submission.Work.OROneRel.stbAssembly
import Submission.Work.OROneRel.pinAux_loopsInE_closure

/-!
# The loop class of an edge of `E` is a loop of `E`

For a weight `c : α → ℤ` and an edge set `E` of the level graph of the `ℤ`-cover,
`loopsInE c E` (`Submission.Work.OROneRel.bandLoopsDefs`) is the subgroup of `FreeGroup α` of the
loops whose *reduced* walk uses only edges of `E`.

Here we prove that the loop class `stbLoop Wt c (x,i) = Wt i * x * (Wt (i + c x))⁻¹` of an edge
`(x,i) ∈ E` lies in `loopsInE c E`, for a gauge `Wt` with `cohom c (Wt k) = ofAdd k`, provided the
walks of the tree paths to the two endpoints of the edge stay inside `E`: the hypotheses `hi` and
`hj` say that every decorated edge of `toWord (Wt i)` respectively of `toWord (Wt (i + c x))` is
in `E`.

The witnessing closed walk is

  `toWord (Wt i) ++ [(x, true)] ++ (toWord (Wt (i + c x)))⁻¹`,

the tree path from the level `0` to the level `i`, then the edge `(x,i)`, then the tree path back
from the level `i + c x` to the level `0`.  Its total weight is `i + c x - (i + c x) = 0`, and its
decorated edges are those of `toWord (Wt i)` (hypothesis `hi`), the edge `(x,i)` itself (hypothesis
`hE`), and — read backwards, hence the same set of edges — those of `toWord (Wt (i + c x))`
(hypothesis `hj`).  The closed-walk description `mem_loopsInE_iff` of `loopsInE` then gives the
claim.
-/

open Work.OROneRel

namespace Work.pinAux

/-! ## Two pieces of bookkeeping for the decorated walk -/

/-- The edge constraint of a walk is inherited by a concatenation of words: this is `decor_append`
read as a statement about the members of the decorated list. -/
private theorem stb_decor_edges_append {α : Type*} {c : α → ℤ} {E : Set (α × ℤ)} {i : ℤ}
    {L₁ L₂ : List (α × Bool)}
    (h₁ : ∀ p ∈ decor c i L₁, coverEdge p ∈ E)
    (h₂ : ∀ p ∈ decor c (i + lsig c L₁) L₂, coverEdge p ∈ E) :
    ∀ p ∈ decor c i (L₁ ++ L₂), coverEdge p ∈ E := by
  intro p hp
  rw [decor_append] at hp
  rcases List.mem_append.mp hp with h | h
  · exact h₁ p h
  · exact h₂ p h

/-- A word and its reverse traverse the same edges, so the constraint of a walk is inherited by the
reverse walk, read from the level reached at the end of the original word. -/
private theorem stb_decor_edges_invRev {α : Type*} {c : α → ℤ} {E : Set (α × ℤ)}
    {W : List (α × Bool)} (hW : ∀ p ∈ decor c 0 W, coverEdge p ∈ E) :
    ∀ p ∈ decor c (lsig c W) (FreeGroup.invRev W), coverEdge p ∈ E := by
  have hmap : (decor c (lsig c W) (FreeGroup.invRev W)).map coverEdge =
      ((decor c 0 W).map coverEdge).reverse := by
    have h0 := decor_invRev c (0 : ℤ) W
    rw [zero_add] at h0
    rw [h0, List.map_map, List.map_reverse]
    rfl
  intro p hp
  have h : coverEdge p ∈ ((decor c 0 W).map coverEdge).reverse := by
    rw [← hmap]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  rw [List.mem_reverse, List.mem_map] at h
  obtain ⟨q, hq, hqe⟩ := h
  rw [← hqe]
  exact hW q hq

/-! ## The statement -/

theorem stbLoop_mem_loopsInE {α : Type*} [DecidableEq α] (Wt : ℤ → FreeGroup α) (c : α → ℤ)
    {E : Set (α × ℤ)} {x : α} {i : ℤ}
    (hcoh : ∀ k : ℤ, Work.OROneRel.cohom c (Wt k) = Multiplicative.ofAdd k)
    (hE : (x, i) ∈ E)
    (hi : ∀ p ∈ Work.OROneRel.decor c 0 (FreeGroup.toWord (Wt i)), Work.OROneRel.coverEdge p ∈ E)
    (hj : ∀ p ∈ Work.OROneRel.decor c 0 (FreeGroup.toWord (Wt (i + c x))),
      Work.OROneRel.coverEdge p ∈ E) :
    Work.OROneRel.stbLoop Wt c (x, i) ∈ Work.OROneRel.loopsInE c E := by
  classical
  rw [mem_loopsInE_iff]
  refine ⟨FreeGroup.toWord (Wt i) ++ [(x, true)] ++
    FreeGroup.invRev (FreeGroup.toWord (Wt (i + c x))), ?_, ?_, ?_⟩
  · -- the closed walk represents the loop class of the edge
    show FreeGroup.mk (FreeGroup.toWord (Wt i) ++ [(x, true)] ++
        FreeGroup.invRev (FreeGroup.toWord (Wt (i + c x)))) =
      Wt i * FreeGroup.of x * (Wt (i + c x))⁻¹
    rw [stb_mk_append, stb_mk_append, stb_mk_cons_true, stb_mk_nil, FreeGroup.mk_toWord,
      stb_mk_invRev, FreeGroup.mk_toWord]
    simp only [mul_one, mul_assoc]
  · -- the walk is closed: its total weight vanishes
    rw [stb_lsig_append, stb_lsig_append, stb_lsig_invRev, stb_lsig_singleton_true,
      stb_lsig_toWord, stb_lsig_toWord, hcoh i, hcoh (i + c x)]
    simp only [toAdd_ofAdd]
    ring
  · -- every decorated edge of the walk lies in `E`
    refine stb_decor_edges_append (i := 0)
      (L₁ := FreeGroup.toWord (Wt i) ++ [(x, true)])
      (L₂ := FreeGroup.invRev (FreeGroup.toWord (Wt (i + c x)))) ?_ ?_
    · -- the tree path from `0` to `i`, and the edge `(x,i)` itself
      refine stb_decor_edges_append (i := 0)
        (L₁ := FreeGroup.toWord (Wt i)) (L₂ := [(x, true)]) ?_ ?_
      · intro p hp
        exact hi p hp
      · -- the edge `(x,i)` itself
        intro p hp
        have hls : lsig c (FreeGroup.toWord (Wt i)) = i := by
          rw [stb_lsig_toWord, hcoh i]
          rfl
        rw [show (0 : ℤ) + lsig c (FreeGroup.toWord (Wt i)) = i from by rw [hls]; ring,
          show decor c i [(x, true)] = [((x, i), true)] from rfl] at hp
        simp only [List.mem_singleton] at hp
        rw [hp]
        exact hE
    · -- the tree path back from the level `i + c x`, read backwards
      intro p hp
      have hls : lsig c (FreeGroup.toWord (Wt i)) = i := by
        rw [stb_lsig_toWord, hcoh i]
        rfl
      have hls2 : lsig c (FreeGroup.toWord (Wt (i + c x))) = i + c x := by
        rw [stb_lsig_toWord, hcoh (i + c x)]
        rfl
      rw [show (0 : ℤ) + lsig c (FreeGroup.toWord (Wt i) ++ [(x, true)]) =
          lsig c (FreeGroup.toWord (Wt (i + c x))) from by
        rw [stb_lsig_append, hls, stb_lsig_singleton_true, hls2]
        ring] at hp
      exact stb_decor_edges_invRev (W := FreeGroup.toWord (Wt (i + c x))) hj p hp

end Work.pinAux

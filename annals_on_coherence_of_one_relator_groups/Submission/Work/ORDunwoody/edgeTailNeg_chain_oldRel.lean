import Mathlib
import Submission.Work.ORDunwoody.colour_walk_defs
import Submission.Work.ORDunwoody.faceWalk_chain

universe u

namespace Work.ORDunwoody

theorem edgeTailNeg_chain_oldRel {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (a : G) (j : Fin P.n) :
    List.IsChain (Work.ORDunwoody.Dunwoody.oldRel D)
      (Work.ORDunwoody.Dunwoody.edgeTailNeg D a j) := by
  -- `oldRel` only constrains a step when *both* entries are old vertices.  The negative
  -- traversal visits `pattern point, old vertex, pattern point, old vertex, ...` (in that
  -- order along the edge), so every step has at least one pattern point and is therefore
  -- automatic: `oldRel_of_inr_left` for a step inside a cell, `oldRel_of_inr_right` for the
  -- step from one cell to the next.
  by_cases hL : D.L (j, true) = 0
  · -- collapsed generator edge: a single vertex, hence a chain
    simp only [Dunwoody.edgeTailNeg, if_pos hL]
    exact List.isChain_singleton _
  · simp only [Dunwoody.edgeTailNeg, if_neg hL]
    refine FaceWalkChain.isChain_flatMap_of_chain (Dunwoody.oldRel D)
      (fun k k' : Fin (D.L (j, true)) => (k : ℕ) = (k' : ℕ) + 1) ?_ ?_ ?_ ?_
    · -- the blocks are glued along consecutive indices
      rw [List.isChain_reverse, ← List.ofFn_id (D.L (j, true)), List.isChain_ofFn]
      intro i _
      rfl
    · intro k _
      simp
    · -- each block `[pattern point, old vertex]`
      intro k _
      exact List.IsChain.cons_cons
        (Dunwoody.oldRel_of_inr_left _ _)
        (List.isChain_singleton _)
    · -- junction between consecutive blocks: `pattern point, old vertex` again
      intro k _ k' _ hkk' x hx y hy
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some_iff] at hx
      simp only [List.head?_cons, Option.mem_some_iff] at hy
      subst hx
      subst hy
      exact Dunwoody.oldRel_of_inr_right _ _

end Work.ORDunwoody

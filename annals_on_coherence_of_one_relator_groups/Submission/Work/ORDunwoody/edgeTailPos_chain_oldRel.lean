import Mathlib
import Submission.Work.ORDunwoody.colour_walk_defs
import Submission.Work.ORDunwoody.faceWalk_chain

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Dunwoody Work.ORDunwoody.Cayley

/-- A list of "blocks" `[pattern point, old vertex]` is a chain for `oldRel`: any pair of
consecutive vertices has a pattern point as one of its two members, and `oldRel D v w` holds
as soon as `v` or `w` is a pattern point. -/
theorem isChain_oldRel_flatMap_blocks {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}
    {ι : Type*} (l : List ι) (m : ι → Work.ORDunwoody.Dunwoody.MidV D)
    (x : ι → Work.ORDunwoody.Dunwoody.BaseV D) :
    List.IsChain (Work.ORDunwoody.Dunwoody.oldRel D)
      (List.flatMap (fun i => [Sum.inr (m i), Sum.inl (x i)]) l) := by
  refine FaceWalkChain.isChain_flatMap_of_chain (Work.ORDunwoody.Dunwoody.oldRel D)
    (fun _ _ : ι => True) ?_ ?_ ?_ ?_
  · exact List.isChain_iff_getElem.mpr (fun i hi => trivial)
  · intro i _
    simp
  · intro i _
    exact List.IsChain.cons_cons (Dunwoody.oldRel_of_inr_left _ _) (List.isChain_singleton _)
  · intro i _ j _ _ y hy z hz
    simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some_iff] at hy
    simp only [List.head?_cons, Option.mem_some_iff] at hz
    subst hy
    subst hz
    exact Dunwoody.oldRel_of_inr_right _ _

theorem edgeTailPos_chain_oldRel {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P} (a : G) (j : Fin P.n) :
    List.IsChain (Work.ORDunwoody.Dunwoody.oldRel D)
      (Work.ORDunwoody.Dunwoody.edgeTailPos D a j) := by
  by_cases hL : D.L (j, true) = 0
  · rw [Dunwoody.edgeTailPos, if_pos hL]
    exact List.isChain_singleton _
  · rw [Dunwoody.edgeTailPos, if_neg hL]
    exact isChain_oldRel_flatMap_blocks (List.finRange (D.L (j, true)))
      (fun k => ⟨a, ⟨j, k⟩⟩) (fun k => pos D a j (k + 1))

end Work.ORDunwoody

import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic
import Submission.Work.ORBassSerre.Tree.IsTreeAPI

namespace Work.ORBassSerre.Tree.Seg

open Quiver

/-- In a tree, there is at most one arrow between any two vertices. -/
theorem arrow_unique {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hT : Work.ORBassSerre.IsTree V} (a b : V) (e f : a ⟶ b) : e = f := by
  have hpaths : e.toPath = f.toPath :=
    congrArg Subtype.val ((hT.subsingleton_isReduced a b).allEq
      (⟨e.toPath, Quiver.Path.IsReduced.of_length_lt_two (by simp)⟩ :
        {p : Quiver.Path a b // p.IsReduced})
      (⟨f.toPath, Quiver.Path.IsReduced.of_length_lt_two (by simp)⟩ :
        {p : Quiver.Path a b // p.IsReduced}))
  exact eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons hpaths)

/-- In a tree there is at most one arrow between any two vertices, so the arrows whose endpoints
both lie in a finite set of vertices form a finite set. -/
theorem exists_finset_arrows {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hT : Work.ORBassSerre.IsTree V} (K : Set V) (hK : K.Finite) :
    ∃ F : Finset (Quiver.Total V),
      ∀ e : Quiver.Total V, e.left ∈ K → e.right ∈ K → e ∈ F := by
  classical
  refine ⟨hK.toFinset.biUnion (fun a => hK.toFinset.biUnion (fun b =>
      if h : Nonempty (a ⟶ b) then {Quiver.Total.mk a b (Classical.choice h)} else ∅)), ?_⟩
  intro e he1 he2
  obtain ⟨a, b, f⟩ := e
  rw [Finset.mem_biUnion]
  refine ⟨a, (Set.Finite.mem_toFinset hK).mpr he1, ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨b, (Set.Finite.mem_toFinset hK).mpr he2, ?_⟩
  rw [dif_pos (⟨f⟩ : Nonempty (a ⟶ b)), Finset.mem_singleton]
  exact congrArg (Quiver.Total.mk a b) (arrow_unique (hT := hT) a b f (Classical.choice ⟨f⟩))

end Work.ORBassSerre.Tree.Seg

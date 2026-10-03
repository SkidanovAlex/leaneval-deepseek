import Mathlib
import Submission.Work.ORHughesFree.Tree
import Submission.Work.ORHughesFree.Tree.PermRel_of_multiset_map_mk
import Submission.Work.ORHughesFree.Tree.zero_mul

/-!
# Elementary properties of the family map `fam`

We prove that `fam` is injective, that it is additive, and record the characterisation of the
one-vertex tree by its (empty) family.
-/

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-- The family of a tree, read off from an explicit list of representatives. -/
noncomputable def cls (l : List MTree) : Multiset Tree :=
  Multiset.ofList (l.map (fun a => (Quotient.mk'' a : Tree)))

theorem fam_eq_cls (x : Tree) : fam x = cls (MTree.children (Quotient.out x)) := rfl

theorem cls_add (A B : List MTree) : cls (A ++ B) = cls A + cls B := by
  show Multiset.ofList ((A ++ B).map (fun a => (Quotient.mk'' a : Tree))) =
    Multiset.ofList (A.map (fun a => (Quotient.mk'' a : Tree))) +
    Multiset.ofList (B.map (fun a => (Quotient.mk'' a : Tree)))
  rw [List.map_append, Multiset.coe_add]

/-- The family of a sum is the sum of the families. -/
theorem fam_add (x y : Tree) : fam (x + y) = fam x + fam y := by
  have hiso : Iso (Quotient.out (x + y))
      (MTree.node (MTree.children (Quotient.out x) ++ MTree.children (Quotient.out y))) :=
    Quotient.exact (show (⟦Quotient.out (x + y)⟧ : Quotient isoSetoid) =
      ⟦MTree.node (MTree.children (Quotient.out x) ++
        MTree.children (Quotient.out y))⟧ from by
      rw [show (⟦Quotient.out (x + y)⟧ : Quotient isoSetoid) = x + y from
        Quotient.out_eq (x + y)]
      rfl)
  have hperm : PermRel (MTree.children (Quotient.out (x + y)))
      (MTree.children (MTree.node (MTree.children (Quotient.out x) ++
        MTree.children (Quotient.out y)))) := PermRel.of_iso_children hiso
  have h : cls (MTree.children (MTree.node (MTree.children (Quotient.out x) ++
      MTree.children (Quotient.out y)))) = fam x + fam y := by
    rw [show MTree.children (MTree.node (MTree.children (Quotient.out x) ++
        MTree.children (Quotient.out y))) =
        MTree.children (Quotient.out x) ++ MTree.children (Quotient.out y) from rfl]
    rw [cls_add, ← fam_eq_cls x, ← fam_eq_cls y]
  exact (fam_eq_cls _).trans ((PermRel.multiset_map_mk _ _ hperm).trans h)

/-- The one-vertex tree has empty family. -/
theorem fam_zero : fam (0 : Tree) = 0 := by
  rw [fam_eq_cls, zero_mul_children_out_zero]
  rfl

/-- A tree is determined by its family. -/
theorem fam_injective {x y : Tree} (h : fam x = fam y) : x = y := by
  have hperm : PermRel (MTree.children (Quotient.out x)) (MTree.children (Quotient.out y)) :=
    PermRel_of_multiset_map_mk h
  have key : ∀ t : MTree,
      (Quotient.mk'' t : Tree) = (Quotient.mk'' (MTree.node (MTree.children t)) : Tree) := by
    intro t; congr 1; cases t; rfl
  have hx : x = (Quotient.mk'' (MTree.node (MTree.children (Quotient.out x))) : Tree) :=
    (Quotient.out_eq x).symm.trans (key (Quotient.out x))
  have hy : (Quotient.mk'' (MTree.node (MTree.children (Quotient.out y))) : Tree) = y :=
    (key (Quotient.out y)).symm.trans (Quotient.out_eq y)
  exact hx.trans ((Quotient.sound (Iso.node hperm)).trans hy)

/-- A tree is the one-vertex tree if and only if its family is empty. -/
theorem fam_eq_zero_iff {x : Tree} : fam x = 0 ↔ x = 0 :=
  ⟨fun h => fam_injective (by rw [h, fam_zero]), fun h => by rw [h, fam_zero]⟩

/-- A tree is nonzero if and only if its family is nonempty. -/
theorem ne_zero_iff_fam_ne_zero {x : Tree} : x ≠ 0 ↔ fam x ≠ 0 :=
  ⟨fun h hf => h (fam_eq_zero_iff.mp hf), fun h hx => h (fam_eq_zero_iff.mpr hx)⟩

end Work.ORHughesFree.Tree

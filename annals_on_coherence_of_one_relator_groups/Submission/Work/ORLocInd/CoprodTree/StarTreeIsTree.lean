/-
# The graph of the free product is a tree

Combining the connectivity of the Bass--Serre graph of the free product
(`starTree_connected`) with the fact that it has no non-trivial reduced closed path
(`eq_nil_of_inv_none`, `eq_nil_of_inv_some`), we obtain `Work.ORBassSerre.IsTree` for it.
-/
import Submission.Work.ORLocInd.CoprodTree.StarTreeTree
import Submission.Work.ORLocInd.CoprodTree.starTree_connected
import Submission.Work.ORLocInd.CoprodTree.inv_of_isReduced
import Submission.Work.ORLocInd.CoprodTree.eq_nil_of_inv_some

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.CoprodTree

open Quiver
open Work.ORBassSerre
open Classical

variable {ι : Type u}

/-- A reduced closed path in the graph is trivial. -/
theorem eq_nil_of_isReduced_of_inv {M : ι → Type u} [∀ i, Group (M i)] {k : Option ι}
    {g : Monoid.CoprodI M} {p : Quiver.Path (vtx k g) (vtx k g)}
    (hp : p.IsReduced) (hinv : Inv k g p) : p = Quiver.Path.nil := by
  match k with
  | none => exact eq_nil_of_inv_none hp hinv
  | some i => exact eq_nil_of_inv_some hp hinv

/-- **The graph of the free product has no non-trivial reduced closed path.** -/
theorem no_nontrivial_reduced_cycle {M : ι → Type u} [∀ i, Group (M i)] (x : Vertex M)
    (p : Quiver.Path x x) (hp : p.IsReduced) : p = Quiver.Path.nil := by
  obtain ⟨k, g, rfl⟩ := exists_vtx x
  exact eq_nil_of_isReduced_of_inv hp (inv_of_isReduced p hp)

/-- **The Bass--Serre graph of a free product is a tree.** -/
theorem starTree_isTree {M : ι → Type u} [∀ i, Group (M i)] : IsTree (Vertex M) :=
  ⟨fun a b => starTree_connected a b, fun a p hp => no_nontrivial_reduced_cycle a p hp⟩

end Work.ORLocInd.CoprodTree

import Mathlib
import Submission.Work.PL.Defs

namespace Work.Cells.Connell

open Set

/-- A cube chart is injective on the open unit cube: it is an open embedding of that cube into
`M`, and an embedding is injective. -/
theorem cubeChart_injOn {n : ℕ} {M : Type*} [TopologicalSpace M] (c : PL.CubeChart n M) :
    Set.InjOn c.toFun (PL.openCube (n := n) 1) := by
  intro x hx y hy hxy
  have hinj : Function.Injective ((PL.openCube (n := n) 1).domRestrict c.toFun) :=
    c.emb.toIsEmbedding.injective
  have h1 : (⟨x, hx⟩ : ↥(PL.openCube (n := n) 1)) = ⟨y, hy⟩ := by
    apply hinj
    exact hxy
  exact congrArg Subtype.val h1

end Work.Cells.Connell

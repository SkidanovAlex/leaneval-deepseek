import Mathlib

/-!
# Functoriality of the homotopy groups

Mathlib defines `HomotopyGroup N X x` as the quotient of the generalized loops
`Ω^ N X x = GenLoop N X x` by the relation "homotopic relative to the boundary", and equips it
with a group structure when `N` is nonempty, but it does **not** provide the functoriality of this
construction.  This file supplies it:

* `HomotopyGroup.map f : HomotopyGroup N X x → HomotopyGroup N Y (f x)` — postcomposition with a
  continuous map;
* `HomotopyGroup.map_id`, `HomotopyGroup.map_comp` — functoriality.

These are the minimum tools needed to compare homotopy groups of different spaces (for instance to
transport a computation performed on a convenient model space, or to make sense of "the map
`πₙ(X) → πₙ(K(ℤ,n))`" in a Hurewicz/Postnikov argument).  They belong to the `STEMS` area
(`Submission/Work/Stems/`), whose target is `Work.Drive.StableStemsTorsion`.
-/

open scoped Topology Topology.Homotopy
open ContinuousMap

namespace HomotopyGroup

variable {N X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {x : X}

/-- The map `πₙ(X) → πₙ(Y)` induced by a continuous map `f : X → Y`. -/
def map (f : C(X, Y)) : HomotopyGroup N X x → HomotopyGroup N Y (f x) :=
  Quotient.map
    (fun p : Ω^ N X x =>
      (⟨f.comp p.1, fun y hy => by rw [ContinuousMap.comp_apply, p.2 y hy]⟩ : Ω^ N Y (f x)))
    (fun _ _ h => h.comp_continuousMap f)

theorem map_mk (f : C(X, Y)) (p : Ω^ N X x) :
    map f ⟦p⟧ = ⟦(⟨f.comp p.1, fun y hy => by rw [ContinuousMap.comp_apply, p.2 y hy]⟩ :
      Ω^ N Y (f x))⟧ :=
  rfl

theorem map_id (a : HomotopyGroup N X x) : map (ContinuousMap.id X) a = a := by
  induction a using Quotient.inductionOn with
  | h p => rfl

theorem map_comp (f : C(X, Y)) (g : C(Y, Z)) (a : HomotopyGroup N X x) :
    map (g.comp f) a = map g (map f a) := by
  induction a using Quotient.inductionOn with
  | h p => rfl

end HomotopyGroup

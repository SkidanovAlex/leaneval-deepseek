import Mathlib

/-!
# Staircase cells attached to a finite family of "level" sets

Let `ι` be a finite index type with an enumeration `e : ι ≃ Fin (Fintype.card ι)`, and let
`U C : ι → Set X` be two families of sets.  We think of `U i` as an *open* set (`c < Φ i`) and
of `C i = (U i)ᶜ` as its complement (`Φ i ≤ c`).

* `levelCell e U C m` is the `m`-th "staircase" cell: the part of `U (e.symm m)` lying outside
  every earlier `U (e.symm j)`, `j < m`.
* `levelCore C` is the residual set `⋂ i, C i`, i.e. the set of points on which *all* the
  functions are `≤ c`.

The cells are pairwise disjoint, each is contained in a single `U i`, and together with the core
they cover all of `X`; these facts are what turns a null-frontier cover of `X` into a finite
partition all of whose atoms have null frontier.
-/

namespace Work.EKLComp

open Set

/-- The `m`-th cell of the staircase associated with the families `U` (open) and `C` (closed),
enumerated by `e`.  It consists of the points of `U (e.symm m)` which are in no earlier `U`. -/
def levelCell {X ι : Type*} [Fintype ι] (e : ι ≃ Fin (Fintype.card ι)) (U C : ι → Set X)
    (m : Fin (Fintype.card ι)) : Set X :=
  U (e.symm m) ∩ ⋂ j : {j : Fin (Fintype.card ι) // j < m}, C (e.symm j.1)

/-- The residual set `⋂ i, C i`: the points lying in none of the `U i` (when `C i = (U i)ᶜ`). -/
def levelCore {X ι : Type*} (C : ι → Set X) : Set X := ⋂ i, C i

end Work.EKLComp

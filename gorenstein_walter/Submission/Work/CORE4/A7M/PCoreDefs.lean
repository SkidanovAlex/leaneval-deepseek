/-
Copied from `Submission/Work/A7F/pCore_defs.lean` with the import list adapted to the
CORE4 world (see the note below); the `Work.A7F` content is unchanged.

**Why a copy:**  the areas of this workspace each carry their own verbatim copy of the `Work.GW2`
vocabulary (`Contracts2.lean`), and two of them cannot be imported into one environment
(`environment already contains 'Work.GW2.A7ModelProp'`).  This file therefore takes the
`Work.GW2` vocabulary from `Submission.Work.CORE4.Defs` and imports `Submission.Work.A7.Defs`
(clash-free) instead of `Submission.Work.A7F.Defs`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.A7.Defs
import Submission.Work.CORE4.A7M.Defs
import Submission.Work.CORE4.A7M.Four

open scoped MatrixGroups

namespace Work.A7F

open Subgroup

/-! ## The extra involutions -/

/-- The involution `(2 3)(5 6)` of `A₇`. -/
def a7y : alternatingGroup (Fin 7) := Work.A7.a7Dswap 2 3 5 6 (by decide) (by decide)

/-- The involution `(2 3)(4 5)` of `A₇`. -/
def a7z : alternatingGroup (Fin 7) := Work.A7.a7Dswap 2 3 4 5 (by decide) (by decide)

/-! ## The carrier predicates -/

/-- The eight elements of `V₁ ∪ (2 3)(5 6)·V₁`. -/
def inS (z : alternatingGroup (Fin 7)) : Prop :=
  z = 1 ∨ z = a7Invol ∨ z = a7D1 ∨ z = a7Invol * a7D1 ∨
    z = a7y ∨ z = a7y * a7Invol ∨ z = a7y * a7D1 ∨ z = a7y * (a7Invol * a7D1)

/-- The eight elements of `V₁ ∪ (2 3)(4 5)·V₁`. -/
def inS2 (z : alternatingGroup (Fin 7)) : Prop :=
  z = 1 ∨ z = a7Invol ∨ z = a7D1 ∨ z = a7Invol * a7D1 ∨
    z = a7z ∨ z = a7z * a7Invol ∨ z = a7z * a7D1 ∨ z = a7z * (a7Invol * a7D1)

/-- The four elements of `V₁`. -/
def inV1 (z : alternatingGroup (Fin 7)) : Prop :=
  z = 1 ∨ z = a7Invol ∨ z = a7D1 ∨ z = a7Invol * a7D1

/-! ## The explicit Sylow subgroups -/

/-- The Sylow `2`-subgroup `V₁ ∪ (2 3)(5 6)·V₁` of `C_{A₇}(t)`, as an explicit eight element
subgroup. -/
def a7S : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {z | inS z}
  mul_mem' := by
    intro x y hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Set.mem_setOf_eq, inS] <;> decide
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Set.mem_setOf_eq, inS] <;> decide

/-- The Sylow `2`-subgroup `V₁ ∪ (2 3)(4 5)·V₁` of `C_{A₇}(t)`, as an explicit eight element
subgroup. -/
def a7S2 : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {z | inS2 z}
  mul_mem' := by
    intro x y hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Set.mem_setOf_eq, inS2] <;> decide
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Set.mem_setOf_eq, inS2] <;> decide

/-! ## Membership -/

theorem mem_a7S {z : alternatingGroup (Fin 7)} : z ∈ a7S ↔ inS z := Iff.rfl

theorem mem_a7S2 {z : alternatingGroup (Fin 7)} : z ∈ a7S2 ↔ inS2 z := Iff.rfl

theorem inV1_iff_mem_a7V1 {z : alternatingGroup (Fin 7)} : inV1 z ↔ z ∈ a7V1 := by
  rw [Work.A7F.mem_a7V1]
  rfl

theorem mem_a7V1_iff {z : alternatingGroup (Fin 7)} : z ∈ a7V1 ↔ inV1 z :=
  inV1_iff_mem_a7V1.symm

/-! ## The cardinalities -/

theorem card_a7S : Nat.card a7S = 8 := by
  have h1 : Nat.card a7S = ({z : alternatingGroup (Fin 7) | inS z} : Set _).ncard :=
    Nat.card_coe_set_eq _
  rw [h1]
  have hset : ({z : alternatingGroup (Fin 7) | inS z} : Set _) =
      ↑({1, a7Invol, a7D1, a7Invol * a7D1, a7y, a7y * a7Invol, a7y * a7D1,
          a7y * (a7Invol * a7D1)} : Finset (alternatingGroup (Fin 7))) := by
    ext z; simp [inS]
  rw [hset, Set.ncard_coe_finset]
  decide

theorem card_a7S2 : Nat.card a7S2 = 8 := by
  have h1 : Nat.card a7S2 = ({z : alternatingGroup (Fin 7) | inS2 z} : Set _).ncard :=
    Nat.card_coe_set_eq _
  rw [h1]
  have hset : ({z : alternatingGroup (Fin 7) | inS2 z} : Set _) =
      ↑({1, a7Invol, a7D1, a7Invol * a7D1, a7z, a7z * a7Invol, a7z * a7D1,
          a7z * (a7Invol * a7D1)} : Finset (alternatingGroup (Fin 7))) := by
    ext z; simp [inS2]
  rw [hset, Set.ncard_coe_finset]
  decide

end Work.A7F

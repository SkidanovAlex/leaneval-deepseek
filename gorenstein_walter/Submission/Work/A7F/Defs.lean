/-
Area A7F of the Gorenstein--Walter project: the model facts on `A₇` (Bender 1.8).

This is the interface file of the area.  It contains

* verbatim copies (from `Submission/Work/_design_gw/Contracts2.lean`) of the definitions of the
  contract vocabulary that the model facts mention, in namespace `Work.GW2` -- in particular
  `Work.GW2.A7ModelProp`, the deliverable Prop of this area;
* the concrete model elements and subgroups of `A₇` used throughout the area.

The main results live in `Submission/Work/A7F/Model.lean`
(`Work.A7F.a7ModelProp : Work.GW2.A7ModelProp`) and `Submission/Work/A7F/Api.lean`.
-/
import Mathlib
import Submission.Work.A7.Defs
import Submission.Work.ASM.Defs

open scoped MatrixGroups

namespace Work.GW2

open Subgroup

/-! ## The contract's vocabulary, verbatim -/


end Work.GW2

namespace Work.A7F

open Subgroup

/-! ## The model elements of `A₇` -/

/-- The `4`-cycle `(0 1 2 3)(5 6)` of `Equiv.Perm (Fin 7)`. -/
def a7FourCyclePerm : Equiv.Perm (Fin 7) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 5 6

/-- The `7`-cycle `(0 1 2 3 4 5 6)` of `Equiv.Perm (Fin 7)`. -/
def a7SevenCyclePerm : Equiv.Perm (Fin 7) :=
  Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5 *
    Equiv.swap 5 6

/-- The element `(0 1 2 3)(5 6)` of `A₇`. -/
def a7FourCycle : alternatingGroup (Fin 7) :=
  ⟨a7FourCyclePerm, by
    rw [Equiv.Perm.mem_alternatingGroup, a7FourCyclePerm, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide⟩

@[simp]
theorem coe_a7FourCycle :
    ((a7FourCycle : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) = a7FourCyclePerm := rfl

/-- The element `(0 1 2 3 4 5 6)` of `A₇`. -/
def a7SevenCycle : alternatingGroup (Fin 7) :=
  ⟨a7SevenCyclePerm, by
    rw [Equiv.Perm.mem_alternatingGroup, a7SevenCyclePerm, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide), Equiv.Perm.sign_swap (by decide)]
    decide⟩

@[simp]
theorem coe_a7SevenCycle :
    ((a7SevenCycle : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) = a7SevenCyclePerm := rfl

/-- The Klein four-group `V₁ = {1, (01)(23), (02)(13), (03)(12)}` of `A₇`, containing the model
involution `t = a7Invol`. -/
abbrev a7V1 : Subgroup (alternatingGroup (Fin 7)) := Work.A7.a7V1

/-- The Klein four-group `V₂ = {1, (01)(23), (01)(45), (23)(45)}` of `A₇`. -/
abbrev a7V2 : Subgroup (alternatingGroup (Fin 7)) := Work.A7.a7V2

/-- `K = O(C_{A₇}(t)) = ⟨(4 5 6)⟩`. -/
abbrev a7K : Subgroup (alternatingGroup (Fin 7)) := Work.A7.a7K

/-- The model involution `t = (0 1)(2 3)` of `A₇`. -/
abbrev a7Invol : alternatingGroup (Fin 7) := Work.A7.a7Invol

/-- A concrete Sylow `2`-subgroup of `A₇`: `⟨(0 1 2 3)(5 6), (0 1)(2 3)⟩`, isomorphic to
`DihedralGroup 4` (the dihedral group of order `8`). -/
def a7S0 : Subgroup (alternatingGroup (Fin 7)) :=
  Subgroup.closure ({a7FourCycle, a7Invol} : Set (alternatingGroup (Fin 7)))

/-- The Sylow `7`-subgroup `⟨(0 1 2 3 4 5 6)⟩` of `A₇`. -/
def a7C7 : Subgroup (alternatingGroup (Fin 7)) := Subgroup.zpowers a7SevenCycle

/-- The `105` nontrivial involutions of `A₇`, as a `Finset`. -/
def a7InvSet : Finset (alternatingGroup (Fin 7)) :=
  Finset.univ.filter (fun t => t ≠ 1 ∧ t * t = 1)

/-- The `A₇`-conjugacy class of `x`, as a `Finset`. -/
def a7ConjClass (x : alternatingGroup (Fin 7)) : Finset (alternatingGroup (Fin 7)) :=
  Finset.image (fun g => g * x * g⁻¹) Finset.univ

end Work.A7F

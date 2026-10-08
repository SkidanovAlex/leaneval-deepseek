/-
Area AUTA7 of the Gorenstein--Walter project: the exceptional group `A₇`.

This file sets up the vocabulary of the area and copies, verbatim, the Prop
`AutA7Prop` from the design contract `Submission/Work/_design_gw/Contracts2.lean`
into the namespace `Work.GW2`.

Main results of the area (see `Submission/Work/AUTA7/Main.lean`):

* `Work.GW2.AutA7Prop` : a finite group `Q` with a normal subgroup `L ≅ A₇` with
  trivial centralizer and with cyclic-or-dihedral Sylow 2-subgroups satisfies `L = ⊤`;
  in particular `A₇` has no such proper overgroup.

Supporting structural facts about `A₇` itself live in
`Submission/Work/AUTA7/A7/Basic.lean`.
-/
import Mathlib
import Submission.Work.A7.Defs
import Submission.Work.ASM.Defs

open scoped MatrixGroups

/-! ## The contract, copied verbatim from `_design_gw/Contracts2.lean` -/

namespace Work.GW2


/-- **AUTA7, even index case** (design3 §4): a group `Q` with a normal subgroup `L ≅ A₇`, with
`C_Q(L) = 1` and cyclic-or-dihedral Sylow 2-subgroups cannot have `L` of even index.
Copied verbatim (up to namespace) from `_design_gw/Core3.lean`. -/
def AutA7EvenIndexProp : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L : Subgroup Q), L.Normal →
    Nonempty (L ≃* alternatingGroup (Fin 7)) → Subgroup.centralizer (L : Set Q) = ⊥ →
    DihOrCycSylow Q → ¬ 2 ∣ L.index

/-- **AUTA7, odd index case** (design3 §4): in the same situation, `L` of odd index forces `L = ⊤`.
Copied verbatim (up to namespace) from `_design_gw/Core3.lean`. -/
def AutA7OddIndexProp : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L : Subgroup Q), L.Normal →
    Nonempty (L ≃* alternatingGroup (Fin 7)) → Subgroup.centralizer (L : Set Q) = ⊥ →
    DihOrCycSylow Q → Odd L.index → L = ⊤

/-! ### Supporting A₇ facts (copied verbatim from `_design_gw/Core3.lean`) -/

/-- Every involution `z` of `A₇` has `|C(z)| = 24` and a normal subgroup `K` of order `3` (the
unique one), with `|C(K)| = 36`, `|N(K)| = 72`, all `2`-subgroups of `C(K)` of order `≤ 4` and no
element of order `4` in `C(K)`. -/
def A7InvolutionLocalProp : Prop :=
  ∀ z : alternatingGroup (Fin 7), orderOf z = 2 →
    Nat.card (Subgroup.centralizer ({z} : Set (alternatingGroup (Fin 7)))) = 24 ∧
    ∃ K : Subgroup (alternatingGroup (Fin 7)),
      K ≤ Subgroup.centralizer ({z} : Set _) ∧
        (K.subgroupOf (Subgroup.centralizer ({z} : Set _))).Normal ∧
      Nat.card K = 3 ∧ Nat.card (Subgroup.centralizer (K : Set (alternatingGroup (Fin 7)))) = 36 ∧
      Nat.card (Subgroup.normalizer (K : Set (alternatingGroup (Fin 7)))) = 72 ∧
      (∀ P : Subgroup (alternatingGroup (Fin 7)),
        P ≤ Subgroup.centralizer (K : Set _) → IsPGroup 2 P → Nat.card P ≤ 4) ∧
      ∀ x ∈ Subgroup.centralizer (K : Set (alternatingGroup (Fin 7))), orderOf x ≠ 4

/-- A Sylow `2`-subgroup `D ≅ D₈` of `A₇` is self-normalizing, and the centralizers of its
involutions generate `A₇`. -/
def A7SylowFactsProp : Prop :=
  ∀ D : Sylow 2 (alternatingGroup (Fin 7)),
    Subgroup.normalizer ((D : Subgroup (alternatingGroup (Fin 7))) : Set (alternatingGroup (Fin 7)))
        = D ∧
    (⨆ (z : alternatingGroup (Fin 7))
        (_ : z ∈ (D : Subgroup (alternatingGroup (Fin 7))))
        (_ : orderOf z = 2), Subgroup.centralizer ({z} : Set (alternatingGroup (Fin 7)))) = ⊤

/-- In `D₁₆` (`DihedralGroup 8`), two distinct subgroups of order `8` meet in a cyclic group. -/
def D16MaxIntersectProp : Prop :=
  ∀ T₁ T₂ : Subgroup (DihedralGroup 8), Nat.card T₁ = 8 → Nat.card T₂ = 8 → T₁ ≠ T₂ →
    IsCyclic (T₁ ⊓ T₂ : Subgroup (DihedralGroup 8))

end Work.GW2

/-! ## The area's own vocabulary -/

namespace Work.AUTA7

open Subgroup

variable {G : Type*} [Group G]

/-- A Klein four-group: a subgroup of order `4` all of whose elements are involutions.
(This is the same predicate as `GW2.IsFourGroup` of the design contract.) -/
def IsV4 (V : Subgroup G) : Prop := Nat.card V = 4 ∧ ∀ v ∈ V, v ^ 2 = 1

/-- The model involution `t = (0 1)(2 3)` of `A₇` (as in `Work.A7`). -/
abbrev a7Invol : alternatingGroup (Fin 7) := Work.A7.a7Invol

end Work.AUTA7

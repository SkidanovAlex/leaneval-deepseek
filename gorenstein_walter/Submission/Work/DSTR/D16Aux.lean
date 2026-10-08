/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DSTR area (fundmath3-gorenstein_walter), `Work.DSTR.d16`

# Splitting Bender 1.6 (`Work.GW2.D16Prop`) into the four cases of `DShape`

`Work.GW2.D16Prop` says: for a finite group `X` with dihedral-or-cyclic Sylow 2-subgroups and
one of Bender's four shapes for `X/O(X)`, one of the following holds

* **(a)** `C_X(F_{2'}(X)) ≤ F_{2'}(X)`,
* **(b)** `X` has a central involution,
* **(c)** `O_2(X)` is a four-group and `X/(O_2(X)·O(X))` is `C₃` or `D₃`,
* **(d)** `X` has a normal quasisimple subgroup `E` with `X/E` solvable.

This file introduces the four clauses `d16a`–`d16d` as transparent abbreviations (so that the
assembly can reason about them) and the three case statements `D16Case1Prop`, `D16Case2Prop`,
`D16Case34Prop` into which the proof splits, according to which clause of `DShape` holds:

* `D16Case1Prop` — `X/O(X)` is a `2`-group;
* `D16Case2Prop` — `X/O(X)` is not a `2`-group but has a self-centralizing normal four-group;
* `D16Case34Prop` — `X/O(X)` is `A₇` or has a normal `L₂(q)` or `PGL₂(q)` of odd index.

The assembly in `Submission/Work/DSTR/d16.lean` is then a four-way case split on `DShape`,
using the three case lemmas proved in `Submission/Work/DSTR/D16/`.
-/
import Mathlib
import Submission.Work.DSTR.Defs

open scoped MatrixGroups

namespace Work.DSTR

open Subgroup

/-- `F_{2'}(X) = O_{2'}(F(X))`, the `2'`-part of the Fitting subgroup, in the notation of
Bender 1.6. -/
abbrev F2p (X : Type) [Group X] : Subgroup X := Work.GW2.fittingPi ({2}ᶜ : Set ℕ) X

/-- **Bender 1.6 (a)**: `C_X(F_{2'}(X)) ≤ F_{2'}(X)`. -/
abbrev d16a (X : Type) [Group X] : Prop :=
  Subgroup.centralizer ((F2p X : Subgroup X) : Set X) ≤ F2p X

/-- **Bender 1.6 (b)**: `X` has a central involution. -/
abbrev d16b (X : Type) [Group X] : Prop :=
  ∃ z : X, z ∈ Subgroup.center X ∧ orderOf z = 2

/-- **Bender 1.6 (c)**: `O_2(X)` is of type `(2,2)` and `X/(O_2(X)·O(X))` is `Z₃` or `D₃`. -/
abbrev d16c (X : Type) [Group X] : Prop :=
  Work.GW2.IsFourGroup (Work.GW2.pCore 2 X) ∧
    ((IsCyclic (X ⧸ (Work.GW2.pCore 2 X ⊔ Work.GW2.oddCore X)) ∧
        Nat.card (X ⧸ (Work.GW2.pCore 2 X ⊔ Work.GW2.oddCore X)) = 3) ∨
      Nonempty ((X ⧸ (Work.GW2.pCore 2 X ⊔ Work.GW2.oddCore X)) ≃* DihedralGroup 3))

/-- **Bender 1.6 (d)**: `X` has a normal quasisimple subgroup `E` with `X/E` solvable. -/
abbrev d16d (X : Type) [Group X] : Prop :=
  ∃ E : Subgroup X, ∃ _ : E.Normal, Work.GW2.IsQuasisimple E ∧ Group.IsSolvable (X ⧸ E)

/-- **Case 1 of Bender 1.6**: `O(X)` is a `2`-group complement, i.e. `X/O(X)` is a `2`-group.
Then `X` is solvable and clauses (a) or (b) hold. -/
abbrev D16Case1Prop : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Work.GW2.FeitThompsonProp → Work.GW2.DihOrCycSylow X →
    IsPGroup 2 (X ⧸ Work.GW2.oddCore X) → d16a X ∨ d16b X

/-- **Case 2 of Bender 1.6**: `X/O(X)` is *not* a `2`-group but has a normal four-group `V` with
`C_{X/O(X)}(V) = V`.  Then clauses (a), (b) or (c) hold. -/
abbrev D16Case2Prop : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Work.GW2.FeitThompsonProp → Work.GW2.DihOrCycSylow X →
    ¬ IsPGroup 2 (X ⧸ Work.GW2.oddCore X) →
    (∃ V : Subgroup (X ⧸ Work.GW2.oddCore X), V.Normal ∧ Work.GW2.IsFourGroup V ∧
      Subgroup.centralizer (V : Set (X ⧸ Work.GW2.oddCore X)) = V) →
    d16a X ∨ d16b X ∨ d16c X

/-- **Cases 3 and 4 of Bender 1.6**: `X/O(X)` is `A₇`, or has a normal subgroup of odd index
isomorphic to `L₂(q)` or `PGL₂(q)` for some odd prime power `q ≥ 5`.  Then clauses (a), (b) or
(d) hold. -/
abbrev D16Case34Prop : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Work.GW2.FeitThompsonProp → Work.GW2.DihOrCycSylow X →
    (Nonempty ((X ⧸ Work.GW2.oddCore X) ≃* alternatingGroup (Fin 7)) ∨
      (∃ L : Subgroup (X ⧸ Work.GW2.oddCore X), L.Normal ∧ Odd L.index ∧ ∃ p k : ℕ,
        ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
        (Nonempty (L ≃* PSL(2, GaloisField p k)) ∨
          Nonempty (L ≃* PGL(2, GaloisField p k))))) →
    d16a X ∨ d16b X ∨ d16d X

end Work.DSTR

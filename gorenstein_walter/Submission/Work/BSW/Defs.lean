/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, `Work.BSW`)

# Area BSW: the Brauer–Suzuki–Wall theorem (Bender 1974)

This is the vocabulary file of area `BSW` of the Gorenstein–Walter project.  The area
implements the recognition step `Work.GW2.BSW2Prop` of the blueprint
(`Submission/Work/NOTES_LEAD_gw_blueprint2.md`, area `BSW`; `Submission/Work/NOTES_LEAD_gw_design2.md`
§7), following

> H. Bender, *The Brauer–Suzuki–Wall theorem*, Illinois J. Math. **18** (1974) 229–235
> (`REFS/bender1974_bsw.txt`) together with
> H. Bender, *Finite groups with large subgroups*, Illinois J. Math. **18** (1974) 223–228
> (`REFS/bender1974_large.txt`) for the `|K| = 4` case.

The theorem recognized is the one of Brauer, Suzuki and Wall (1958):

a finite group `G` with an involution `t` and an abelian subgroup `K ≤ C_G(t)` containing `t`,
such that `C_G(t) = K⟨s⟩` with an involution `s ∉ K` inverting `K`, `K` TI with respect to
`C_G(t)`, and all involutions of `G` conjugate, is `PSL(2, q)`: more precisely it carries a
Zassenhaus action on the cosets of some subgroup.

## Contents

* Helpers `conjSub`, `involutionSet`, `OneInvClassIn`, `Inverts`, `cosetInvCount`, `bCount` and
  the four `Prop`s `ZassHyps2`, `ZassOdd2Prop`, `BSWHyps2`, `BSWZass2Prop`, `BSW2Prop`, copied
  **verbatim** from the design file `Submission/Work/_design_gw/Core2.lean` (namespace `GW2`
  there, `Work.GW2` here, as requested by the lead), so that this area can be composed with the
  other areas.  The library file `Submission/Work/BSW/Basic.lean` develops the API of
  `BSWHyps2`; `Submission/Work/BSW/Cases.lean` holds the intermediate `Prop`s of Bender's proof
  (`Work.BSW.BSWCaseProp` and friends) and `Submission/Work/BSW/Main.lean` the assembly
  `Work.BSW.bsw2 : BSWZass2Prop → ZassOdd2Prop → BSW2Prop`.

Nothing here depends on the odd-order library: this file imports Mathlib only.
-/
import Mathlib

open scoped MatrixGroups

namespace Work.GW2

open Subgroup

section Helpers

variable {G : Type*} [Group G]

/-- `K^g = g K g⁻¹`. -/
def conjSub (g : G) (K : Subgroup G) : Subgroup G := K.map (MulAut.conj g).toMonoidHom

/-- Involutions lying in `K`. -/
def involutionSet (K : Subgroup G) : Set G := {x | x ∈ K ∧ orderOf x = 2}

/-- `K` has one class of involutions under `K`-conjugation. -/
def OneInvClassIn (K : Subgroup G) : Prop :=
  ∀ x ∈ involutionSet K, ∀ y ∈ involutionSet K, ∃ g ∈ K, g * x * g⁻¹ = y

/-- `s` inverts every element of `K`. -/
def Inverts (s : G) (K : Subgroup G) : Prop := ∀ x ∈ K, s * x * s⁻¹ = x⁻¹

/-- Number of involutions in the left coset `g Ĥ`. Bender uses right cosets; inversion
swaps the two counts. -/
noncomputable def cosetInvCount (Hh : Subgroup G) (g : G) : ℕ :=
  {x : G | orderOf x = 2 ∧ g⁻¹ * x ∈ Hh}.ncard

/-- Bender §3: `b_n` = number of cosets `≠ Ĥ` containing exactly `n` involutions. -/
noncomputable def bCount (Hh : Subgroup G) (n : ℕ) : ℕ :=
  {c : G ⧸ Hh | c ≠ ((1 : G) : G ⧸ Hh) ∧ cosetInvCount Hh (Quotient.out c) = n}.ncard

end Helpers

/-- Zassenhaus hypotheses WITHOUT the cyclicity clause. HB III XI 1.5 (d odd, `G` simple) and
the proof of 1.11 (d even) derive it.

Copied verbatim from `Submission/Work/_design_gw/Core2.lean` (`GW2.ZassHyps2`). -/
def ZassHyps2 (G X : Type) [Group G] [Finite G] [MulAction G X] (q : ℕ) : Prop :=
  FaithfulSMul G X ∧ Nat.card X = q + 1 ∧ MulAction.IsMultiplyPretransitive G X 2 ∧
    (∀ g : G, g ≠ 1 → {x : X | g • x = x}.ncard ≤ 2) ∧
    (∀ x y : X, x ≠ y →
      2 * Nat.card (MulAction.stabilizer G x ⊓ MulAction.stabilizer G y : Subgroup G) = q - 1)

/-- HB III XI Theorems 1.11 + 1.12. ZASS should deliver this; it implies `ZassOddProp`.

Copied verbatim from `Submission/Work/_design_gw/Core2.lean` (`GW2.ZassOdd2Prop`). -/
def ZassOdd2Prop : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [MulAction G X] [Finite X] (p k : ℕ) [Fact p.Prime],
    Odd p → 5 ≤ p ^ k → IsSimpleGroup G → ZassHyps2 G X (p ^ k) →
    Nonempty (G ≃* PSL(2, GaloisField p k))

/-- The BSW hypotheses exactly as in Bender 1974, Theorem (i)–(iv).
* `K` is abelian and contains `t`, and `C(t) = K⟨s⟩`;
* `s` inverts `K`;
* `C_K(s) = ⟨t⟩`;
* `K` is TI with respect to `C(t)`;
* there is one class of involutions.

Copied verbatim from `Submission/Work/_design_gw/Core2.lean` (`GW2.BSWHyps2`). -/
def BSWHyps2 (G : Type) [Group G] [Finite G] (t s : G) (K : Subgroup G) : Prop :=
  orderOf t = 2 ∧ orderOf s = 2 ∧ t ∈ K ∧ s ∉ K ∧ IsMulCommutative K ∧
    centralizer ({t} : Set G) = K ⊔ zpowers s ∧ Inverts s K ∧
    K ⊓ centralizer ({s} : Set G) = zpowers t ∧
    (∀ g : G, g ∉ centralizer ({t} : Set G) → K ⊓ conjSub g K = ⊥) ∧
    ∀ x : G, orderOf x = 2 → IsConj x t

/-- B74 §§1–3: a Zassenhaus action on the conjugates of `Q`, i.e. on `G ⧸ N(Q)`.
`G` simple and nonabelian.

Copied verbatim from `Submission/Work/_design_gw/Core2.lean` (`GW2.BSWZass2Prop`). -/
def BSWZass2Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (t s : G) (K : Subgroup G), BSWHyps2 G t s K →
      ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
        ∃ M : Subgroup G, ZassHyps2 G (G ⧸ M) (p ^ k)

/-- The deliverable of area `BSW` (replaces the blueprint-2 `BSWProp`).

Copied verbatim from `Submission/Work/_design_gw/Core2.lean` (`GW2.BSW2Prop`). -/
def BSW2Prop : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (t s : G) (K : Subgroup G), BSWHyps2 G t s K →
      ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
        Nonempty (G ≃* PSL(2, GaloisField p k))

end Work.GW2

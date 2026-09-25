/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Submission.Work.CFT.ShafarevichCore.Defs
import Submission.Work.Tower.Defs

/-!
# `Work.CFT.GlobalClassFormation` — global class field theory and the class rank formula

This area owns the *global class field theory* input that the Shafarevich area
(`Submission/Work/CFT/ShafarevichCore`) localises in its two facts (a) and (b′), reproducing the
main theorems of class field theory *unconditionally where possible* and otherwise localising them
to classical statements that are manifestly true.

The target is **Koch's fact (b′)**, the *class-group rank formula*

`dim_{𝔽_p} H¹(G_∅, 𝔽_p) = dim_{𝔽_p} Cl_F[p]`

for `G_∅` the maximal everywhere-unramified pro-`p` group of a number field `F`, together with the
**weaker lower bound** `dim Cl_F[p] ≤ dim H¹(G_∅, 𝔽_p)` which is all the tower construction
consumes (see `Work.CFT.WeakCore`).

## What is in this file

Only the vocabulary; the mathematics is in the other modules of the area.

* `Work.CFT.GlobalClassFormation.classGroupTorsionGroup` — `Cl_F[p]` as a *multiplicative* group
  of exponent `p` (the form in which the class group is the Galois group of the `p`-Hilbert class
  field).
* `Work.CFT.GlobalClassFormation.HasClassGroupQuotient` — the **Artin surjectivity** / existence of
  the `p`-Hilbert class field, in the form of a surjection `G ↠ Cl_F[p]`.
* `Work.CFT.GlobalClassFormation.ClassRankLowerBound` / `ClassRankUpperBound` /
  `ClassRankFormula` — the two halves of (b′) and their conjunction.
* `Work.CFT.GlobalClassFormation.PHilbertClassField` — the *existence theorem* for the maximal
  everywhere-unramified abelian extension of exponent `p` (the `p`-Hilbert class field).
* `Work.CFT.GlobalClassFormation.UnramifiedProPModel` — `G` models the maximal everywhere-unramified
  pro-`p` group of `F` (it surjects onto every finite everywhere-unramified `p`-extension group).

## Conventions

Everything is monomorphic (`F K G : Type`), `NumberField` and `Classical` are open; groups acting
are finite when Tate cohomology is used.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.CFT.GlobalClassFormation

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Re-exported vocabulary -/

/-- `H¹(G, 𝔽_p)` with trivial coefficients. -/
abbrev H1Fp (p : ℕ) (G : Type) [Group G] : ModuleCat (ZMod p) :=
  Work.Tower.Shafarevich.H1Fp p G

/-- `H²(G, 𝔽_p)` with trivial coefficients. -/
abbrev H2Fp (p : ℕ) (G : Type) [Group G] : ModuleCat (ZMod p) :=
  Work.Tower.Shafarevich.H2Fp p G

/-- The `p`-torsion `Cl_F[p]` of the class group, as an `𝔽_p`-vector space. -/
abbrev classGroupTorsion (F : Type*) [Field F] [NumberField F] (p : ℕ) : Type _ :=
  Work.CFT.Kummer.classGroupTorsion F p

/-- The Kummer character group `𝓒_∅ = Hom(V_∅/F^{×p}, 𝔽_p)`. -/
abbrev kummerDual (F : Type*) [Field F] [NumberField F] (p : ℕ) : Type _ :=
  Work.CFT.Kummer.kummerDual F p ∅

/-! ## The class group as a multiplicative group of exponent `p` -/

/-- `Cl_F[p]`, the `p`-torsion subgroup of the class group, as a **multiplicative group** of
exponent `p`.

This is the natural group appearing in class field theory: the maximal everywhere-unramified
abelian extension of `F` of exponent `p` has Galois group `Cl_F / Cl_F^p ≅ Cl_F[p]` (the
`p`-Hilbert class field), and it is a quotient of the maximal everywhere-unramified pro-`p` group. -/
abbrev classGroupTorsionGroup (F : Type*) [Field F] [NumberField F] (p : ℕ) : Type _ :=
  Work.CFT.Kummer.classGroupP F p

theorem classGroupTorsionGroup_pow (F : Type*) [Field F] [NumberField F] (p : ℕ)
    (x : classGroupTorsionGroup F p) : x ^ p = 1 := Subtype.ext x.2

/-! ## The class rank formula and its two halves -/

/-- **The lower-bound half of the class-group rank formula (b′).**  The `p`-rank of the class
group is at most the generator rank of the maximal everywhere-unramified pro-`p` group:

`dim_{𝔽_p} Cl_F[p] ≤ dim_{𝔽_p} H¹(G, 𝔽_p)`.

Equivalently: `Cl_F[p]` is a quotient of `G/Φ(G)`, i.e. `F` has enough independent
everywhere-unramified abelian exponent-`p` extensions (the `p`-Hilbert class field exists).  This
is the *existence* direction of Artin reciprocity for unramified abelian extensions, and it is all
of (b′) that the tower construction consumes. -/
def ClassRankLowerBound (F : Type*) [Field F] [NumberField F] (p : ℕ) (G : Type) [Group G] :
    Prop :=
  Module.finrank (ZMod p) (classGroupTorsion F p) ≤ Module.finrank (ZMod p) (H1Fp p G)

/-- **The upper-bound half of the class-group rank formula (b′).**  The generator rank of the
maximal everywhere-unramified pro-`p` group is at most the `p`-rank of the class group:

`dim_{𝔽_p} H¹(G, 𝔽_p) ≤ dim_{𝔽_p} Cl_F[p]`.

Equivalently: `G^ab/p` is a quotient of `Cl_F[p]`, i.e. every everywhere-unramified abelian
exponent-`p` extension is contained in the `p`-Hilbert class field.  This is the
*norm-limitation* direction of Artin reciprocity (the reciprocity map is surjective onto the class
group with the right kernel). -/
def ClassRankUpperBound (F : Type*) [Field F] [NumberField F] (p : ℕ) (G : Type) [Group G] :
    Prop :=
  Module.finrank (ZMod p) (H1Fp p G) ≤ Module.finrank (ZMod p) (classGroupTorsion F p)

/-- **The class-group rank formula (b′)** in the form used by this area: the two inequalities
together. -/
def ClassRankFormula (F : Type*) [Field F] [NumberField F] (p : ℕ) (G : Type) [Group G] : Prop :=
  ClassRankLowerBound F p G ∧ ClassRankUpperBound F p G

/-- The formula in the two-halves form is the equality. -/
theorem classRankFormula_iff (F : Type*) [Field F] [NumberField F] (p : ℕ) (G : Type) [Group G] :
    ClassRankFormula F p G ↔
      Module.finrank (ZMod p) (H1Fp p G) = Module.finrank (ZMod p) (classGroupTorsion F p) :=
  ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨le_of_eq h.symm, le_of_eq h⟩⟩

/-- The class rank formula of `Submission/Work/CFT/ShafarevichCore` is exactly the equality form
used here. -/
theorem classRankFormula_iff_shafarevichCore (F : Type*) [Field F] [NumberField F] (p : ℕ)
    (G : Type) [Group G] :
    ClassRankFormula F p G ↔ Work.CFT.ShafarevichCore.ClassRankFormula F p G := by
  rw [classRankFormula_iff]
  rfl

/-! ## The Artin surjectivity / existence of the `p`-Hilbert class field -/

/-- **The existence of the `p`-Hilbert class field as a quotient** — Artin surjectivity for
everywhere-unramified abelian `p`-extensions.

There is a surjection `G ↠ Cl_F[p]` from the maximal everywhere-unramified pro-`p` group onto the
`p`-torsion of the class group.  Equivalently, the maximal everywhere-unramified abelian extension
of `F` of exponent `p` exists and has Galois group `Cl_F[p]`.

This is a theorem of global class field theory (the existence theorem of Takagi, in its
everywhere-unramified abelian `p`-form; Hilbert's theorem 94 combined with the existence of the
Hilbert class field).  It is *not* the conclusion of the tower argument; it is the one arithmetic
input which the lower bound needs. -/
def HasClassGroupQuotient (F : Type*) [Field F] [NumberField F] (p : ℕ) (G : Type) [Group G] :
    Prop :=
  ∃ φ : G →* classGroupTorsionGroup F p, Function.Surjective φ

/-- **The norm-limitation direction of Artin reciprocity**, in the dual form of an *injection*
`Hom(G, 𝔽_p) ↪ Cl_F[p]`: every everywhere-unramified abelian exponent-`p` extension of `F` is
contained in the `p`-Hilbert class field (`G^ab / p` is a quotient of `Cl_F[p]`).

This gives the upper bound `dim_{𝔽_p} H¹(G,𝔽_p) ≤ dim_{𝔽_p} Cl_F[p]` (see
`Work.CFT.GlobalClassFormation.classRank_upper_bound_of_covering`).  Note that for finite-dimensional
spaces the *existence* of such an injection is equivalent to the dimension inequality
(`Work.CFT.GlobalClassFormation.hasClassGroupCovering_of_classRankUpperBound`), so the arithmetic
content of this hypothesis is precisely the upper bound — the injection is a convenient "shape" for
it, not extra data. -/
def HasClassGroupCovering (F : Type*) [Field F] [NumberField F] (p : ℕ) (G : Type) [Group G] :
    Prop :=
  ∃ ι : (Additive G →+ ZMod p) →ₗ[ZMod p] classGroupTorsion F p, Function.Injective ι

/-- **The existence theorem for the `p`-Hilbert class field**, geometrically.

The maximal everywhere-unramified abelian extension `H` of `F` of exponent `p` exists: it is a
finite Galois extension, unramified everywhere, abelian of exponent `p`, with Galois group
`Cl_F[p]`, and it is maximal (every other everywhere-unramified abelian exponent-`p` extension of
`F` embeds in it).  This is the every-unramified abelian `p`-part of the *existence theorem* of
global class field theory (Takagi; the `p`-Hilbert class field).

It is a classical theorem, absent from Mathlib; the areas of the project build on it as a named
input (this structure), and reduce the class rank formula to it. -/
structure PHilbertClassField (F : Type) [Field F] [NumberField F] (p : ℕ) where
  /-- the `p`-Hilbert class field -/
  H : Type
  [field_H : Field H]
  [numberField_H : NumberField H]
  [algebra_H : Algebra F H]
  [finiteDimensional_H : FiniteDimensional F H]
  [isGalois_H : IsGalois F H]
  /-- `H/F` is unramified at every finite prime -/
  isUnramified : Work.Tower.IsUnramifiedExtension F H
  /-- `H/F` is abelian -/
  isAbelian : IsMulCommutative (Gal(H/F))
  /-- every element of the Galois group has order dividing `p` (the extension has exponent `p`) -/
  exponent : ∀ σ : Gal(H/F), σ ^ p = 1
  /-- the Galois group is the `p`-torsion of the class group -/
  galoisIso : Nonempty (Gal(H/F) ≃* classGroupTorsionGroup F p)
  /-- maximality: every everywhere-unramified abelian exponent-`p` extension of `F` embeds in `H` -/
  maximal : ∀ (L : Type) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L]
    [IsGalois F L], Work.Tower.IsUnramifiedExtension F L → IsMulCommutative (Gal(L/F)) →
    (∀ σ : Gal(L/F), σ ^ p = 1) → ∃ (_ : L →ₐ[F] H), True

attribute [instance] PHilbertClassField.field_H PHilbertClassField.numberField_H
  PHilbertClassField.algebra_H PHilbertClassField.finiteDimensional_H
  PHilbertClassField.isGalois_H

/-- **`G` models the maximal everywhere-unramified pro-`p` group of `F`**: `G` surjects onto the
Galois group of every finite everywhere-unramified Galois `p`-extension of `F`.

This is the universal property of the maximal everywhere-unramified pro-`p` group
`G_∅ = Gal(F_∅(p)/F)` (the inverse limit of the finite quotients `Gal(L/F)`); it is a *true*
statement for `G = G_∅`, and it is the structural hypothesis under which the abstract group `G` is
used by `Submission/Work/CFT/ShafarevichCore`. -/
structure UnramifiedProPModel (F : Type) [Field F] [NumberField F] (p : ℕ) (G : Type) [Group G]
    where
  /-- surjection onto the Galois group of any finite everywhere-unramified `p`-extension -/
  covers : ∀ (L : Type) [Field L] [NumberField L] [Algebra F L] [FiniteDimensional F L]
    [IsGalois F L], Work.Tower.IsUnramifiedExtension F L → IsPGroup p (Gal(L/F)) →
    ∃ φ : G →* Gal(L/F), Function.Surjective φ

end

end Work.CFT.GlobalClassFormation

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Neukirch's *Kennzeichnung* through the higher ramification filtration

This file connects the higher ramification filtration built in
`Submission/Work/Ramification/` to the input that the Neukirch–Uchida development consumes,
`NK.LocalStructure.LocalFieldFromFiniteExtensionLattice`.

The two halves of the classical argument (Neukirch, Invent. Math. **6** (1969); NSW (12.1.4)–(12.1.5))
are separated, in exactly the form in which the docstring of `LocalFieldFromFiniteExtensionLattice`
records them:

* **`FiltrationDetectedByLattice`** — (i) the ramification filtration is determined by the lattice of
  finite extensions: for `Φ : Gal(L'/N) ≃* Gal(K'/𝔭.adicCompletion K)` carrying a correspondence of
  finite extension lattices `C`, the lower indices `g_i` of the higher ramification subgroups of a
  finite Galois level `E` of `κ = 𝔭.adicCompletion K` agree with those of the corresponding level
  `C.level E` of `N`.  This is Neukirch's hard step; it is *not* proved here.
* **`RamificationDeterminesLocalField`** — (ii) the ramification filtration, read through the
  correspondence, determines the field: `N ≃+* 𝔭.adicCompletion K`.

The main theorem is the reduction

  `RamificationDeterminesLocalField` together with `FiltrationDetectedByLattice` implies
  `NK.LocalStructure.LocalFieldFromFiniteExtensionLattice`,

and, modulo `FiltrationDetectedByLattice`, the two are *equivalent*
(`localFieldFromFiniteExtensionLattice_iff_ramificationDeterminesLocalField`).
-/
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.Filtration
import Submission.NK.LocalStructure.Defs

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.Ramification

universe u

noncomputable section

/-- **The `i`-th lower index `g_i` of a finite level of a `p`-adic field.**  For `B` a separable
closure of `Q.adicCompletion K` and `E` a finite extension of `Q.adicCompletion K` inside `B`, this
is the number of elements of the `i`-th higher ramification subgroup of `Gal(E/Q.adicCompletion K)`,
computed with the valuation ring `finiteExtensionIntegers Q E` of `E`, which is stable under all of
`Gal(E/Q.adicCompletion K)`. -/
def levelIndex {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (B : Type u) [Field B] [Algebra (Q.adicCompletion K) B]
    (E : {E : IntermediateField (Q.adicCompletion K) B //
      FiniteDimensional (Q.adicCompletion K) ↥E}) (i : ℕ) : ℕ :=
  letI : FiniteDimensional (Q.adicCompletion K) ↥E.1 := E.2
  Nat.card ↥(((ramificationSubgroup (K := Q.adicCompletion K) (finiteExtensionIntegers Q ↥E.1) i).map
    ((finiteExtensionIntegers Q ↥E.1).decompositionSubgroup (Q.adicCompletion K)).subtype))

/-- **The same lower index computed over an intermediate base `M₀`**: the number of elements of
the `i`-th higher ramification subgroup of `Gal(E/M₀)`, where `E` is a finite extension of the
finite extension `M₀` of `Q.adicCompletion K`, computed with the valuation ring of `E`. -/
def levelIndexOver {K : Type u} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (B : Type u) [Field B] [Algebra (Q.adicCompletion K) B]
    (M₀ : IntermediateField (Q.adicCompletion K) B) [FiniteDimensional (Q.adicCompletion K) ↥M₀]
    (E : {E : IntermediateField ↥M₀ B // FiniteDimensional ↥M₀ ↥E}) (i : ℕ) : ℕ :=
  letI : FiniteDimensional ↥M₀ ↥E.1 := E.2
  letI : FiniteDimensional (Q.adicCompletion K) ↥E.1 :=
    FiniteDimensional.trans (Q.adicCompletion K) ↥M₀ ↥E.1
  Nat.card ↥(((ramificationSubgroup (K := ↥M₀) (finiteExtensionIntegers Q ↥E.1) i).map
    ((finiteExtensionIntegers Q ↥E.1).decompositionSubgroup ↥M₀).subtype))

/-- **The ramification filtration is carried by a correspondence of finite extension lattices.**

For a fixed isomorphism `Φ : Gal(L'/N) ≃* Gal(K'/𝔭.adicCompletion K)` of absolute Galois groups of
`p`-adic fields together with a correspondence `C` of their lattices of finite extensions
(`NK.LocalStructure.FiniteExtensionCorrespondence Φ`), this says: at every finite extension `E` of
`N` inside `L'`, the lower indices `g_i` of the higher ramification subgroups of `Gal(E/N)` —
computed with the valuation ring `finiteExtensionIntegers 𝔮 E` of `E` — agree with those of the
corresponding level `C.level E` of `κ = 𝔭.adicCompletion K` inside `K'`. -/
def FiltrationCorresponds {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (N : IntermediateField (𝔮.adicCompletion L) L') [FiniteDimensional (𝔮.adicCompletion L) ↥N]
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    (Φ : Gal(L'/↥N) ≃* Gal(K'/𝔭.adicCompletion K))
    (C : NK.LocalStructure.FiniteExtensionCorrespondence Φ) : Prop :=
  ∀ (E : {E : IntermediateField ↥N L' // FiniteDimensional ↥N ↥E}) (i : ℕ),
    levelIndexOver 𝔮 L' N E i =
      levelIndex 𝔭 K' ⟨C.level E, C.level_finite E⟩ i

/-- **Neukirch's hard step, in ramification language: the filtration is detected by the lattice.**

For every isomorphism `Φ` of absolute Galois groups of `p`-adic fields and every correspondence `C`
of their finite extension lattices, the ramification filtration is carried by the correspondence
(`FiltrationCorresponds`).

This is the statement that the higher ramification filtration of `Gal(κ̄/κ)` is an invariant of the
*abstract* group (or, equivalently here, of the lattice of finite extensions); classically it is
obtained from local class field theory (the reciprocity map carries the unit filtration `U^i` onto
the upper-numbered ramification subgroups `G^i`, Serre, *Local Fields* XV §2), together with
Neukirch's analysis of the lattice (Invent. Math. **6** (1969)).  It is **not** proved in this
workspace; it is isolated here as a single named proposition, and the reduction below shows exactly
what it buys. -/
def FiltrationDetectedByLattice : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (N : IntermediateField (𝔮.adicCompletion L) L') [FiniteDimensional (𝔮.adicCompletion L) ↥N]
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    (Φ : Gal(L'/↥N) ≃* Gal(K'/𝔭.adicCompletion K))
    (C : NK.LocalStructure.FiniteExtensionCorrespondence (κ := ↥N) (K' := L')
      (κ₂ := 𝔭.adicCompletion K) (L' := K') Φ),
    FiltrationCorresponds 𝔭 𝔮 L' N K' Φ C

/-- **Neukirch's Kennzeichnung through the ramification filtration.**  The ramification filtration,
read through a correspondence of finite extension lattices, determines the `p`-adic field: if the
filtration is carried by the correspondence, then `N ≃+* 𝔭.adicCompletion K`.

This is the statement that a `p`-adic field is determined by its residue data together with the
ramification breaks of its absolute Galois group (Neukirch, Invent. Math. **6** (1969), the local
case; NSW (12.1.4)–(12.1.5)). -/
def RamificationDeterminesLocalField : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (N : IntermediateField (𝔮.adicCompletion L) L') [FiniteDimensional (𝔮.adicCompletion L) ↥N]
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
    [IsSepClosure (𝔭.adicCompletion K) K']
    (Φ : Gal(L'/↥N) ≃* Gal(K'/𝔭.adicCompletion K))
    (C : NK.LocalStructure.FiniteExtensionCorrespondence (κ := ↥N) (K' := L')
      (κ₂ := 𝔭.adicCompletion K) (L' := K') Φ),
    FiltrationCorresponds 𝔭 𝔮 L' N K' Φ C → Nonempty (↥N ≃+* 𝔭.adicCompletion K)

/-- **The reduction: the two ramification-side halves imply the workspace's input.**

`FiltrationDetectedByLattice` (the filtration is read off the lattice — Neukirch's hard step)
together with `RamificationDeterminesLocalField` (the filtration determines the field) imply
`NK.LocalStructure.LocalFieldFromFiniteExtensionLattice`. -/
theorem localFieldFromFiniteExtensionLattice_of_detection_and_ramification
    (hdet : FiltrationDetectedByLattice.{u}) (hram : RamificationDeterminesLocalField.{u}) :
    NK.LocalStructure.LocalFieldFromFiniteExtensionLattice.{u} := by
  intro K L _ _ _ _ 𝔭 𝔮 L' _ _ _ N _ K' _ _ _ Φ C
  exact hram K L 𝔭 𝔮 L' N K' Φ C (hdet K L 𝔭 𝔮 L' N K' Φ C)

/-- **The filtration-side statement follows from the workspace's input** (one direction of the
equivalence below): a proof of `LocalFieldFromFiniteExtensionLattice` yields, in particular, the
field isomorphism asked for by `RamificationDeterminesLocalField`. -/
theorem ramificationDeterminesLocalField_of_localFieldFromFiniteExtensionLattice
    (h : NK.LocalStructure.LocalFieldFromFiniteExtensionLattice.{u}) :
    RamificationDeterminesLocalField.{u} := by
  intro K L _ _ _ _ 𝔭 𝔮 L' _ _ _ N _ K' _ _ _ Φ C _
  exact h K L 𝔭 𝔮 L' N K' Φ C

/-- **The equivalence.**  Modulo Neukirch's hard step `FiltrationDetectedByLattice`, Neukirch's
*Kennzeichnung* in lattice form is *equivalent* to its ramification form
`RamificationDeterminesLocalField`: "the ramification filtration of the finite levels, read through
the correspondence, determines the `p`-adic field". -/
theorem localFieldFromFiniteExtensionLattice_iff_ramificationDeterminesLocalField
    (hdet : FiltrationDetectedByLattice.{u}) :
    NK.LocalStructure.LocalFieldFromFiniteExtensionLattice.{u} ↔
      RamificationDeterminesLocalField.{u} :=
  ⟨ramificationDeterminesLocalField_of_localFieldFromFiniteExtensionLattice,
    fun hram => localFieldFromFiniteExtensionLattice_of_detection_and_ramification hdet hram⟩

end

end NK.Ramification

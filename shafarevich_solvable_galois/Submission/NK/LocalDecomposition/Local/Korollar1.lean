/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The local reconstruction: Neukirch's Korollar 1 and the local Neukirch–Uchida theorem

The two local classical inputs of this chapter are

* `NK.LocalStructure.LocalNUExistence` — the local Neukirch–Uchida existence theorem: an
  isomorphism `Gal(L'/M) ≃* Gal(K'/(𝔭.adicCompletion K))` of absolute Galois groups of `p`-adic
  fields (with `M/L` finite) forces `M ≅ 𝔭.adicCompletion K` (Neukirch, Invent. Math. **6** (1969),
  CoNF (12.1.4)–(12.1.5));
* `NK.LocalStructure.Korollar1Local p` — the same statement with the finiteness of `M/L` phrased
  as the finite index of the fixing subgroup `M.fixingSubgroup ≤ Gal(L'/𝔮.adicCompletion L)`, which
  is the form in which Neukirch's Theorem 1 consumes it.

This file proves that the two are **equivalent** (the forward implication is a re-proof of
`NK.LocalStructure.Brauer.korollar1Local_of_localNUExistence`, the backward one is the Galois
correspondence: a finite-dimensional intermediate field has finitely-indexed fixing subgroup, and
`M.fixingSubgroup ≃* Gal(L'/M)`), and deduces from them, together with the local form
`NK.LocalDecomposition.LocalInjectionFiniteIndex` of Neukirch's Korollar 1, the *full* classical
statement:

* `NK.LocalDecomposition.localInjection_ringEquiv` — if `Gal(L'/N) ≅ Gal(κ'/κ)` for a `p`-adic
  field `κ`, then `N` is a *finite* extension of `L` and `N ≅ κ` (Neukirch, Invent. Math. **6**
  (1969), Korollar 1; A. Ivanov, arXiv:1309.2801, Lemma `lm:locfinindex`).
-/
import Submission.NK.LocalDecomposition.Defs
import Submission.NK.LocalStructure.Brauer.korollar1Local_of_localNUExistence
import Submission.NK.LocalStructure.LocalNU.localNUExistence_of_finiteExtensionLattice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false


open scoped Classical Pointwise
open IsDedekindDomain.HeightOneSpectrum

universe u

namespace NK.LocalDecomposition

noncomputable section

open NK.BrauerHasse

/-- **Neukirch's local Neukirch–Uchida existence theorem and Korollar 1 are equivalent.**

The forward implication is Neukirch's Korollar 1 from the local Neukirch–Uchida statement (a
re-proof of `NK.LocalStructure.Brauer.korollar1Local_of_localNUExistence`).  For the converse, if
`M` is a finite-dimensional intermediate field of the separable closure `L'` of `𝔮.adicCompletion L`
and `Gal(L'/M) ≃* Gal(K'/𝔭.adicCompletion K)`, then the fixing subgroup of `M` has finite index —
`IntermediateField.finrank_eq_fixingSubgroup_index` identifies the index of `M.fixingSubgroup` with
`Module.finrank (𝔮.adicCompletion L) M`, which is non-zero — and the given isomorphism transfers to
`M.fixingSubgroup ≃* Gal(K'/𝔭.adicCompletion K)` through `IntermediateField.fixingSubgroupEquiv`. -/
theorem korollar1Local_iff_localNUExistence (p : ℕ) :
    NK.LocalStructure.Korollar1Local.{u} p ↔ NK.LocalStructure.LocalNUExistence.{u} := by
  refine ⟨?_, NK.LocalStructure.Brauer.korollar1Local_of_localNUExistence p⟩
  intro h1Local
  intro K L _ _ _ _ 𝔭 𝔮 L' _ _ _ M _ K' _ _ _ hiso
  -- the fixing subgroup of a finite-dimensional intermediate field has finite index
  have hindex : M.fixingSubgroup.FiniteIndex := by
    rw [Subgroup.finiteIndex_iff]
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index (F := 𝔮.adicCompletion L)
      (E' := L') (L := M)]
    exact ne_of_gt Module.finrank_pos
  -- transport the isomorphism of absolute Galois groups to the fixing subgroup
  obtain ⟨e⟩ := hiso
  exact h1Local K L 𝔭 𝔮 L' K' M M.fixingSubgroup rfl hindex
    ⟨(IntermediateField.fixingSubgroupEquiv M).trans e⟩

/-- **The full statement of Neukirch's Korollar 1** (Invent. Math. **6** (1969); CoNF (12.1.9) end;
A. Ivanov, arXiv:1309.2801, Lemma `lm:locfinindex`): the absolute Galois group of an intermediate
field `N` of a separable closure of a `p`-adic field `L` determines `N` — if it is isomorphic to
the absolute Galois group of the completion `𝔭₂.adicCompletion K₂` of a number field at a finite
prime, then `N` is a *finite* extension of `L` and `N ≅ 𝔭₂.adicCompletion K₂`.

The finiteness is the input `LocalInjectionFiniteIndex` (the local half of `lm:locfinindex`); the
isomorphism is `LocalNUExistence` (Neukirch's local theorem). -/
theorem localInjection_ringEquiv {K₂ : Type u} [Field K₂] [NumberField K₂]
    (𝔭₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂))
    {K₂' : Type u} [Field K₂'] [Algebra (𝔭₂.adicCompletion K₂) K₂']
    [IsSepClosure (𝔭₂.adicCompletion K₂) K₂']
    (hD : LocalInjectionFiniteIndex (𝔭₂.adicCompletion K₂) K₂')
    (hNU : NK.LocalStructure.LocalNUExistence.{u})
    {L : Type u} [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    {L' : Type u} [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (N : IntermediateField (𝔮.adicCompletion L) L')
    (h : Nonempty (Gal(L'/↥N) ≃* Gal(K₂'/𝔭₂.adicCompletion K₂))) :
    FiniteDimensional (𝔮.adicCompletion L) ↥N ∧ Nonempty (↥N ≃+* 𝔭₂.adicCompletion K₂) := by
  have hfin : FiniteDimensional (𝔮.adicCompletion L) ↥N := hD L 𝔮 L' N h
  haveI := hfin
  exact ⟨hfin, hNU K₂ L 𝔭₂ 𝔮 L' N K₂' h⟩

/-- **The local Neukirch–Uchida existence theorem from the finite-extension lattice**: the
assembly proved in `Submission/Work/LocalStructure/LocalNU/`, re-exported here.  Neukirch's local
reconstruction is reduced to the field-theoretic statement
`NK.LocalStructure.LocalFieldFromFiniteExtensionLattice` (the lattice of finite extensions of a
`p`-adic field determines the field) together with the *proved* Galois-correspondence half
`NK.LocalStructure.LocalNU.finiteExtensionCorrespondence_of_groupIso`. -/
theorem localNUExistence_of_finiteExtensionLattice
    (h : NK.LocalStructure.LocalFieldFromFiniteExtensionLattice.{u})
    (hcorr : ∀ (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
      (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
      (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
      [IsSepClosure (𝔮.adicCompletion L) L']
      (N : IntermediateField (𝔮.adicCompletion L) L') [FiniteDimensional (𝔮.adicCompletion L) ↥N]
      (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K']
      [IsSepClosure (𝔭.adicCompletion K) K']
      (Φ : Gal(L'/↥N) ≃* Gal(K'/𝔭.adicCompletion K)),
      Nonempty (NK.LocalStructure.FiniteExtensionCorrespondence Φ)) :
    NK.LocalStructure.LocalNUExistence.{u} :=
  NK.LocalStructure.LocalNU.localNUExistence_of_finiteExtensionLattice h hcorr

end

end NK.LocalDecomposition

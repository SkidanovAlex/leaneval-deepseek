/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Neukirch's local Korollar 1, deduced from the local Neukirch–Uchida existence statement

`NK.LocalStructure.Korollar1Local p` is Neukirch's local reconstruction statement in the form
consumed by Neukirch's Theorem 1 (CoNF (12.1.4)–(12.1.6)): if `M` is an intermediate field of a
separable closure `L'` of a `p`-adic field `𝔮.adicCompletion L`, the fixing subgroup of `M` has
finite index in `Gal(L'/𝔮.adicCompletion L)`, and that fixing subgroup is isomorphic to the
absolute Galois group `Gal(K'/𝔭.adicCompletion K)` of another `p`-adic field, then
`M ≅ 𝔭.adicCompletion K`.

The reduction to the local Neukirch–Uchida existence statement `LocalNUExistence` is
bookkeeping across the Galois correspondence:

* the fixing subgroup `M.fixingSubgroup` of `M` in `Gal(L'/𝔮.adicCompletion L)` is canonically
  isomorphic to `Gal(L'/↥M)` (`IntermediateField.fixingSubgroupEquiv`), so an isomorphism
  `M.fixingSubgroup ≃* Gal(K'/𝔭.adicCompletion K)` is the same thing as an isomorphism
  `Gal(L'/↥M) ≃* Gal(K'/𝔭.adicCompletion K)`;
* `LocalNUExistence` is stated for *finite dimensional* `M`, so we must extract
  `FiniteDimensional (𝔮.adicCompletion L) ↥M` from the hypothesis `M.fixingSubgroup.FiniteIndex`.
  This is the Krull-topology form of the Galois correspondence: since `L'/𝔮.adicCompletion L` is
  Galois (it is a separable closure), `M.fixingSubgroup` is closed, a closed finite-index subgroup
  is open, and `InfiniteGalois.isOpen_iff_finite` says that the fixing subgroup of `M` is open
  exactly when `M` is finite dimensional over the base.
-/
import Mathlib
import Submission.NK.LocalStructure.Defs

namespace NK.LocalStructure.Brauer

open scoped Classical Pointwise
open IsDedekindDomain.HeightOneSpectrum

universe u

/-- **Neukirch's Korollar 1 (local reconstruction) from the local Neukirch–Uchida existence
statement.**

The local Neukirch–Uchida existence statement `LocalNUExistence` — every isomorphism of absolute
Galois groups of `p`-adic fields is induced by a field isomorphism — implies Neukirch's Korollar 1
in the "fixing subgroup" form used by his Theorem 1: a finite extension `M` of a `p`-adic field
whose absolute Galois group is isomorphic to that of a `p`-adic field `κ` is itself isomorphic
to `κ`.

The two bookkeeping steps are described in the file header. -/
theorem korollar1Local_of_localNUExistence (p : ℕ)
    (h : NK.LocalStructure.LocalNUExistence.{u}) :
    NK.LocalStructure.Korollar1Local.{u} p := by
  intro K L _ _ _ _ 𝔭 𝔮 L' _ _ _ K' _ _ _ M H hH hHidx hHiso
  -- Replace the abstract subgroup `H` by the fixing subgroup it is assumed to be.
  subst hH
  -- `L'` is a separable closure of the `p`-adic field `𝔮.adicCompletion L`, hence the extension
  -- is Galois, so its fixing subgroups are closed for the Krull topology.
  have hclosed : IsClosed (M.fixingSubgroup : Set Gal(L'/𝔮.adicCompletion L)) :=
    InfiniteGalois.fixingSubgroup_isClosed M
  -- A closed subgroup of finite index is open.
  have hFinIdx : M.fixingSubgroup.FiniteIndex := hHidx
  have hopen : IsOpen (M.fixingSubgroup : Set Gal(L'/𝔮.adicCompletion L)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex M.fixingSubgroup hclosed
  -- An open fixing subgroup means exactly a finite-dimensional intermediate field.
  have hfin : FiniteDimensional (𝔮.adicCompletion L) M :=
    (InfiniteGalois.isOpen_iff_finite M).mp hopen
  obtain ⟨e⟩ := hHiso
  -- `Gal(L'/↥M) ≅ M.fixingSubgroup`, so the given isomorphism is one of the shape that
  -- `LocalNUExistence` consumes.
  refine h K L 𝔭 𝔮 L' M K' ⟨?_⟩
  exact (IntermediateField.fixingSubgroupEquiv M).symm.trans e

end NK.LocalStructure.Brauer

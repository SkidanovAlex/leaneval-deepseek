/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Block (i), part (C)-Korollar 1: instantiating `NK.Indecomposed.LocalKorollar1`

Neukirch's **Korollar 1** (Invent. Math. **6** (1969); NSW (12.1.9), end of the proof; A. Ivanov,
arXiv:1309.2801, Lemma `lm:locfinindex`) says that an injection of absolute Galois groups of local
fields, with the source local field `p`-adic, forces the target to be `p`-adic and the injection to
have finite index.

The form consumed by the criterion is

```
NK.Indecomposed.LocalKorollar1 κ κ' :
  ∀ (L : Type u) [Field L] [NumberField L] (𝔮) (L') (H : Subgroup Gal(L'/𝔮.adicCompletion L)),
    Nonempty (H ≃* Gal(κ'/κ)) → 0 < H.relIndex ⊤
```

i.e. *every* subgroup of the absolute Galois group of the `p`-adic field `L_𝔮` isomorphic to
`Gal(κ'/κ)` has finite index.  The classical statement is for **closed** subgroups (an injection
`Gal_L ⊆ Gal_M` of absolute Galois groups is an injection of closed subgroups), so this module
proves the requester's form from

* `NK.LocalDecomposition.LocalInjectionFiniteIndex κ κ'` — the classical finiteness statement for
  closed subgroups (the on-disk name for Ivanov's `lm:locfinindex`), and
* `NK.IndecomposedDeep.LocalSubgroupClosed κ κ'` — the closedness of a subgroup isomorphic to a
  `p`-adic absolute Galois group (Serre's theorem that a subgroup of a `p`-adic analytic group
  isomorphic to a `p`-adic analytic group is closed).

The proof is the Galois correspondence: a closed subgroup is the fixing subgroup of its fixed field,
`NK.LocalDecomposition.LocalInjectionFiniteIndex` makes that fixed field a *finite* extension, the
index of the fixing subgroup is its degree
(`IntermediateField.finrank_eq_fixingSubgroup_index`), and a finite-index subgroup has positive
index (`Subgroup.relIndex_top_right`, `Subgroup.FiniteIndex.index_ne_zero`).
-/

import Submission.NK.IndecomposedDeep.Defs

open IsDedekindDomain.HeightOneSpectrum

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

namespace NK.IndecomposedDeep

variable {κ κ' : Type u} [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']

/-- **Neukirch's Korollar 1 for a closed subgroup forces finite index.**

This is the classical statement (Ivanov's `lm:locfinindex`) with the closedness hypothesis made
explicit: a closed subgroup `H ≤ Gal(L'/L_𝔮)` isomorphic to `Gal(κ'/κ)` — `κ` a `p`-adic field —
has finite index in `Gal(L'/L_𝔮)`. -/
theorem relIndex_pos_of_isClosed (hfin : NK.LocalDecomposition.LocalInjectionFiniteIndex.{u} κ κ')
    (L : Type u) [Field L] [NumberField L]
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
    [IsSepClosure (𝔮.adicCompletion L) L']
    (H : Subgroup Gal(L'/𝔮.adicCompletion L)) (hHcl : IsClosed (H : Set Gal(L'/𝔮.adicCompletion L)))
    (hκ : Nonempty (H ≃* Gal(κ'/κ))) :
    0 < H.relIndex ⊤ := by
  obtain ⟨e⟩ := hκ
  have : IsGalois (𝔮.adicCompletion L) L' := inferInstance
  -- a closed subgroup is the fixing subgroup of its fixed field
  have hfix : H = (IntermediateField.fixedField H).fixingSubgroup := by
    rw [InfiniteGalois.fixingSubgroup_fixedField (k := 𝔮.adicCompletion L) (K := L') ⟨H, hHcl⟩]
  -- the isomorphism, transported to the fixing subgroup of the fixed field
  have hiso : Nonempty ((IntermediateField.fixedField H).fixingSubgroup ≃* Gal(κ'/κ)) := ⟨hfix ▸ e⟩
  have hiso' : Nonempty (Gal(L'/↥(IntermediateField.fixedField H)) ≃* Gal(κ'/κ)) := by
    obtain ⟨g⟩ := hiso
    exact ⟨(IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField H)).symm.trans g⟩
  -- Neukirch's Korollar 1: the fixed field is a finite extension
  have hfd : FiniteDimensional (𝔮.adicCompletion L) ↥(IntermediateField.fixedField H) :=
    hfin L 𝔮 L' (IntermediateField.fixedField H) hiso'
  haveI := hfd
  -- ... whence the fixing subgroup has finite index, of positive index
  have hfinidx : H.FiniteIndex := by
    rw [hfix, Subgroup.finiteIndex_iff,
      ← IntermediateField.finrank_eq_fixingSubgroup_index (F := 𝔮.adicCompletion L)
        (E' := L') (L := IntermediateField.fixedField H)]
    exact (Module.finrank_pos (R := 𝔮.adicCompletion L)
      (M := ↥(IntermediateField.fixedField H))).ne'
  rw [Subgroup.relIndex_top_right]
  exact Nat.pos_of_ne_zero hfinidx.index_ne_zero

/-- **Neukirch's Korollar 1 in the form consumed by the criterion**
(`NK.Indecomposed.LocalKorollar1`), from the closed-subgroup form
(`NK.LocalDecomposition.LocalInjectionFiniteIndex`) together with the closedness input
`NK.IndecomposedDeep.LocalSubgroupClosed`.

The only content beyond `relIndex_pos_of_isClosed` is the closedness of a subgroup isomorphic to
`Gal(κ'/κ)`: this is where Serre's theorem on analytic subgroups of `p`-adic analytic groups enters,
and it is the reason the requester's form — which quantifies over *arbitrary* subgroups — is not
literally the classical statement.  See `README.md` §5. -/
theorem localKorollar1_of_inputs (hclosed : LocalSubgroupClosed.{u} κ κ')
    (hfin : NK.LocalDecomposition.LocalInjectionFiniteIndex.{u} κ κ') :
    NK.Indecomposed.LocalKorollar1.{u} κ κ' := by
  intro L _ _ 𝔮 L' _ _ _ H hκ
  exact relIndex_pos_of_isClosed hfin L 𝔮 L' H (hclosed L 𝔮 L' H hκ) hκ

/-- The same theorem with the closedness input supplied as a plain function instead of the bundled
`LocalSubgroupClosed`, for callers that already have the closedness of the subgroup at hand. -/
theorem localKorollar1_of_relIndex_pos_of_isClosed
    (hclosed : ∀ (L : Type u) [Field L] [NumberField L]
      (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L']
      [IsSepClosure (𝔮.adicCompletion L) L']
      (H : Subgroup Gal(L'/𝔮.adicCompletion L)),
      Nonempty (H ≃* Gal(κ'/κ)) → IsClosed (H : Set Gal(L'/𝔮.adicCompletion L)))
    (hfin : NK.LocalDecomposition.LocalInjectionFiniteIndex.{u} κ κ') :
    NK.Indecomposed.LocalKorollar1.{u} κ κ' :=
  localKorollar1_of_inputs (κ := κ) (κ' := κ') hclosed hfin

end NK.IndecomposedDeep

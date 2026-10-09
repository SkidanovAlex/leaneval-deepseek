/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Neukirch's Korollar 1 (local form): the relative index in a decomposition group is positive

This file derives, from the *local* form `NK.Indecomposed.LocalKorollar1 κ κ'` of Neukirch's
Korollar 1 (Neukirch, Invent. Math. **6** (1969); CoNF (12.1.9); A. Ivanov, arXiv:1309.2801,
`lm:locfinindex`), the positivity of the relative index `[D_A : H]` for a subgroup
`H ≤ D_A = stabSubgroup A` of a decomposition group which is isomorphic to the absolute Galois
group `Gal(κ'/κ)` of the `p`-adic field `κ`.

The statement is the local-form companion of
`NK.LocalDecomposition.relIndex_pos_of_localInjection` (which uses the
`IntermediateField`-parametrised form of Korollar 1): here no intermediate field occurs, matching
the correct reading of Neukirch's Korollar 1 (see the discussion around
`NK.Indecomposed.LocalKorollar1` and `NK.Indecomposed.not_localInjectionFiniteIndexSubgroup`).

The proof is the transport of the index along the local correspondence
`NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois`
(`D_A ≅ Gal(L'/L)` for `L = 𝔭.adicCompletion K`), which is valid for arbitrary subgroups.
-/
import Mathlib
import Submission.NK.Indecomposed.Defs
import Submission.NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois
import Submission.NK.LocalDecomposition.Local.Korollar1Global
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u

namespace NK.Indecomposed

open NK.BrauerHasse

/-- **Neukirch's Korollar 1, local form: the relative index in a decomposition group.**

Let `K` be a number field, `K'` a separable closure, `A` a place of `K'` over a finite prime of `K`
(so that `D_A = stabSubgroup A` is a decomposition group), and `H ≤ D_A` a subgroup isomorphic to
the absolute Galois group `Gal(κ'/κ)` of a `p`-adic field `κ`.  Then, given the local form of
Neukirch's Korollar 1, the relative index `[D_A : H]` is non-zero, i.e. `H` has finite index in
`D_A`.

The index is transported along the local correspondence `D_A ≅ Gal(L'/L)` for
`L = 𝔭.adicCompletion K`, which is valid for arbitrary subgroups and hence needs no closedness
hypothesis on `H`. -/
theorem relIndex_pos_of_localKorollar1 {K K' κ κ' : Type u} [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Field κ] [Field κ'] [Algebra κ κ'] [IsSepClosure κ κ']
    (h : NK.Indecomposed.LocalKorollar1 κ κ') (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') ≠ ⊤) (H : Subgroup Gal(K'/K))
    (hHle : H ≤ NK.BrauerTwist.stabSubgroup A) (hκ : Nonempty (H ≃* Gal(κ'/κ))) :
    0 < H.relIndex (NK.BrauerTwist.stabSubgroup A) := by
  classical
  obtain ⟨𝔭, h𝔭⟩ := exists_heightOneSpectrum_eq_comap A hA
  obtain ⟨e⟩ :=
    NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_localGalois 𝔭 A h𝔭
  show 0 < H.relIndex (NK.Mine.decompositionGroupOf K K' A)
  have hD' : H ≤ NK.Mine.decompositionGroupOf K K' A := hHle
  -- the image of `H` under the local correspondence is isomorphic to `Gal(κ'/κ)`
  have hmap : Nonempty
      (((H.subgroupOf (NK.Mine.decompositionGroupOf K K' A)).map
        (e : ↥(NK.Mine.decompositionGroupOf K K' A) →*
          Gal(SeparableClosure (𝔭.adicCompletion K)/𝔭.adicCompletion K))) ≃*
        Gal(κ'/κ)) := by
    obtain ⟨hκe⟩ := hκ
    exact ⟨(Subgroup.equivMapOfInjective (H.subgroupOf (NK.Mine.decompositionGroupOf K K' A))
        (e : ↥(NK.Mine.decompositionGroupOf K K' A) →*
          Gal(SeparableClosure (𝔭.adicCompletion K)/𝔭.adicCompletion K)) e.injective).symm.trans
      ((Subgroup.subgroupOfEquivOfLe hD').trans hκe)⟩
  -- Korollar 1 in its local form, at the completion of `K` at `𝔭`
  have hloc := h K 𝔭 (SeparableClosure (𝔭.adicCompletion K)) _ hmap
  -- transport the finiteness back along the local correspondence
  have h1 : (H.subgroupOf (NK.Mine.decompositionGroupOf K K' A)).relIndex ⊤ =
      H.relIndex (NK.Mine.decompositionGroupOf K K' A) := by
    rw [← Subgroup.subgroupOf_self (NK.Mine.decompositionGroupOf K K' A)]
    exact Subgroup.relIndex_subgroupOf (H := H) (K := NK.Mine.decompositionGroupOf K K' A)
      (L := NK.Mine.decompositionGroupOf K K' A) le_rfl
  rw [← h1, ← NK.LocalDecomposition.relIndex_map_eq_of_mulEquiv e
    (H.subgroupOf (NK.Mine.decompositionGroupOf K K' A))]
  exact hloc

end NK.Indecomposed

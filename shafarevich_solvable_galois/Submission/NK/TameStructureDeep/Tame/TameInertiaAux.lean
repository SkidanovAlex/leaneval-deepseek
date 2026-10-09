/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Auxiliary module for the pro-prime-to-`p` tame inertia

This module contains no mathematics of its own: it collects the imports and the *hints* that the
three lemmas

* `NK.TameStructureDeep.Tame.isProPrimeToP_of_openNormal_index`,
* `NK.TameStructureDeep.Tame.finrank_adjoin_dvd_of_pow_eq`,
* `NK.TameStructureDeep.Tame.coprime_finrank_of_le_tameClosure`

need, so that their proofs can be written without re-deriving the route.

## The route these three lemmas serve

The endgame is

```
NK.LocalTame.IsProPrimeToP (resCharAt 𝔭)
  ↥(NK.LocalTame.quotientImage (correctedWildInertia π) (inertiaSubgroup))
```

i.e. the tame inertia `I_κ/V_κ = Gal(κ^tr/κ^ur)` is pro-prime-to-`p`.  Write
`κ = 𝔭.adicCompletion K`, `U₀ = unramifiedClosure p ⊆ K'`, `T = tameClosure p π ⊆ K'`,
`I = U₀.fixingSubgroup ≤ Gal(K'/κ)` and `V = T.fixingSubgroup ≤ I`.

`Gal(κ^tr/κ^ur)` is a *profinite* group, so — because the library's `IsProPrimeToP` is the
finite-quotient formulation — it suffices to test the **open** normal subgroups
(`isProPrimeToP_of_openNormal_index`: this is the exact analogue of the existing
`NK.TameStructureDeep.Support.isProP_of_openNormal_index`, whose proof is a template: from
"every open normal subgroup has index coprime to `p`" one derives *`p`-divisibility* of the
group by the compactness of the `p`-th power map, and a finite `p`-divisible group is trivial).

Open normal subgroups of `Gal(κ^tr/κ^ur)` correspond to finite extensions `L/κ^ur` inside `κ^tr`,
and their index is `[L : κ^ur]`.  So everything reduces to the *arithmetic* statement
`coprime_finrank_of_le_tameClosure`: **a finite extension `L/κ^ur` inside `κ^tr` has degree prime
to `p`** — which is `finrank_adjoin_dvd_of_pow_eq` applied to the Kummer layers.

## Hints for `coprime_finrank_of_le_tameClosure`

* `L : IntermediateField ↥U₀ K'` with `(L : Set K') ⊆ (T : Set K')` and `FiniteDimensional ↥U₀ L`.
* `Algebra ↥U₀ ↥L` and `FiniteDimensional ↥U₀ ↥L` are instances
  (`Mathlib/FieldTheory/IntermediateField/Basic.lean`, `shortcut_instances`).
* `Field.exists_primitive_element ↥U₀ ↥L` (needs `Algebra.IsSeparable ↥U₀ ↥L`, which follows from
  `Algebra.IsSeparable κ K'` by `Algebra.isSeparable_tower_top_of_isSeparable` (top) together with
  `Algebra.IsSeparable.of_algHom` applied to the inclusion `↥L →ₐ[↥U₀] K'`) gives `α : ↥L` with
  `↥U₀⟮α⟯ = ⊤`; then `L = IntermediateField.adjoin ↥U₀ {α.1}` via
  `IntermediateField.lift_adjoin_simple` together with `IntermediateField.lift_top`.
* `α.1 ∈ T` because `α ∈ L` and `(L : Set K') ⊆ (T : Set K')`, so
  `NK.TameStructureDeep.Tame.exists_kummerLayer_of_mem_tameClosure` gives `n`, `β` with
  `¬ p ∣ n`, `β ^ n = algebraMap κ K' π` and `α.1 ∈ U₀ ⊔ κ⟮β⟯`.
* Since `U₀ ⊔ κ⟮β⟯ ≤ (IntermediateField.adjoin ↥U₀ {β}).restrictScalars κ`
  (`IntermediateField.restrictScalars` has the *same carrier*, `coe_restrictScalars`; use
  `sup_le_iff` and `IntermediateField.adjoin_le_iff`), we get
  `L ≤ IntermediateField.adjoin ↥U₀ {β}`.
* `Module.finrank ↥U₀ L ∣ Module.finrank ↥U₀ (adjoin ↥U₀ {β})` (tower formula
  `Module.finrank_mul_finrank`).
* `NK.TameStructureDeep.Tame.finrank_adjoin_dvd_of_pow_eq` is being proved separately in the
  module `Submission.NK.TameStructureDeep.Tame.finrank_adjoin_dvd_of_pow_eq`; if that module is
  already available, import it and use it here, otherwise prove that statement inline (it is a
  short independent fact).  With `F := ↥U₀`, `E := K'`, which is Galois over `↥U₀` by
  `IsGalois.tower_top_of_isGalois`/`IsSepClosure.isGalois`; and with
  `hμ : ∀ ζ, ζ ^ n = 1 → ζ ∈ (⊥ : IntermediateField ↥U₀ K')` supplied by
  `NK.TameStructureDeep.Tame.mem_unramifiedClosure_of_pow_eq_one`) gives
  `finrank ↥U₀ (adjoin ↥U₀ {β}) ∣ n`.
* `¬ p ∣ n` and `p` prime finish it (`Nat.Prime.coprime_iff_not_dvd`).

## Hints for `finrank_adjoin_dvd_of_pow_eq`

Let `L = F⟮α⟯`, `hα : α ^ n = algebraMap F E a`, `hα0 : α ≠ 0`.  The map

  `φ : Gal(E/F) →* rootsOfUnity n E`,  `σ ↦ σ α * α⁻¹`

is well defined because `(σ α * α⁻¹) ^ n = σ a * a⁻¹ = 1`, and is a group homomorphism because
`τ α * α⁻¹` lies in `⊥ : IntermediateField F E` (by `hμ`), hence is fixed by `σ`.  Its kernel is
`L.fixingSubgroup` (an element of `Gal(E/F)` fixes `α` iff it fixes `F⟮α⟯`), so
`Nat.card φ.range = L.fixingSubgroup.index = Module.finrank F L`
(`IntermediateField.finrank_eq_fixingSubgroup_index`, valid for the Galois extension `E/F` even
when `E/F` is infinite-dimensional; `Subgroup.index` *is* `Nat.card` of the quotient).
Finally `φ.range ≤ rootsOfUnity n E`, the group of `n`-th roots of unity is cyclic
(`rootsOfUnity.isCyclic`), and its cardinality divides `n` because every element has order
dividing `n` (`IsCyclic` plus `orderOf`); so `Module.finrank F L ∣ n`.
-/
import Mathlib
import Submission.NK.TameStructureDeep.Tame.TameClosure
import Submission.NK.TameStructureDeep.Tame.Defs
import Submission.NK.TameStructureDeep.Tame.isGalois_tameClosure
import Submission.NK.TameStructureDeep.Tame.exists_kummerLayer_of_mem_tameClosure
import Submission.NK.ProfiniteP.ProPCore.totallyDisconnectedSpace_quotient
import Submission.NK.TameStructure.ProfiniteAux.fixingSubgroup_isClosed_of_isIntegral
import Submission.NK.TameStructureDeep.Support.isProP_of_openNormal_index_prime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameStructureDeep.Tame

end NK.TameStructureDeep.Tame

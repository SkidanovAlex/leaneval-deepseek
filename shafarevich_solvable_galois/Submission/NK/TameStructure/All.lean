/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.TameStructure`: the local ramification/structure inputs for `p`-adic fields

Umbrella module of `Submission/Work/TameStructure/` (namespace `NK.TameStructure`).
Import this for the whole chapter (except the place-vocabulary wrapper `Places.lean`).

## What this chapter does

For a number field `K`, a finite prime `𝔭` of `K`, the local field `κ = K_𝔭 = 𝔭.adicCompletion K`
of residue characteristic `p` and `K'` a separable closure of `κ`, this chapter supplies the local
structure theory of the absolute Galois group `G_κ = Gal(K'/κ)` in the form in which the
Neukirch–Uchida development consumes it, namely instances of the three structures of the reduced
input catalogue `Submission/Work/TameData/Definitions.lean`:

| structure | theorem | reference |
|---|---|---|
| `NK.TameData.TameInertiaInput p (K_𝔭) K'` | `NK.TameStructure.tameInertiaInput_adicCompletion` | NSW (7.5.7) Cor., (7.5.11); Iwasawa |
| `NK.LocalStructure.TameFrobeniusCore p q (K_𝔭) K'` | `NK.TameStructure.tameFrobeniusCore_adicCompletion` | NSW (12.1.8); Iwasawa |
| `NK.TameData.TameAbelianisationInput p q (K_𝔭) K'` | `NK.TameStructure.tameAbelianisationInput_adicCompletion` | Shimizu 2.1, via local CFT |

with `q = NK.LocalStructure.residueCard K 𝔭`, and the bundle

* `NK.TameStructure.tameDataInput_adicCompletion` — `NK.TameData.TameDataInput p q (K_𝔭) K'`;
* `NK.TameStructure.tameData_adicCompletion` — `NK.LocalTame.TameData p q (K_𝔭) K'`;
* `NK.TameStructure.tameDataInputs_atPlace` (`Places.lean`) — `NK.ResidueFrob.TameDataInputs K K' A`
  at every finite place `A`, the bundle the endgame consumes;
* `NK.TameStructure.frobeniusLiftCharacterisation_adicCompletion` — the packaged Frobenius
  characterisation `NK.LocalTame.FrobeniusLiftCharacterisation` (NSW (12.1.8)).

## The named classical inputs

Everything reduces to the named inputs of `NK.TameStructure.Defs`, listed with their references:

| input | content | reference |
|---|---|---|
| `NK.TameStructure.UnramifiedZhat` | `Gal(κ(μ_{p'})/κ) ≅ Ẑ` | NSW (7.5.6), (7.5.7) Cor.; Serre V §4 |
| `NK.TameStructure.TameInertiaStructure` | `I_κ/V_κ` maximal closed normal pro-cyclic, pro-prime-to-`p`, and `V_κ` closed | NSW (7.5.7) Cor., (7.5.11); Iwasawa; Serre IV §2 |
| `NK.TameStructure.FrobeniusNormalisation` | the two halves of the Frobenius normalisation | NSW (12.1.8); Iwasawa |
| `NK.TameStructure.TameAbelianisationStructure` | `G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}` | Shimizu, arXiv:2009.10431, 2.1 |
| `NK.TameStructure.UnitsStructure` | `κˣ^{∧} ⧸ (pro-p part) ≅ Ẑ × μ_{q-1}` | Serre II §5 |

`NK.TameStructure.TameStructureInputs` bundles the first four (plus `CharP` of the residue
field); `NK.TameStructure.TameAbelianisationViaUnits` is the `κˣ`-form of Shimizu's lemma, from
which the abelianisation component is derived
(`NK.TameStructure.tameAbelianisationStructure_of_unitsTameQuotient`).

## What is *proved* here rather than named

* **The Galois-correspondence bridge** `Gal(K'/κ) ⧸ I_κ ≅ Gal(κ(μ_{p'})/κ)`
  (`NK.TameStructure.quotient_inertiaSubgroup_mulEquiv_unramifiedClosure`, `GaloisBridge.lean`),
  which converts `UnramifiedZhat` into the field `unramifiedQuotient` of `TameInertiaInput`.
* **The commutator relation `[I_κ, I_κ] ≤ V_κ` is *derived*, not assumed**: it follows from the
  *maximality* of `I_κ/V_κ` alone, using that `V_κ` is closed so that `I_κ/V_κ` is a pro-cyclic
  *profinite* group and hence abelian
  (`NK.TameStructure.tameInertia_commutator_mem`,
  `NK.TameStructure.ProfiniteAux.commutator_mem_of_isMaxNormalProCyclicInQuotient`,
  `NK.TameStructure.ProfiniteAux.fixingSubgroup_isClosed_of_isIntegral`).
* The arithmetic `q = p ^ f` for `κ = K_𝔭`
  (`NK.TameStructure.residueCard_eq_pow`, from `CharP` of the residue field).
* The reduction of `TameAbelianisationStructure` to its `κˣ`-form
  (`NK.TameStructure.tameAbelianisationStructure_of_unitsTameQuotient`) and the equivalence of
  the structure of the units with a surjection `κˣ^{∧} →* Ẑ × μ_{q-1}` with pro-`p` kernel
  (`NK.TameStructure.unitsStructure_iff_exists_surjective`,
  `NK.TameStructure.unitsStructure_of_prod`).

See `README.md` for the full account, including precisely which classical statement each named
input stands for, and what would be needed to remove it.
-/
import Submission.NK.TameStructure.Defs
import Submission.NK.TameStructure.GaloisBridge
import Submission.NK.TameStructure.ProfiniteAux.commutator_mem_of_isMaxNormalProCyclicInQuotient
import Submission.NK.TameStructure.ProfiniteAux.fixingSubgroup_isClosed_of_isIntegral
import Submission.NK.TameStructure.Inertia
import Submission.NK.TameStructure.Frobenius
import Submission.NK.TameStructure.Abelianisation
import Submission.NK.TameStructure.Assembly
import Submission.NK.TameStructure.Compatibility
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

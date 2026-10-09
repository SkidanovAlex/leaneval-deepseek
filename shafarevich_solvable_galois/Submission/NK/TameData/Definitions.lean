/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The reduced input catalogue for `NK.LocalTame.TameData`

The deliverable asks for the classical structure theorem of the absolute Galois group `G_κ` of a
`p`-adic field `κ` in the packaged form

  `NK.LocalTame.TameData p q κ K'  =  TameStructureInput ∧ ResidueCardRecovery ∧
     FrobeniusLiftCharacterisation`.

The three components are theorems of the classical theory (NSW, *Cohomology of Number Fields*,
(7.5.7), (7.5.11) and (12.1.8); Iwasawa, *On Galois groups of local fields*; Shimizu,
arXiv:2009.10431, Lemma 2.1), none of which is available in Mathlib.  This file records the
*reduced* input statements — one per component, each strictly weaker than the component it
implies, each with its reference — together with the assembled catalogue `TameDataInput`.

| reduced input | implies | reference |
|---|---|---|
| `TameInertiaInput p κ K'` | `TameStructureInput p q κ K'` | NSW (7.5.7) Cor., (7.5.11); Iwasawa |
| `TameAbelianisationInput p q κ K'` | `ResidueCardRecovery p q κ K'` | Shimizu Lemma 2.1 (local CFT) |
| `NK.LocalStructure.TameFrobeniusCore p q κ K'` | `FrobeniusLiftCharacterisation p q κ K'` | NSW (12.1.8); Iwasawa |

The derivations are in `NK.TameData.Inertia`, `NK.TameData.Abelianisation` and
`NK.LocalStructure.Frobenius` respectively; the assembly is `NK.TameData.Main`.

## What is *not* an input here

`TameStructureInput` has eight fields, of which two are *proved* from the other six in this
development: `exists_frobeniusLift` follows from `unramifiedQuotient` and the non-triviality of
`Ẑ` (`NK.LocalStructure.Tame.exists_notMem_inertiaSubgroup_of_unramifiedQuotient`), and
`wildInertia_le_inertia` is the first component of `IsMaxNormalProCyclicInQuotient`.  `TameInertiaInput`
therefore carries only the arithmetic content of NSW (7.5.7)/(7.5.11).

Likewise `ResidueCardRecovery` has three fields, of which `hp` and `q_eq` are part of the
statement that `q` is the residue field order; `TameAbelianisationInput` records the classical
splitting `G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}` from which the third field (`card_torsion`) is *derived*
(`NK.TameData.Abelianisation`), using the torsion-freeness of `Ẑ`
(`NK.TameData.isMulTorsionFree_zhat`).
-/
import Mathlib
import Submission.NK.LocalTame.All
import Submission.NK.LocalStructure.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open NK.LocalTame

namespace NK.TameData

universe u

noncomputable section

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']

/-! ## Component 1: the structure of the tame quotient -/

/-- **The structure of the tame quotient of a `p`-adic field** (NSW, *Cohomology of Number
Fields*, (7.5.7) Corollary and (7.5.11); Iwasawa, *On Galois groups of local fields*), in reduced
form: everything about `G_κ^{tr} = G_κ/V_κ` except the two fields of
`NK.LocalTame.TameStructureInput` that are *proved* in this development.

* `isTameInertia` — `I_κ/V_κ` is the maximal closed normal pro-cyclic subgroup of `G_κ/V_κ`
  (this contains `V_κ ≤ I_κ`, the wild inertia is contained in the inertia subgroup);
* `isProPrimeToP_tameInertia` — the tame inertia is pro-prime-to-`p`, i.e. the maximal tamely
  ramified extension `κ^{tr}` of `κ` is `κ^ur(κ^{1/n} : (n,p) = 1)` with
  `Gal(κ^{tr}/κ^ur) ≅ ∏_{ℓ ≠ p} ℤ_ℓ`;
* `tameInertia_commutator_mem` — the abelian consequence of the pro-cyclicity: the commutator of
  two inertia elements lies in the wild inertia;
* `unramifiedQuotient` — `G_κ/I_κ ≅ Gal(κ^ur/κ) ≅ Ẑ`.

The two fields of `TameStructureInput` that are absent are supplied by
`NK.TameData.TameInertiaInput.toStructureInput`: `wildInertia_le_inertia` is the first component
of `isTameInertia`, and `exists_frobeniusLift` follows from `unramifiedQuotient`. -/
structure TameInertiaInput (p : ℕ) (κ K' : Type*) [Field κ] [Field K'] [Algebra κ K']
    [IsSepClosure κ K'] : Prop where
  hp : p.Prime
  /-- `I_κ/V_κ` is the maximal closed normal pro-cyclic subgroup of `G_κ^{tr}` -/
  isTameInertia : IsMaxNormalProCyclicInQuotient (wildInertiaSubgroup (κ := κ) (K' := K') p)
    (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p)
  /-- the tame inertia `I_κ/V_κ` is pro-prime-to-`p` -/
  isProPrimeToP_tameInertia :
    IsProPrimeToP p ↥(tameInertiaSubgroup (κ := κ) (K' := K') p)
  /-- the tame inertia is abelian modulo the wild inertia -/
  tameInertia_commutator_mem :
    ∀ y ∈ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p,
      ∀ z ∈ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p,
        y * z * y⁻¹ * z⁻¹ ∈ wildInertiaSubgroup (κ := κ) (K' := K') p
  /-- the unramified quotient is `Ẑ`: `G_κ/I_κ ≅ Ẑ` -/
  unramifiedQuotient : Nonempty
    ((Gal(K'/κ) ⧸ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) ≃* NK.LocalAnabelian.Zhat)

/-! ## Component 2: the residue field order from the torsion of the tame abelianisation -/

/-- **The structure of the abelianised tame quotient** (Shimizu, arXiv:2009.10431, Lemma 2.1,
via local class field theory), in the form in which the residue field order is read off:

  `G_κ^{tr,ab} = (G_κ/V_κ)^{ab} ≅ Ẑ × μ_{q-1}`.

The classical proof: local reciprocity gives `G_κ^{ab} ≅ κˣ^{∧}`; the structure theory of the
units gives `κˣ ≅ ℤ × μ_{q-1} × U¹` with `U¹ = 1 + 𝔪_κ` pro-`p` (the `p`-adic logarithm); killing
the wild inertia — a pro-`p` group, the image of which is the pro-`p` part `U¹^{∧}` — leaves
`Ẑ × μ_{q-1}`.  Taking torsion then recovers `q - 1 = Nat.card μ_{q-1}` (see
`NK.TameData.Abelianisation`). -/
structure TameAbelianisationInput (p q : ℕ) (κ K' : Type*) [Field κ] [Field K'] [Algebra κ K']
    [IsSepClosure κ K'] : Prop where
  hp : p.Prime
  /-- the residue field cardinality is a power of `p`, `q = p^f` with `f ≥ 1` -/
  q_eq : ∃ f : ℕ, 0 < f ∧ q = p ^ f
  /-- the abelianised tame quotient is `Ẑ × μ_{q-1}` -/
  nonempty_iso : Nonempty
    (tameAbelianization (κ := κ) (K' := K') p ≃*
      (NK.LocalAnabelian.Zhat × Multiplicative (ZMod (q - 1))))

/-! ## Shimizu's Lemma 2.1 in its literal form -/

/-- **Shimizu, arXiv:2009.10431, Lemma 2.1**: the torsion of the abelianised tame quotient
`G_κ^{tr,ab}` is *cyclic of order `q - 1`*, i.e. it is the group `μ_{q-1}` of roots of unity of
the residue field.

This is the literal form in which Shimizu's lemma is stated (the residue field order is the order
of the torsion of `G_κ^{tr,ab}`), and it is *weaker* than the splitting
`TameAbelianisationInput`: the splitting `G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}` exhibits the torsion as the
second factor.  Either form implies `ResidueCardRecovery` (`NK.TameData.Abelianisation`); this
one by a two-line computation, the splitting by using the torsion-freeness of `Ẑ`
(`NK.TameData.isMulTorsionFree_zhat`). -/
structure TameTorsionInput (p q : ℕ) (κ K' : Type*) [Field κ] [Field K'] [Algebra κ K']
    [IsSepClosure κ K'] : Prop where
  hp : p.Prime
  /-- the residue field cardinality is a power of `p`, `q = p^f` with `f ≥ 1` -/
  q_eq : ∃ f : ℕ, 0 < f ∧ q = p ^ f
  /-- the torsion of the abelianised tame quotient is cyclic of order `q - 1` -/
  nonempty_torsion_iso : Nonempty
    (↥(tameTorsion (κ := κ) (K' := K') p) ≃* Multiplicative (ZMod (q - 1)))

/-! ## The reduced input catalogue -/

/-- **The reduced input catalogue of the structure theorem for `G_κ`.**

Bundles the three reduced inputs: the structure of the tame quotient
(`TameInertiaInput`, NSW (7.5.7)/(7.5.11), Iwasawa), the splitting of the abelianised tame
quotient (`TameAbelianisationInput`, Shimizu Lemma 2.1) and the Frobenius normalisation
(`NK.LocalStructure.TameFrobeniusCore`, NSW (12.1.8), Iwasawa).  Their consequences are
assembled in `NK.TameData.Main`:

  `NK.TameData.TameDataInput.toTameData : TameDataInput p q κ K' → TameData p q κ K'`. -/
structure TameDataInput (p q : ℕ) (κ K' : Type*) [Field κ] [Field K'] [Algebra κ K']
    [IsSepClosure κ K'] : Prop where
  /-- the structure of the tame quotient: NSW (7.5.7) Corollary, (7.5.11); Iwasawa -/
  inertia : TameInertiaInput p κ K'
  /-- the splitting of the abelianised tame quotient: Shimizu, arXiv:2009.10431, Lemma 2.1 -/
  abelianisation : TameAbelianisationInput p q κ K'
  /-- the Frobenius normalisation: NSW (12.1.8) Lemma; Iwasawa -/
  frobenius : NK.LocalStructure.TameFrobeniusCore p q κ K'

end

end NK.TameData

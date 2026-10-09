/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `NK.TameData`: the structure theorem for the absolute Galois group of a `p`-adic field

Umbrella module of `Submission/Work/TameData/` (namespace `NK.TameData`).  Everything in this
directory is `sorry`-free and `axiom`-free.

The chapter packages the classical structure theorem of `G_κ = Gal(κ̄/κ)` for a `p`-adic field `κ`
in the form in which the Neukirch–Uchida development consumes it, namely

  `NK.LocalTame.TameData p q κ K'  =  TameStructureInput p q κ K' ∧ ResidueCardRecovery p q κ K'
     ∧ FrobeniusLiftCharacterisation p q κ K'`

(NSW, *Cohomology of Number Fields*, (7.5.7) Corollary, (7.5.11), (12.1.8); Iwasawa, *On Galois
groups of local fields*; Shimizu, arXiv:2009.10431, 2.1), for `q = #κ = p^f` the residue field
cardinality and `p` the residue characteristic.

## What is here

* **`Definitions`** (`NK.TameData.Definitions`) — the *reduced* input catalogue, one named input
  per component, each strictly weaker than the component it implies and each carrying its
  reference:
  `TameInertiaInput p κ K'` (the structure of the tame quotient; NSW (7.5.7)/(7.5.11), Iwasawa),
  `TameAbelianisationInput p q κ K'` (the splitting `G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}`; Shimizu 2.1 via
  local class field theory), `TameTorsionInput p q κ K'` (Shimizu's literal statement: the torsion
  of `G_κ^{tr,ab}` is cyclic of order `q - 1`), and the bundle `TameDataInput p q κ K'`.
* **`Inertia`** (`NK.TameData.Inertia`) — component 1: `TameInertiaInput.toStructureInput`.
  Two of the eight fields of `TameStructureInput` are *proved*: `wildInertia_le_inertia` (from
  `IsMaxNormalProCyclicInQuotient`) and `exists_frobeniusLift` (from `G_κ/I_κ ≅ Ẑ`).
* **`Torsion`** (`NK.TameData.Torsion`) — the `Nat.card` bookkeeping for torsion subgroups.
* **`Abelianisation`** (`NK.TameData.Abelianisation`) — component 2:
  `ResidueCardRecovery.of_torsionInput` and `ResidueCardRecovery.of_abelianisation`.
* **`Main`** (`NK.TameData.Main`) — the assembly `TameDataInput.toTameData` and its
  consequences: `le_inertia_of_tameData`, `exists_frobeniusLift_of_tameData`,
  `card_torsion_of_tameData`, `isFrobeniusFor_iff_of_tameData`, `residueCard_eq_of_tameData`.
* **`Adic`** (`NK.TameData.Adic`) — the number-field corollary:
  `NK.TameData.tameData_adicCompletion` gives
  `TameData p (residueCard K 𝔭) (𝔭.adicCompletion K) K'`, with
  `residueCard K 𝔭 = #(𝓞 K ⧸ 𝔭) = 𝔭.asIdeal.absNorm`.
* **`Zhat/isMulTorsionFree_zhat`** (`NK.TameData.Zhat.isMulTorsionFree_zhat`, registered as the
  instance `NK.TameData.instIsMulTorsionFreeZhat`) — **`Ẑ` is torsion-free** (`Ẑ = ∏_ℓ ℤ_ℓ` is a
  product of domains), proved from the description of the profinite completion as the limit of the
  finite quotients `ℤ ⧸ mℤ`.  This is the only group-theoretic input of the residue-cardinality
  recovery, and it is *proved* here rather than assumed; with the instance registered the
  statements above carry no `IsMulTorsionFree` hypothesis.
* **`Abelianisation/torsion_mulEquiv_zmod`** — the splitting `G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}` implies
  Shimizu's literal statement that the torsion is cyclic of order `q - 1`; see also
  `NK.TameData.TameAbelianisationInput.toTorsionInput`.
* **`Arithmetic/eq_of_prime_pow_eq_prime_pow`** — a prime is determined by any positive power of
  it, the step recovering the residue characteristic from `q = p ^ f`.
* **`Places`** (`NK.TameData.Places`, *not* imported here on purpose — see its header) — the same
  number-field corollary in the vocabulary of `Submission/Work/FrobeniusBridge/Basic.lean`
  (`localField A`, `localClosure A`), together with `exists_tameData_at_places`.

## What a caller imports

`import Submission.NK.TameData.All` for everything except the place-vocabulary wrapper, and
`import Submission.NK.TameData.Places` for that.

## What remains open

The three reduced inputs (`TameInertiaInput`, `TameAbelianisationInput`/`TameTorsionInput` and
`NK.LocalStructure.TameFrobeniusCore`) are the classical theorems named above; none of them is
available in Mathlib.  `README.md` documents, for each one, the exact reason it is not proved here
and what a future stretch would have to build.
-/
import Submission.NK.TameData.Torsion
import Submission.NK.TameData.Definitions
import Submission.NK.TameData.Inertia
import Submission.NK.TameData.Abelianisation
import Submission.NK.TameData.Main
import Submission.NK.TameData.Adic
import Submission.NK.TameData.Arithmetic.eq_of_prime_pow_eq_prime_pow
import Submission.NK.TameData.Zhat.isMulTorsionFree_zhat
import Submission.NK.TameData.Abelianisation.torsion_mulEquiv_zmod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

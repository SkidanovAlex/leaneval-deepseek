/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The structure theorem for `G_κ`, assembled

This is the assembly module of the chapter: `NK.TameData.TameDataInput` (the reduced input
catalogue of `Definitions.lean`) is turned into the packaged statement

  `NK.LocalTame.TameData p q κ K' = TameStructureInput p q κ K' ∧ ResidueCardRecovery p q κ K'
     ∧ FrobeniusLiftCharacterisation p q κ K'`

which is what `Submission/Work/LocalTame/` and `Submission/Work/FrobeniusBridge/` consume.

Two entry points are provided, according to which form of the residue-cardinality input is
available:

* `NK.TameData.TameDataInput.toTameData` from the splitting `G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}`
  (Shimizu, arXiv:2009.10431, 2.1, via local class field theory) — the classical form;
* `NK.TameData.tameData_of_torsionInput` from the literal statement that the torsion of
  `G_κ^{tr,ab}` is cyclic of order `q - 1` — this route needs no property of `Ẑ` at all.

The components themselves are derived in `NK.TameData.Inertia` (component 1),
`NK.TameData.Abelianisation` (component 2) and `NK.LocalStructure.Frobenius` (component 3,
imported).

## Consequences of `TameData`

Everything `TameData` bundles is available field by field, and the chapter records the following
consequences in the vocabulary of `NK.LocalTame`, for consumers who would rather not unfold the
structure:

* `NK.TameData.le_inertia_of_tameData` — `V_κ ≤ I_κ`;
* `NK.TameData.exists_frobeniusLift_of_tameData` — there is an element outside `I_κ`;
* `NK.TameData.card_torsion_of_tameData` — `#(G_κ^{tr,ab})_{tor} = q - 1`;
* `NK.TameData.isFrobeniusFor_iff_of_tameData` — the Frobenius normalisation (NSW (12.1.8));
* `NK.TameData.residueCard_eq_of_tameData` — two `TameData` at the *same* `p` over the same
  field force the same `q` (the cross-field version is `NK.LocalTame.residueCard_eq_of_tameData`,
  which uses the induced isomorphism `G_κ^{tr,ab} ≃* G_{κ₂}^{tr,ab}`).
-/
import Submission.NK.TameData.Definitions
import Submission.NK.TameData.Inertia
import Submission.NK.TameData.Abelianisation
import Submission.NK.LocalStructure.Frobenius.frobeniusLiftCharacterisation_of_core
import Submission.NK.TameData.Arithmetic.eq_of_prime_pow_eq_prime_pow
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open NK.LocalTame

set_option linter.unusedSectionVars false

namespace NK.TameData

universe u

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K'] [IsSepClosure κ K']

/-! ## The assembly -/

/-- **The structure theorem of `G_κ` for a `p`-adic field `κ`**, from the reduced input catalogue
`TameDataInput`: the wild inertia is the maximal closed normal pro-`p` subgroup and lies in the
inertia subgroup, the tame inertia is the maximal closed normal pro-cyclic pro-prime-to-`p`
subgroup of the tame quotient and is abelian modulo the wild inertia, `G_κ/I_κ ≅ Ẑ` and a
Frobenius lift exists (NSW (7.5.7), (7.5.11); Iwasawa); the torsion of the abelianised tame
quotient is cyclic of order `q - 1` (Shimizu, arXiv:2009.10431, 2.1); and the Frobenius lifts are
exactly the elements acting on the tame inertia by the `q`-th power map (NSW (12.1.8), Iwasawa). -/
theorem TameDataInput.toTameData {p q : ℕ} (h : TameDataInput p q κ K') :
    TameData p q κ K' where
  structure_input := h.inertia.toStructureInput h.abelianisation.q_eq
  residueCard := ResidueCardRecovery.of_abelianisation h.abelianisation
  frobeniusLift :=
    NK.LocalStructure.Frobenius.frobeniusLiftCharacterisation_of_core h.frobenius
      h.inertia.tameInertia_commutator_mem

/-- **The structure theorem from the three components separately.** -/
theorem tameData_of_components {p q : ℕ} (hI : TameInertiaInput p κ K')
    (hA : TameAbelianisationInput p q κ K')
    (hF : NK.LocalStructure.TameFrobeniusCore p q κ K') : TameData p q κ K' :=
  TameDataInput.toTameData ⟨hI, hA, hF⟩

/-- **The structure theorem from the literal form of Shimizu's 2.1** (the torsion of
`G_κ^{tr,ab}` is cyclic of order `q - 1`), which needs no property of `Ẑ`. -/
theorem tameData_of_torsionInput {p q : ℕ} (hI : TameInertiaInput p κ K')
    (hT : TameTorsionInput p q κ K') (hF : NK.LocalStructure.TameFrobeniusCore p q κ K') :
    TameData p q κ K' where
  structure_input := hI.toStructureInput hT.q_eq
  residueCard := ResidueCardRecovery.of_torsionInput hT
  frobeniusLift :=
    NK.LocalStructure.Frobenius.frobeniusLiftCharacterisation_of_core hF
      hI.tameInertia_commutator_mem

/-! ## Consequences of `TameData` -/

/-- `V_κ ≤ I_κ` for a `p`-adic field with the packaged structure theorem. -/
theorem le_inertia_of_tameData {p q : ℕ} (h : TameData p q κ K') :
    wildInertiaSubgroup (κ := κ) (K' := K') p ≤
      NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p :=
  h.structure_input.wildInertia_le_inertia

/-- There are elements of `G_κ` outside the inertia subgroup — the extension of `Ẑ` by the tame
inertia splits. -/
theorem exists_frobeniusLift_of_tameData {p q : ℕ} (h : TameData p q κ K') :
    ∃ x : Gal(K'/κ), x ∉ NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p :=
  h.structure_input.exists_frobeniusLift

/-- The order of the residue field of `κ` is the order of the torsion of the abelianised tame
quotient, plus one: `#(G_κ^{tr,ab})_{tor} = q - 1` (Shimizu, arXiv:2009.10431, 2.1). -/
theorem card_torsion_of_tameData {p q : ℕ} (h : TameData p q κ K') :
    Nat.card (tameTorsion (κ := κ) (K' := K') p) = q - 1 :=
  h.residueCard.card_torsion

/-- **The Frobenius normalisation** (NSW (12.1.8), Iwasawa): an element of `G_κ` acts on the
prime-to-`p` roots of unity by `ζ ↦ ζ ^ q` if and only if it lies outside `I_κ` and acts on the
tame inertia `I_κ/V_κ` by the `q`-th power map. -/
theorem isFrobeniusFor_iff_of_tameData {p q : ℕ} (h : TameData p q κ K') (x : Gal(K'/κ)) :
    NK.LocalAnabelian.IsFrobeniusFor (κ := κ) (K' := K') p q x ↔
      IsTameFrobeniusLift q (wildInertiaSubgroup (κ := κ) (K' := K') p)
        (NK.LocalAnabelian.inertiaSubgroup (κ := κ) (K' := K') p) x :=
  h.frobeniusLift.iff x

/-- **Two `TameData` over the same field at the same residue characteristic force the same residue
field order.**  Both compute `Nat.card (tameTorsion p)` as `q - 1` resp. `q' - 1`. -/
theorem residueCard_eq_of_tameData {p q q' : ℕ} (h : TameData p q κ K')
    (h' : TameData p q' κ K') : q = q' := by
  have h1 := h.residueCard.card_torsion_add_one
  have h2 := h'.residueCard.card_torsion_add_one
  omega

/-- **Two `TameData` over the same field with the same residue field order force the same residue
characteristic**: `q = p ^ f = p' ^ f'` with `p`, `p'` prime and `f, f' > 0`
(`NK.TameData.Arithmetic.eq_of_prime_pow_eq_prime_pow`). -/
theorem residueChar_eq_of_tameData {p p' q : ℕ} (h : TameData p q κ K')
    (h' : TameData p' q κ K') : p = p' := by
  obtain ⟨f, hf, hqf⟩ := h.structure_input.q_eq
  obtain ⟨g, hg, hqg⟩ := h'.structure_input.q_eq
  exact Arithmetic.eq_of_prime_pow_eq_prime_pow h.structure_input.hp h'.structure_input.hp hf hg
    (by rw [← hqf, hqg])

end NK.TameData

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Frobenius normalisation, from the residual of `NK.TameStructureDeep`

This file turns the Frobenius fields of `NK.TameStructureDeep.TameRamificationCore` — the
existence of the normalised Frobenius (NSW (7.5.6)) and the two directions of the Frobenius
normalisation (NSW (12.1.8) Lemma; Iwasawa) — into

* `NK.LocalStructure.TameFrobeniusCore p q κ K'`,
* `NK.LocalTame.FrobeniusLiftCharacterisation p q κ K'`,
* `NK.LocalAnabelian.ResidueCardInput p q κ K'` (the data-carrying form of the existence of
  the Frobenius).
-/
import Submission.NK.TameStructureDeep.Defs
import Submission.NK.LocalStructure.Defs
import Submission.NK.LocalTame.Inputs

open scoped Classical

namespace NK.TameStructureDeep

universe u

noncomputable section

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']

/-- **The Frobenius normalisation core** (NSW (12.1.8); Iwasawa) from the residual: the existence
of an element which both acts on the prime-to-`p` roots of unity by `ζ ↦ ζ^q` and conjugates the
tame inertia by the `q`-th power map, and the converse implication. -/
theorem tameFrobeniusCore_of_core {p q : ℕ} [IsSepClosure κ K']
    (h : TameRamificationCore p q κ K') :
    NK.LocalStructure.TameFrobeniusCore p q κ K' where
  hp := h.hp
  exists_frob := h.exists_isFrobeniusFor_and_isTameFrobeniusLift
  actsAsFrobenius_of_isTameFrobeniusLift := fun _x hx =>
    h.actsAsFrobenius_of_isTameFrobeniusLift hx

/-- **The packaged Frobenius characterisation** `NK.LocalTame.FrobeniusLiftCharacterisation` from
the residual: the two predicates `IsFrobeniusFor p q` and `IsTameFrobeniusLift q V_κ I_κ` are
equivalent. -/
theorem frobeniusLiftCharacterisation_of_core {p q : ℕ} (h : TameRamificationCore p q κ K') :
    NK.LocalTame.FrobeniusLiftCharacterisation p q κ K' where
  hp := h.hp
  iff := h.frobenius_iff

/-- **The canonical Frobenius as `NK.LocalAnabelian.ResidueCardInput`**: the data-carrying form
of the existence of the Frobenius, obtained from the residual of the element supplied by
`exists_frobenius`. -/
noncomputable def residueCardInput_of_core {p q : ℕ} [IsSepClosure κ K']
    (h : TameRamificationCore p q κ K') :
    NK.LocalAnabelian.ResidueCardInput p q κ K' where
  hp := h.hp
  frob := h.exists_frobenius.choose
  frob_notMem_inertia := h.exists_frobenius.choose_spec.1
  actsAsFrobenius := h.exists_frobenius.choose_spec.2

/-! ## The boundary form at a `𝔭`-adic completion -/

/-- **The Frobenius normalisation `NK.LocalStructure.TameFrobeniusCore` at a genuine local field
`κ = K_𝔭`** (NSW (12.1.8) Lemma; Iwasawa), from the residual. -/
theorem tameFrobeniusCore_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    {p q : ℕ} (h : TameRamificationCore p q (𝔭.adicCompletion K) K') :
    NK.LocalStructure.TameFrobeniusCore p q (𝔭.adicCompletion K) K' :=
  tameFrobeniusCore_of_core h

end

end NK.TameStructureDeep

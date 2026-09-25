/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The abelianised tame quotient, from the residual of `NK.TameStructureDeep`

This file turns the abelianisation field of `NK.TameStructureDeep.TameRamificationCore` — the
classical splitting `G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}` of Shimizu (arXiv:2009.10431, Lemma 2.1, via local
class field theory) — into the structures

* `NK.TameData.TameAbelianisationInput p q κ K'` (the splitting; `q_eq` supplied separately, and
  *proved* from the arithmetic of the completion when `κ = K_𝔭` and `q = residueCard K 𝔭`), and
* `NK.TameData.TameTorsionInput p q κ K'` (Shimizu's literal statement: the torsion of
  `G_κ^{tr,ab}` is cyclic of order `q - 1`), via
  `NK.TameData.TameAbelianisationInput.toTorsionInput`.
-/
import Submission.NK.TameStructureDeep.Defs
import Submission.NK.TameData.Abelianisation
import Submission.NK.LocalStructure.Tame.residueCard_eq_pow_of_charP

open scoped Classical
open IsDedekindDomain.HeightOneSpectrum

namespace NK.TameStructureDeep

universe u

noncomputable section

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']

/-- **Shimizu's splitting from the residual.**  The hypothesis `q_eq` — that `q` is a positive
power of the prime `p` — is the elementary arithmetic statement that `q` is the order of a finite
field of characteristic `p`; for a genuine local field it is *proved* by
`NK.TameStructureDeep.tameAbelianisationInput_adicCompletion`. -/
theorem tameAbelianisationInput_of_core {p q : ℕ} [IsSepClosure κ K']
    (hq : ∃ f : ℕ, 0 < f ∧ q = p ^ f)
    (h : TameRamificationCore p q κ K') :
    NK.TameData.TameAbelianisationInput p q κ K' where
  hp := h.hp
  q_eq := hq
  nonempty_iso := h.abelianisation

/-- **Shimizu's literal torsion statement from the residual** (arXiv:2009.10431, Lemma 2.1): the
torsion of the abelianised tame quotient is cyclic of order `q - 1`. -/
theorem tameTorsionInput_of_core {p q : ℕ} [IsSepClosure κ K']
    (hq : ∃ f : ℕ, 0 < f ∧ q = p ^ f)
    (h : TameRamificationCore p q κ K') :
    NK.TameData.TameTorsionInput p q κ K' :=
  (tameAbelianisationInput_of_core hq h).toTorsionInput

/-! ## The arithmetic `q = p ^ f` for a genuine local field -/

/-- **`q = #(𝒪_κ/𝔪_κ)` is a positive power of the residue characteristic.**  This is the `q_eq`
field of the reduced input catalogue, *proved* here rather than assumed: the residue field of
`κ = K_𝔭` is `𝓞 K ⧸ 𝔭`, a finite field of characteristic `p`
(`NK.LocalStructure.Tame.residueCard_eq_pow_of_charP`). -/
theorem q_eq_of_charP {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hp : p.Prime) (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    ∃ f : ℕ, 0 < f ∧ NK.LocalStructure.residueCard K 𝔭 = p ^ f :=
  NK.LocalStructure.Tame.residueCard_eq_pow_of_charP 𝔭 hp hchar

/-- **Shimizu's splitting at a genuine local field**, from the residual with
`q = NK.LocalStructure.residueCard K 𝔭`: the arithmetic `q = p^f` is *proved* from `CharP` of the
residue field, so it is not an extra input. -/
theorem tameAbelianisationInput_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (h : TameRamificationCore p (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K) K') :
    NK.TameData.TameAbelianisationInput p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K' :=
  tameAbelianisationInput_of_core (q_eq_of_charP 𝔭 h.hp hchar) h

/-- **Shimizu's torsion statement at a genuine local field.** -/
theorem tameTorsionInput_adicCompletion {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type u}
    [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K'] {p : ℕ}
    (hchar : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p)
    (h : TameRamificationCore p (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K) K') :
    NK.TameData.TameTorsionInput p (NK.LocalStructure.residueCard K 𝔭)
      (𝔭.adicCompletion K) K' :=
  (tameAbelianisationInput_adicCompletion 𝔭 hchar h).toTorsionInput

end

end NK.TameStructureDeep

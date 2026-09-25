/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `G_1` is the wild inertia: unconditional forms

`NK.RamificationDeep.coprime_natCard_quotient_zero` and
`NK.RamificationDeep.isWildInertia_ramificationSubgroup_one_of_residue` take the unit count
`Nat.card ((A ⧸ 𝔪_A)ˣ) = p^f - 1` as an explicit hypothesis; it is discharged here by
`NK.RamificationDeep.natCard_units_residueField`, so that the two headline consequences of the
embedding `G_0/G_1 ↪ (A/𝔪_A)^×` become unconditional in terms of the residue cardinality.

For a finite Galois extension `L/K` of `p`-adic fields with valuation ring `A` of uniformizer `π`
the only remaining hypotheses are then the residue cardinality `q = p^f` and the termination of
the ramification filtration, both automatic in that setting
(`NK.Ramification.exists_ramificationSubgroup_eq_bot`).
-/
import Mathlib
import Submission.NK.RamificationDeep.WildInertia
import Submission.NK.RamificationDeep.natCard_units_residueField

set_option linter.style.haveILetI false

open scoped Pointwise

namespace NK.RamificationDeep

universe u

noncomputable section

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
variable {A : ValuationSubring L} [IsDiscreteValuationRing A] {π : A} {E : IntermediateField K L}

/-- **`p` is coprime to `#(G_0/G_1)`**, unconditionally in the residue cardinality: the residue
field has `p^f` elements, `G_0/G_1` embeds into `(A/𝔪_A)^×`, and the latter has `p^f - 1`
elements, which is prime to `p`. -/
theorem coprime_natCard_quotient_zero_of_card (D : UniformizerData (K := K) A π E) {p f : ℕ}
    (hp : p.Prime) (hf : 0 < f) (hq : Nat.card (A ⧸ IsLocalRing.maximalIdeal A) = p ^ f) :
    Nat.Coprime p
      (Nat.card (↥(NK.Ramification.ramificationSubgroup (K := K) A 0) ⧸
        (NK.Ramification.ramificationSubgroup (K := K) A 1).subgroupOf
          (NK.Ramification.ramificationSubgroup (K := K) A 0))) :=
  coprime_natCard_quotient_zero (K := K) D hp hf
    (natCard_units_residueField (K := K) A hq)

/-- **`G_1` is the wild inertia of `G_0`**, with the unit-count hypothesis discharged: the only
hypotheses are that the residue field has `p^f` elements and that the filtration terminates at
level `1 + N`. -/
theorem isWildInertia_ramificationSubgroup_one_of_card (D : UniformizerData (K := K) A π E)
    [Finite ↥(A.decompositionSubgroup K)] {p f N : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hq : Nat.card (A ⧸ IsLocalRing.maximalIdeal A) = p ^ f)
    (hbot : NK.Ramification.ramificationSubgroup (K := K) A (1 + N) = ⊥) :
    NK.LocalTame.IsWildInertia p
      ↥(NK.Ramification.ramificationSubgroup (K := K) A 0)
      ((NK.Ramification.ramificationSubgroup (K := K) A 1).subgroupOf
        (NK.Ramification.ramificationSubgroup (K := K) A 0)) :=
  isWildInertia_ramificationSubgroup_one_of_residue (K := K) D hp hf hq
    (natCard_units_residueField (K := K) A hq) hbot

end

end NK.RamificationDeep

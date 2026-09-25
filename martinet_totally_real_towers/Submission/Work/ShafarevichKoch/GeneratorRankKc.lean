import Mathlib
import Submission.Work.ShafarevichKoch.GeneratorRank
import Submission.Work.ShafarevichKoch.twoTorsion_card_sub_one
import Submission.Work.ShafarevichKoch.nonempty_embedding_quadraticLevel_twoTorsion
import Submission.Work.ShafarevichKoch.exists_embedding_fin31_quadraticLevel_Kc
import Submission.Work.ShafarevichKoch.nonempty_proTwoCharEquiv_option_quadraticLevel
import Submission.Work.ShafarevichKoch.CardKc
import Submission.Work.ShafarevichKoch.KcRank
import Submission.Work.ClassFieldTower.WitnessField

/-!
# `Work.ShafarevichKoch.GeneratorRankKc` -- item (1) of the deliverable for `Kc = ℚ(√-30030)`

The two halves of the arithmetic identification

```
d(G_∅) = rank₂ Cl(Kc) = 5,        G_∅ = Gal(Kc_∅/Kc),
```

proved in the Kummer-theoretic form of the deliverable:

* **upper bound** (Kummer, "every unramified `Z/2`-extension comes from a class of order `2`"):
  `#(QuadraticLevel Kc M) ≤ 2 ^ rank₂ Cl(Kc) - 1`, i.e. at most `31` unramified quadratic
  extensions, from the sharpened two-descent embedding
  `Work.ShafarevichKoch.nonempty_embedding_quadraticLevel_twoTorsion` (which uses
  `hunits_Kc`: the only non-square unit class `-1` is not a square in `Kc_∅`);
* **lower bound** (genus theory): the genus level of `Kc` produces `31` distinct quadratic levels.

Together with the infinite Galois correspondence they give
`#(QuadraticLevel Kc M) = 2 ^ rank₂ Cl(Kc) - 1` and `#(ProTwoChar Kc M) = 2 ^ rank₂ Cl(Kc)`,
i.e. `dim_{F₂} H¹(G_∅,𝔽₂) = rank₂ Cl(Kc) = 5`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

variable (M : MaximalUnramifiedProP.{0} Kc 2)

/-- **The quadratic levels of `Kc_∅/Kc` form a finite type.**  Forced by the sharpened Kummer
two-descent: they embed into the finite group `Cl(Kc)[2]` (with the trivial class excluded). -/
theorem finite_quadraticLevel_Kc : Finite (QuadraticLevel Kc M) := by
  obtain ⟨f⟩ := nonempty_embedding_quadraticLevel_twoTorsion Kc M (hunits_Kc M)
  exact Finite.of_injective f f.injective

/-- **The Kummer upper bound (item (1), upper half)**: every unramified quadratic extension of
`Kc` comes from a nontrivial class of order `2`, so there are at most
`2 ^ rank₂ Cl(Kc) - 1 = 31` of them. -/
theorem card_quadraticLevel_le_Kc :
    Nat.card (QuadraticLevel Kc M) ≤ 2 ^ classGroupTwoRank Kc - 1 := by
  obtain ⟨f⟩ := nonempty_embedding_quadraticLevel_twoTorsion Kc M (hunits_Kc M)
  haveI : Finite {c : ClassGroup (𝓞 Kc) // c ^ 2 = 1 ∧ c ≠ 1} := inferInstance
  exact le_trans (Nat.card_le_card_of_injective f f.injective) (le_of_eq (card_twoTorsion_ne_one Kc))

/-- The upper bound, numerically: at most `31` unramified quadratic extensions. -/
theorem card_quadraticLevel_le_thirtyone_Kc :
    Nat.card (QuadraticLevel Kc M) ≤ 31 := by
  have h := card_quadraticLevel_le_Kc M
  rw [classGroupTwoRank_Kc] at h
  norm_num at h
  exact h

/-- **The genus-theory lower bound (item (1), lower half)**: `Kc` has at least
`2 ^ rank₂ Cl(Kc) - 1 = 31` unramified quadratic extensions.  (The genus level of `Kc`,
`Work.ClassFieldTower.hasGenusLevel_witness`, produces `31` distinct quadratic levels.) -/
theorem card_quadraticLevel_ge_Kc :
    2 ^ classGroupTwoRank Kc - 1 ≤ Nat.card (QuadraticLevel Kc M) := by
  obtain ⟨f⟩ := exists_embedding_fin31_quadraticLevel_Kc M
  haveI := finite_quadraticLevel_Kc M
  have h : Nat.card (Fin 31) ≤ Nat.card (QuadraticLevel Kc M) :=
    Nat.card_le_card_of_injective f f.injective
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  rw [classGroupTwoRank_Kc]
  norm_num
  exact h

/-- **ITEM (1) OF THE DELIVERABLE, in Kummer form.**  `Kc = ℚ(√-30030)` has exactly
`2 ^ rank₂ Cl(Kc) - 1 = 31` unramified quadratic extensions, i.e. the Kummer two-descent is
*sharp*: the unramified quadratic extensions of `Kc` correspond bijectively to the nontrivial
classes of order `2` in `Cl(Kc)`.

Equivalently (by infinite Galois theory and the Burnside basis theorem for pro-`2` groups), the
generator rank of `G_∅ = Gal(Kc_∅/Kc)` is `log₂(#ProTwoChar) = log₂ 32 = 5 = rank₂ Cl(Kc)`; see
`card_proTwoChar_Kc` for the character-group form. -/
theorem card_quadraticLevel_Kc :
    Nat.card (QuadraticLevel Kc M) = 2 ^ classGroupTwoRank Kc - 1 :=
  le_antisymm (card_quadraticLevel_le_Kc M) (card_quadraticLevel_ge_Kc M)

/-- The same, numerically: `Kc` has exactly `31` unramified quadratic extensions. -/
theorem card_quadraticLevel_Kc_eq_thirtyone :
    Nat.card (QuadraticLevel Kc M) = 31 := by
  rw [card_quadraticLevel_Kc M, classGroupTwoRank_Kc]
  norm_num

/-- **The Kummer correspondence is exact**: the unramified quadratic extensions of `Kc` are
counted by the nontrivial classes of order `2` in the class group. -/
theorem card_quadraticLevel_eq_twoTorsion_Kc :
    Nat.card (QuadraticLevel Kc M)
      = Nat.card {c : ClassGroup (𝓞 Kc) // c ^ 2 = 1 ∧ c ≠ 1} := by
  rw [card_quadraticLevel_Kc M, card_twoTorsion_ne_one Kc]

/-- **ITEM (1) OF THE DELIVERABLE: `dim_{𝔽₂} H¹(G_∅, 𝔽₂) = rank₂ Cl(Kc) = 5`.**

`G_∅ = Gal(Kc_∅/Kc)` has exactly `2 ^ rank₂ Cl(Kc)` continuous characters with values in `𝔽₂`;
since `#ProTwoChar = 2 ^ d(G_∅)` (the characters form the dual of the Frattini quotient
`G_∅/Φ(G_∅)`), this says `d(G_∅) = rank₂ Cl(Kc) = 5`, the arithmetic identification of item (1):
the generator rank of the maximal unramified pro-`2` group is the `2`-rank of the class group. -/
theorem card_proTwoChar_Kc :
    Nat.card (ProTwoChar Kc M) = 2 ^ classGroupTwoRank Kc := by
  obtain ⟨e⟩ := nonempty_proTwoCharEquiv_option_quadraticLevel Kc M
  haveI : Finite (QuadraticLevel Kc M) := finite_quadraticLevel_Kc M
  haveI : Fintype (QuadraticLevel Kc M) := Fintype.ofFinite _
  have hopt : Nat.card (Option (QuadraticLevel Kc M)) = Nat.card (QuadraticLevel Kc M) + 1 := by
    rw [Nat.card_eq_fintype_card (α := Option (QuadraticLevel Kc M)),
      Fintype.card_option, Nat.card_eq_fintype_card (α := QuadraticLevel Kc M)]
  rw [Nat.card_congr e, hopt, card_quadraticLevel_Kc M]
  have h1 : 1 ≤ 2 ^ classGroupTwoRank Kc := Nat.one_le_two_pow
  omega

/-- The same, numerically: `G_∅` has exactly `32` characters, i.e. `d(G_∅) = 5`. -/
theorem card_proTwoChar_Kc_eq_thirtytwo : Nat.card (ProTwoChar Kc M) = 32 := by
  rw [card_proTwoChar_Kc M, classGroupTwoRank_Kc]
  norm_num

end Work.ShafarevichKoch

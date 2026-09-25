import Mathlib
import Submission.Work.ShafarevichKoch.card_quadraticLevel_le_of_unit_dichotomy
import Submission.Work.ShafarevichKoch.exists_sq_or_neg_sq_of_totallyComplex_quadratic
import Submission.Work.ShafarevichKoch.CardKc
import Submission.Work.ClassFieldTower.WitnessField

/-!
# `Work.ShafarevichKoch.ItemOneGeneral` -- item (1) of the deliverable in general form

The deliverable asks for the arithmetic identification

```
d(G_∅) = rank₂ Cl(F),        G_∅ = Gal(F_∅/F),
```

for an imaginary quadratic field `F`, in the Kummer-theoretic form

```
#(unramified quadratic levels of F_∅/F) ≤ 2 ^ rank₂ Cl(F) - 1      ("every unramified Z/2-extension
                                                                    of F comes from a class of
                                                                    order 2")
```

(`Work.ShafarevichKoch.card_unramifiedQuadraticLevels_le_classGroupTwoRank`, which is stated for an
arbitrary number field `F` under the hypothesis that a unit of `𝓞 F` which is a square in `F_∅` was
already a square in `F`).

This module assembles the two arithmetic facts that discharge that hypothesis for a
**totally complex quadratic field**:

* `Work.ShafarevichKoch.exists_sq_or_neg_sq_of_totallyComplex_quadratic`: every unit of `𝓞 F` is
  `±` a square in `Fˣ`, provided `-1` is not a square in `F` (a genuinely needed hypothesis: for
  `F = ℚ(i)` and the unit `i` it fails, since `i = ((1+i)/√2)²` only after adjoining `√2`);
* `Work.ShafarevichKoch.hunits_of_unit_dichotomy`: this dichotomy, together with "`-1` is not a
  square in `F_∅`", gives the sharpness hypothesis of the two-descent
  (`Work.ShafarevichKoch.hunits_of_unit_dichotomy`), the general form of the `Kc` proof in
  `CardKc.lean`.

## Main declarations

* `Work.ShafarevichKoch.card_quadraticLevel_le_of_totallyComplex_quadratic` -- item (1), upper
  half, for an arbitrary totally complex quadratic field with `-1 ∉ (F_∅^×)²`;
* `Work.ShafarevichKoch.card_quadraticLevel_le_of_totallyComplex_quadratic_Kc` -- the `Kc`
  instance, recovering `Work.ShafarevichKoch.card_quadraticLevel_le_Kc`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open scoped Classical
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- **Item (1), upper half, in general form.**  For a totally complex quadratic number field `F`
in which `-1` is not a square in the maximal unramified pro-`2` extension `F_∅`, the unramified
quadratic levels of `F_∅/F` embed into the nontrivial `2`-torsion of the class group; in
particular there are at most `2 ^ rank₂ Cl(F) - 1` of them. -/
theorem card_quadraticLevel_le_of_totallyComplex_quadratic (F : Type*) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] (h2 : Module.finrank ℚ F = 2)
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2)
    (hneg : ∀ z : M.K, z * z = -1 → False) :
    Nat.card (Work.ShafarevichKoch.QuadraticLevel F M) ≤
      2 ^ Work.ClassFieldTower.classGroupTwoRank F - 1 := by
  -- `-1` is not a square in `F` either, since `algebraMap` is injective.
  have hnegF : ∀ y : F, y * y = -1 → False := by
    intro y hy
    refine hneg (algebraMap F M.K y) ?_
    rw [← map_mul, hy, map_neg, map_one]
  exact card_quadraticLevel_le_of_unit_dichotomy F M
    (fun u => exists_sq_or_neg_sq_of_totallyComplex_quadratic F h2 hnegF u) hneg

/-- **Item (1), upper half, for `Kc`** -- the general theorem applied to the benchmark field
`Kc = ℚ(√-30030)`, recovering `Work.ShafarevichKoch.card_quadraticLevel_le_Kc`. -/
theorem card_quadraticLevel_le_of_totallyComplex_quadratic_Kc
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2) :
    Nat.card (QuadraticLevel Kc M) ≤ 2 ^ classGroupTwoRank Kc - 1 := by
  haveI : NumberField.IsTotallyComplex Kc := isTotallyComplex
  exact card_quadraticLevel_le_of_totallyComplex_quadratic Kc finrank_eq_two M
    (fun z hz => no_sqrt_neg_one_in_maximalUnramified M
      ⟨z, by rw [hz, map_neg, map_one]⟩)

end Work.ShafarevichKoch

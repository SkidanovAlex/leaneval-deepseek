import Mathlib
import Submission.Work.ShafarevichKoch.ItemOneGeneral
import Submission.Work.ShafarevichKoch.card_quadraticLevel_ge_of_hasGenusLevel
import Submission.Work.ShafarevichKoch.finite_quadraticLevel

/-!
# `Work.ShafarevichKoch.ItemOneEquality` -- item (1) as an *equality*, in general form

This module packages the two halves of item (1) of the deliverable for an arbitrary number field
`F`, with the arithmetic inputs made explicit:

* **lower half**: a genus level, i.e. an unramified exponent-`2` extension of degree `2 ^ 5`
  (`Work.ClassFieldTower.HasGenusLevel F`) gives `31` distinct unramified quadratic levels
  (`Work.ShafarevichKoch.card_quadraticLevel_ge_of_hasGenusLevel`; this is the general form of
  `exists_embedding_fin31_quadraticLevel_Kc`);
* **upper half**: the Kummer two-descent bounds the unramified quadratic levels by
  `2 ^ rank₂ Cl(F) - 1` whenever `F` is totally complex quadratic with `-1` not a square in `F_∅`
  (`Work.ShafarevichKoch.card_quadraticLevel_le_of_totallyComplex_quadratic`);
* **finiteness**: the level type is finite for *every* number field `F`
  (`Work.ShafarevichKoch.finite_quadraticLevel`), so the `Nat.card` statements are not vacuous
  (`Nat.card` of an infinite type is `0`).

Hence for such an `F` with `rank₂ Cl(F) = 5`, the unramified quadratic extensions of `F` correspond
*exactly* to the `31 = 2^5 - 1` nontrivial classes of order `2` in `Cl(F)`; equivalently
`d(G_∅) = 5 = rank₂ Cl(F)`.  This is item (1) of the deliverable, with the two arithmetic inputs
(lower and upper) explicit; for `F = Kc = ℚ(√-30030)` both are *proved* unconditionally
(`Work.ClassFieldTower.hasGenusLevel_witness`, `Work.ShafarevichKoch.hunits_Kc`,
`Work.ShafarevichKoch.no_sqrt_neg_one_in_maximalUnramified`), which is
`Work.ShafarevichKoch.card_quadraticLevel_Kc`.

## Main declarations

* `Work.ShafarevichKoch.card_quadraticLevel_eq_of_hasGenusLevel` -- item (1) as an equality.
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

/-- **ITEM (1) OF THE DELIVERABLE, as an equality, in general form.**

For a totally complex quadratic field `F` in which `-1` is not a square in `F_∅`, which admits a
genus level (an unramified exponent-`2` extension of degree `2^5`) and whose class group has
`2`-rank `5`, the unramified quadratic levels of `F_∅/F` are exactly `2 ^ rank₂ Cl(F) - 1 = 31`
in number: every unramified `ℤ/2`-extension of `F` comes from a class of order `2`, and every
nontrivial class of order `2` occurs. -/
theorem card_quadraticLevel_eq_of_hasGenusLevel (F : Type*) [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] (h2 : Module.finrank ℚ F = 2)
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2)
    (hgen : Work.ClassFieldTower.HasGenusLevel F)
    (hrank : Work.ClassFieldTower.classGroupTwoRank F = 5)
    (hneg : ∀ z : M.K, z * z = -1 → False) :
    Nat.card (QuadraticLevel F M) = 2 ^ Work.ClassFieldTower.classGroupTwoRank F - 1 := by
  haveI hfin : Finite (QuadraticLevel F M) := finite_quadraticLevel F M
  obtain ⟨e⟩ := card_quadraticLevel_ge_of_hasGenusLevel F hgen M
  have hge : 31 ≤ Nat.card (QuadraticLevel F M) := by
    have h := Nat.card_le_card_of_injective e e.injective
    rwa [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  have hle : Nat.card (QuadraticLevel F M) ≤
      2 ^ Work.ClassFieldTower.classGroupTwoRank F - 1 :=
    card_quadraticLevel_le_of_totallyComplex_quadratic F h2 M hneg
  rw [hrank] at hle ⊢
  norm_num at hle
  omega

end Work.ShafarevichKoch

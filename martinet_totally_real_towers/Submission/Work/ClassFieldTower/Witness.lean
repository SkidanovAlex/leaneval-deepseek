import Mathlib
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.Objects
import Submission.Work.ClassFieldTower.Tower
import Submission.Work.ClassFieldTower.Main
import Submission.Work.ClassFieldTower.WitnessField
import Submission.Work.ClassFieldTower.exists_imaginaryQuadratic_classGroupTwoRank_ge_five
import Submission.Work.ClassFieldTower.unitTwoRank_eq_one_of_imaginaryQuadratic
import Submission.Work.ClassFieldTower.exists_unramifiedLevel_of_infinite
import Submission.Work.ClassFieldTower.Asymptotic

/-!
# `Work.ClassFieldTower.Witness` -- the capstone: the infinite Hilbert `2`-class tower over `Kc`

The chapter's explicit imaginary quadratic field is

    `Kc = ℚ(√-30030)`,  `-30030 = -2·3·5·7·11·13`,

for which `Work.ClassFieldTower.exists_imaginaryQuadratic_classGroupTwoRank_ge_five` proves the
numerical genus-theory certificate `5 ≤ classGroupTwoRank Kc` (completely proved).

Given this, the ONLY remaining arithmetic input is the class-field-theoretic description of
`G_∅ = Gal((Kc)_∅/Kc)`: `d(G_∅) = rank₂ Cl(Kc)` and the Shafarevich--Koch relation bound, i.e.
`Work.ClassFieldTower.DeficiencyBoundInput Kc M` (`GolodShafarevichCertificate Kc M d r` without
the numerical field).  With it, `G_∅` is infinite and `Kc` has an infinite Hilbert `2`-class
field tower with constant root discriminant.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- `Kc = ℚ(√-30030)` is totally complex, as a global instance for this chapter. -/
instance : NumberField.IsTotallyComplex Kc := isTotallyComplex

theorem finrank_witness : Module.finrank ℚ Kc = 2 := finrank_eq_two

theorem unitTwoRank_witness : unitTwoRank Kc = 1 :=
  unitTwoRank_eq_one_of_imaginaryQuadratic Kc finrank_eq_two

/-- **THE CAPSTONE (single field form).**  For the explicit imaginary quadratic field
`Kc = ℚ(√-30030)`, the maximal unramified pro-`2` extension is infinite as soon as `G_∅` is
described by class field theory as having `d = rank₂ Cl(Kc)` generators and few enough relators
(`DeficiencyBoundInput`).  The numerical genus-theory certificate `rank₂ Cl(Kc) ≥ 5` is already
proved, so `Kc` has an infinite Hilbert `2`-class field tower. -/
@[deprecated "SUPERSEDED: its hypothesis is unsatisfiable -- see Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower in Vacuity.lean; use Work.ClassFieldTower.ProTwoTowerInput / ProTwoShafarevichKochInput and ProTwo.lean / ProTwoGenus.lean instead" (since := "2026-09-17")]
theorem infinite_galoisGroup_witness_of_deficiencyBoundInput
    (M : MaximalUnramifiedProP.{0} Kc 2) (h : DeficiencyBoundInput Kc M) :
    Infinite (galoisGroup M) := by
  obtain ⟨r, hbound, hpres⟩ := h
  exact infinite_galoisGroup_of_classGroupTwoRank_ge_five M
    (le_of_eq unitTwoRank_witness) hbound hpres five_le_classGroupTwoRank

/-- **THE CAPSTONE (certificate form).** -/
theorem infinite_galoisGroup_witness_of_certificate
    (M : MaximalUnramifiedProP.{0} Kc 2) {d r : ℕ}
    (h : GolodShafarevichCertificate Kc M d r) : Infinite (galoisGroup M) :=
  infinite_galoisGroup_of_certificate M h

/-- **THE TOWER CONSEQUENCE FOR THE WITNESS FIELD.**  For every `N` there is a finite unramified
Galois extension `L/Kc` with `[L : Kc] ≥ N` and constant root discriminant
`rootDiscr L = rootDiscr Kc`. -/
theorem exists_unramifiedLevel_rootDiscr_witness
    (M : MaximalUnramifiedProP.{0} Kc 2) (h : DeficiencyBoundInput Kc M) (N : ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra Kc L)
      (_ : FiniteDimensional Kc L) (_ : IsGalois Kc L),
      N ≤ Module.finrank Kc L ∧ differentIdeal (𝓞 Kc) (𝓞 L) = ⊤ ∧
        NumberField.rootDiscr L = NumberField.rootDiscr Kc :=
  exists_unramifiedLevel_of_infinite M (infinite_galoisGroup_witness_of_deficiencyBoundInput M h) N

/-- **THE WALL FOR THE WITNESS FIELD.**  The class-field-theoretic Shafarevich--Koch input for
`Kc` (against the now-proved numerical certificate) yields the chapter's wall. -/
@[deprecated "SUPERSEDED: its hypothesis is unsatisfiable -- see Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower in Vacuity.lean; use Work.ClassFieldTower.ProTwoTowerInput / ProTwoShafarevichKochInput and ProTwo.lean / ProTwoGenus.lean instead" (since := "2026-09-17")]
theorem infiniteHilbertTwoClassFieldTower_of_witnessShafarevichKochInput
    (h : ShafarevichKochInput Kc) : InfiniteHilbertTwoClassFieldTower := by
  obtain ⟨M, d, r, hcert⟩ := h
  exact ⟨Kc, inferInstance, inferInstance, M, d, r, hcert,
    infinite_galoisGroup_witness_of_certificate M hcert⟩

/-- **THE TOWER CONSEQUENCE FOR THE WITNESS FIELD, from the class-field-theoretic input.**
From `ShafarevichKochInput Kc` (`G_∅` presented with `d = rank₂ Cl(Kc)` generators and the
Shafarevich--Koch relation bound) one gets, for every `N`, a finite unramified Galois extension
`L/Kc` with `[L : Kc] ≥ N` and `rootDiscr L = rootDiscr Kc`. -/
@[deprecated "SUPERSEDED: its hypothesis is unsatisfiable -- see Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower in Vacuity.lean; use Work.ClassFieldTower.ProTwoTowerInput / ProTwoShafarevichKochInput and ProTwo.lean / ProTwoGenus.lean instead" (since := "2026-09-17")]
theorem exists_unramifiedLevel_rootDiscr_witness_of_shafarevichKochInput
    (h : ShafarevichKochInput Kc) (N : ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra Kc L)
      (_ : FiniteDimensional Kc L) (_ : IsGalois Kc L),
      N ≤ Module.finrank Kc L ∧ differentIdeal (𝓞 Kc) (𝓞 L) = ⊤ ∧
        NumberField.rootDiscr L = NumberField.rootDiscr Kc := by
  obtain ⟨M, d, r, hcert⟩ := h
  exact exists_unramifiedLevel_of_infinite M (infinite_galoisGroup_of_certificate M hcert) N

/-- **THE ASYMPTOTICALLY GOOD FAMILY, from the class-field-theoretic input for `Kc`.** -/
@[deprecated "SUPERSEDED: its hypothesis is unsatisfiable -- see Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower in Vacuity.lean; use Work.ClassFieldTower.ProTwoTowerInput / ProTwoShafarevichKochInput and ProTwo.lean / ProTwoGenus.lean instead" (since := "2026-09-17")]
theorem exists_bounded_rootDiscr_family_of_witnessShafarevichKochInput
    (h : ShafarevichKochInput Kc) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L),
      N ≤ Module.finrank ℚ L ∧ NumberField.rootDiscr L ≤ C :=
  exists_bounded_rootDiscr_family_of_infiniteHilbertTwoClassFieldTower
    (infiniteHilbertTwoClassFieldTower_of_witnessShafarevichKochInput h)

end Work.ClassFieldTower

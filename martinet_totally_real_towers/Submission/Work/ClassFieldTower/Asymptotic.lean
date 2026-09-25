import Mathlib
import Submission.Helpers
import Submission.Work.ClassFieldTower.Defs
import Submission.Work.ClassFieldTower.Objects
import Submission.Work.ClassFieldTower.Tower
import Submission.Work.ClassFieldTower.exists_unramifiedLevel_of_infinite
import Submission.Work.ClassFieldTower.Main

/-!
# `Work.ClassFieldTower.Asymptotic` -- the asymptotically good family from the wall

**WARNING.**  The hypothesis `InfiniteHilbertTwoClassFieldTower` used below is UNSATISFIABLE:
it bundles `GolodShafarevichCertificate`, i.e. an abstract finite presentation of `G_∅`, which
cannot exist once `F_∅/F` is infinite.  Machine-checked in
`Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower` (`Vacuity.lean`).  The sound
replacement is `Work.ClassFieldTower.ProTwoTowerInput` /
`exists_bounded_rootDiscr_family_of_proTwoTowerInput` (`ProTwo.lean`).

The final output form of the chapter: from `InfiniteHilbertTwoClassFieldTower` (an imaginary
quadratic field with an infinite Hilbert `2`-class field tower) one gets a family of number
fields of unbounded degree and bounded root discriminant -- exactly the "asymptotically good
family" property which, together with the CM argument of `Submission/Work/CMRealSubfield`,
yields Martinet's theorem.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ClassFieldTower

/-- **The asymptotically good family.**  An infinite Hilbert `2`-class field tower over an
imaginary quadratic field produces number fields `L` of arbitrarily large degree `[L : ℚ]` with
the SAME root discriminant (`= rootDiscr F`, bounded by an absolute constant `C`). -/
@[deprecated "SUPERSEDED: its hypothesis is unsatisfiable -- see Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower in Vacuity.lean; use Work.ClassFieldTower.ProTwoTowerInput / ProTwoShafarevichKochInput and ProTwo.lean / ProTwoGenus.lean instead" (since := "2026-09-17")]
theorem exists_bounded_rootDiscr_family_of_infiniteHilbertTwoClassFieldTower
    (h : InfiniteHilbertTwoClassFieldTower) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L),
      N ≤ Module.finrank ℚ L ∧ NumberField.rootDiscr L ≤ C := by
  classical
  obtain ⟨F, iF, iNF, M, d, r, hcert, hinf⟩ := h
  letI : Field F := iF
  letI : NumberField F := iNF
  refine ⟨NumberField.rootDiscr F,
    lt_of_lt_of_le zero_lt_one (Submission.Helpers.one_le_rootDiscr F), ?_⟩
  intro N
  obtain ⟨L, iL, iNL, iAL, hfd, hgal, hdeg, hdiff, hrd⟩ :=
    exists_unramifiedLevel_of_infinite M hinf N
  letI : Field L := iL
  letI : NumberField L := iNL
  letI : Algebra F L := iAL
  letI : FiniteDimensional F L := hfd
  have hdegQ : Module.finrank F L ≤ Module.finrank ℚ L := by
    have hmul : Module.finrank ℚ F * Module.finrank F L = Module.finrank ℚ L :=
      Module.finrank_mul_finrank ℚ F L
    have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
    nlinarith [Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)]
  exact ⟨L, iL, iNL, le_trans hdeg hdegQ, le_of_eq hrd⟩

/-- **The asymptotically good family, totally complex form.**  If some imaginary quadratic
field carries the Shafarevich--Koch data of `G_∅` (so that `G_∅` is infinite), then there are
TOTALLY COMPLEX number fields of arbitrarily large degree with the same root discriminant. -/
@[deprecated "SUPERSEDED: its hypothesis is unsatisfiable -- see Work.ClassFieldTower.not_infiniteHilbertTwoClassFieldTower in Vacuity.lean; use Work.ClassFieldTower.ProTwoTowerInput / ProTwoShafarevichKochInput and ProTwo.lean / ProTwoGenus.lean instead" (since := "2026-09-17")]
theorem exists_bounded_rootDiscr_totallyComplex_family_of_shafarevichKochInput
    (h : ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : NumberField.IsTotallyComplex F)
        (_ : Module.finrank ℚ F = 2), ShafarevichKochInput F) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ (L : Type) (_ : Field L) (_ : NumberField L)
      (_ : NumberField.IsTotallyComplex L),
      N ≤ Module.finrank ℚ L ∧ NumberField.rootDiscr L ≤ C := by
  classical
  obtain ⟨F, iF, iNF, hTC, h2, M, d, r, hcert⟩ := h
  letI : Field F := iF
  letI : NumberField F := iNF
  letI : NumberField.IsTotallyComplex F := hTC
  refine ⟨NumberField.rootDiscr F,
    lt_of_lt_of_le zero_lt_one (Submission.Helpers.one_le_rootDiscr F), ?_⟩
  intro N
  obtain ⟨L, iL, iNL, iAL, hfd, hgal, hdeg, hdiff, hrd⟩ :=
    exists_unramifiedLevel_of_infinite M (infinite_galoisGroup_of_certificate M hcert) N
  letI : Field L := iL
  letI : NumberField L := iNL
  letI : Algebra F L := iAL
  letI : FiniteDimensional F L := hfd
  haveI : NumberField.IsTotallyComplex L :=
    isTotallyComplex_of_isTotallyComplex_base (F := F) (L := L)
  have hdegQ : Module.finrank F L ≤ Module.finrank ℚ L := by
    have hmul : Module.finrank ℚ F * Module.finrank F L = Module.finrank ℚ L :=
      Module.finrank_mul_finrank ℚ F L
    have hpos : 0 < Module.finrank ℚ F := Module.finrank_pos
    nlinarith [Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpos)]
  exact ⟨L, iL, iNL, inferInstance, le_trans hdeg hdegQ, le_of_eq hrd⟩

end Work.ClassFieldTower

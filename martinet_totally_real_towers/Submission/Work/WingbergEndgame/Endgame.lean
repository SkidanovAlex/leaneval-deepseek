import Mathlib
import Submission.Work.WingbergEndgame.GolodShafarevich
import Submission.NumberField.UnramifiedPro2Assembly
import Submission.Work.CMRealSubfield.Defs
import Submission.Work.QuadraticFields.CertificateRealSummary

/-!
# `Work.WingbergEndgame.Endgame` -- the benchmark from the wall

The wall `Work.WingbergEndgame.h3DeficiencyWall` makes the wide maximal pro-`2` extension of the
totally real base `gsF` infinite (`exists_infinite_of_h3DeficiencyWall`).  This module converts
that into Martinet's theorem, using the already proved endgame
`Submission.NumberField.exists_totallyReal_discr_le_of_infinite_unramified_protwo`: every finite
dimensional Galois subextension of an everywhere-unramified pro-`2` extension of a totally real
field is a **totally real** number field with `rootDiscr` equal to `rootDiscr gsF`
(`Commons.NumberTheory.NumberField.isTotallyReal_of_isUnramifiedAtInfinitePlaces` and
`Commons.NumberTheory.NumberField.rootDiscr_eq_of_different_eq_top`), so the levels of the tower
are an asymptotically good family of totally real fields.

Nothing is assumed beyond the wall. -/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.WingbergEndgame

/-- **The benchmark from *any* wide maximal pro-`2` extension with infinite Galois group.** -/
theorem exists_totallyReal_discr_le_of_infinite (E : UnramifiedProTwoExtension gsF)
    (hinf : Infinite (galoisGroup E)) : Work.CMRealSubfield.Benchmark := by
  haveI : NumberField.IsTotallyReal gsF := Work.QuadraticFields.gsF_isTotallyReal
  exact Submission.NumberField.exists_totallyReal_discr_le_of_infinite_unramified_protwo
    (F := gsF) (K := E.K) hinf
    (fun L _ hfd hgal => E.unramified L hfd hgal)
    (fun L _ hfd hgal => E.unramifiedInf L hfd hgal)
    (fun L _ hfd hgal => E.proP L hfd hgal)

/-- **THE BENCHMARK FROM THE WALL.**  `Work.WingbergEndgame.h3DeficiencyWall` implies
`Work.CMRealSubfield.Benchmark`, i.e. the statement of `Challenge.lean`:

there is `C > 0` such that for every `N` there is a **totally real** number field `K` of degree
`≥ N` with `|disc K| ≤ C ^ [K : ℚ]`. -/
theorem exists_totallyReal_discr_le_of_h3DeficiencyWall (h : h3DeficiencyWall) :
    Work.CMRealSubfield.Benchmark := by
  obtain ⟨E, hinf⟩ := exists_infinite_of_h3DeficiencyWall h
  haveI : NumberField.IsTotallyReal gsF := Work.QuadraticFields.gsF_isTotallyReal
  exact Submission.NumberField.exists_totallyReal_discr_le_of_infinite_unramified_protwo
    (F := gsF) (K := E.K) hinf
    (fun L _ hfd hgal => E.unramified L hfd hgal)
    (fun L _ hfd hgal => E.unramifiedInf L hfd hgal)
    (fun L _ hfd hgal => E.proP L hfd hgal)

/-- The benchmark in the spelling of `Challenge.lean`, from the wall. -/
theorem exists_totallyReal_discr_le_spelled_of_h3DeficiencyWall (h : h3DeficiencyWall) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d :=
  exists_totallyReal_discr_le_of_h3DeficiencyWall h

end Work.WingbergEndgame

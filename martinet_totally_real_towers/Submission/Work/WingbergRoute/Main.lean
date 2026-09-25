import Mathlib
import Submission.Work.WingbergRoute.Verification
import Submission.Work.HilbertTowerCM.All

/-!
# `Work.WingbergRoute.Main` -- the `Kc` endgame of the unramified (Wingberg) route

This module turns the area's wall `Work.WingbergRoute.KcWingbergWall` (Shafarevich's relation-rank
bound for the maximal unramified pro-`2` extension of `Kc = ℚ(√-30030)`, equivalently Wingberg's
duality, equivalently `Work.ShafarevichKoch.KcKochCohomologyBound`) into

* the chapter's crux `Work.ShafarevichKoch.KcProTwoPresentationInput`, i.e.
  `Work.ShafarevichKoch.HasProTwoPresentation Kc 5 6`, given the group-theoretic input
  `Work.RelatorRank.GaschutzCohomologicalValue` (Gaschütz's value theorem, one input per `M`);
* the arithmetic consequences: `Work.ClassFieldTower.InfiniteProTwoExtension Kc`,
  `Submission.NumberField.UnramifiedPro2TowerWall`,
  `Submission.NumberField.BoundedRdTowerWall`, and unramified levels of every prescribed degree
  with constant root discriminant `rootDiscr Kc`;
* and the **conditional benchmark**: the extra hypothesis is a real-part (or CM-level) clause on
  the tower, which `Submission/Work/HilbertTowerCM/` proves is *not* a consequence of the
  infinitude of the tower over an imaginary quadratic base (the machine-checked obstruction of
  `Work.HilbertTowerCM.not_isCMField_of_inverting_involution` and the numerical certificate of
  `Work.HilbertTowerCM/certificate.gp`).  The totally real instance, which does reach the
  benchmark unconditionally, is `Work.WingbergRoute.TotallyReal`.

## Main declarations

* `Work.WingbergRoute.kcProTwoPresentationInput_of_kcWingbergWall`,
  `Work.WingbergRoute.hasProTwoPresentation_Kc_five_six_of_kcWingbergWall`;
* `Work.WingbergRoute.infiniteProTwoExtension_Kc_of_kcWingbergWall`,
  `Work.WingbergRoute.unramifiedPro2TowerWall_of_kcWingbergWall`,
  `Work.WingbergRoute.boundedRdTowerWall_of_kcWingbergWall`;
* `Work.WingbergRoute.benchmark_of_kcWingbergWall_of_realPart`,
  `Work.WingbergRoute.benchmark_of_kcWingbergWall_of_cmLevels`;
* the same for the `H³`-torsion and Kummer-pairing forms of the wall.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Classical
open scoped NumberField
open NumberField
open Work.ConCohomology

noncomputable section

namespace Work.WingbergRoute

/-! ## The crux and the presentation interface -/

/-- **The Shafarevich--Koch crux from the wall.**  This is the chapter's
`Work.ShafarevichKoch.KcProTwoPresentationInput` (equivalently
`Work.ShafarevichKoch.HasProTwoPresentation Kc 5 6`), obtained from the wall and Gaschütz's value
theorem. -/
theorem kcProTwoPresentationInput_of_kcWingbergWall
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcWingbergWall) : Work.ShafarevichKoch.KcProTwoPresentationInput := by
  obtain ⟨M, hM⟩ := h
  exact Work.ShafarevichKoch.kcProTwoPresentationInput_of_contH2DimLe M (hdict M)
    (contH2DimLe_six_of_shafarevichBound M hM)

/-- **`HasProTwoPresentation Kc 5 6` from the wall** -- the exact statement the caller asked for. -/
theorem hasProTwoPresentation_Kc_five_six_of_kcWingbergWall
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcWingbergWall) : Work.ShafarevichKoch.HasProTwoPresentation Kc 5 6 :=
  Work.ShafarevichKoch.hasProTwoPresentation_six_of_input
    (kcProTwoPresentationInput_of_kcWingbergWall hdict h)

/-! ## The arithmetic consequences -/

/-- **`Kc` has an infinite unramified pro-`2` tower.** -/
theorem infiniteProTwoExtension_Kc_of_kcWingbergWall
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcWingbergWall) : Work.ClassFieldTower.InfiniteProTwoExtension Kc :=
  Work.ShafarevichKoch.infiniteProTwoExtension_Kc_of_input
    (kcProTwoPresentationInput_of_kcWingbergWall hdict h)

/-- **The caller's `UnramifiedPro2TowerWall`.** -/
theorem unramifiedPro2TowerWall_of_kcWingbergWall
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcWingbergWall) : Submission.NumberField.UnramifiedPro2TowerWall :=
  Work.ShafarevichKoch.unramifiedPro2TowerWall_of_input
    (kcProTwoPresentationInput_of_kcWingbergWall hdict h)

/-- **The caller's `BoundedRdTowerWall`** -- the root-discriminant consequence of the unramified
route over `Kc`.  Note that this is *weaker* than the benchmark: the levels of the tower over the
imaginary quadratic `Kc` are not totally real (see `Work.WingbergRoute.benchmark_of_kcWingbergWall_of_realPart`). -/
theorem boundedRdTowerWall_of_kcWingbergWall
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcWingbergWall) : Submission.NumberField.BoundedRdTowerWall :=
  Work.ShafarevichKoch.boundedRdTowerWall_of_input
    (kcProTwoPresentationInput_of_kcWingbergWall hdict h)

/-- **Unramified levels of every prescribed degree with constant root discriminant `rootDiscr Kc`.** -/
theorem exists_unramifiedLevel_rootDiscr_of_kcWingbergWall
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcWingbergWall) (N : ℕ) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra Kc L)
      (_ : FiniteDimensional Kc L) (_ : IsGalois Kc L),
      N ≤ Module.finrank Kc L ∧ differentIdeal (𝓞 Kc) (𝓞 L) = ⊤ ∧
        NumberField.rootDiscr L = NumberField.rootDiscr Kc :=
  Work.ShafarevichKoch.exists_unramifiedLevel_rootDiscr_of_hasProTwoPresentation
    (hasProTwoPresentation_Kc_five_six_of_kcWingbergWall hdict h) le_rfl N

/-! ## The same consequences from the other normalisations of the wall -/

/-- Every consequence of the wall is available from the `H³`-torsion form. -/
theorem kcProTwoPresentationInput_of_kcH3Wall
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcH3Wall) : Work.ShafarevichKoch.KcProTwoPresentationInput :=
  kcProTwoPresentationInput_of_kcWingbergWall hdict (kcWingbergWall_of_kcH3Wall h)

/-- Every consequence of the wall is available from the Kummer-pairing (Koch) form. -/
theorem kcProTwoPresentationInput_of_kcKochInjectionWall
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcKochInjectionWall) : Work.ShafarevichKoch.KcProTwoPresentationInput :=
  Work.ShafarevichKoch.kcProTwoPresentationInput_of_kochInjection hdict
    ⟨h.choose, h.choose_spec⟩

/-- The `H³`-torsion form gives `BoundedRdTowerWall`. -/
theorem boundedRdTowerWall_of_kcH3Wall
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcH3Wall) : Submission.NumberField.BoundedRdTowerWall :=
  boundedRdTowerWall_of_kcWingbergWall hdict (kcWingbergWall_of_kcH3Wall h)

/-- The Kummer-pairing (Koch) form gives `BoundedRdTowerWall`. -/
theorem boundedRdTowerWall_of_kcKochInjectionWall
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcKochInjectionWall) : Submission.NumberField.BoundedRdTowerWall :=
  boundedRdTowerWall_of_kcWingbergWall hdict (kcWingbergWall_of_kochInjectionWall h)

/-! ## The conditional benchmark

The real-part / CM-level clause is the *only* missing input, and
`Submission/Work/HilbertTowerCM/` proves that it is not a consequence of the infinitude of the
tower over the imaginary quadratic base `Kc`.  Over a totally real base it is *free*: see
`Work.WingbergRoute.TotallyReal`. -/

/-- **The benchmark from the wall and the real-part clause.** -/
theorem benchmark_of_kcWingbergWall_of_realPart
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcWingbergWall) (hreal : Work.HilbertTowerCM.RealPartWall Kc) :
    Work.CMRealSubfield.Benchmark :=
  Work.HilbertTowerCM.benchmark_of_infiniteProTwoExtension_Kc_of_realPart
    (infiniteProTwoExtension_Kc_of_kcWingbergWall hdict h) hreal

/-- **The benchmark from the wall and the CM-level clause.** -/
theorem benchmark_of_kcWingbergWall_of_cmLevels
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcWingbergWall) (hcm : Work.HilbertTowerCM.CMLevelWall Kc) :
    Work.CMRealSubfield.Benchmark :=
  Work.HilbertTowerCM.benchmark_of_infiniteProTwoExtension_Kc_of_cmLevels
    (infiniteProTwoExtension_Kc_of_kcWingbergWall hdict h) hcm

/-- **The benchmark from the wall and the half-real clause.** -/
theorem benchmark_of_kcWingbergWall_of_halfReal
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcWingbergWall) (hhalf : Work.HilbertTowerCM.HalfRealLevelWall Kc) :
    Work.CMRealSubfield.Benchmark :=
  Work.HilbertTowerCM.benchmark_of_infiniteProTwoExtension_Kc_of_halfReal
    (infiniteProTwoExtension_Kc_of_kcWingbergWall hdict h) hhalf

/-- `CMWall` from the wall and the CM-level clause. -/
theorem cmWall_of_kcWingbergWall_of_cmLevels
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcWingbergWall) (hcm : Work.HilbertTowerCM.CMLevelWall Kc) :
    Work.CMRealSubfield.CMWall :=
  Work.HilbertTowerCM.cmWall_of_infiniteProTwoExtension_Kc_of_cmLevels
    (infiniteProTwoExtension_Kc_of_kcWingbergWall hdict h) hcm

/-! ## The seam-free group-theoretic route

`Work.RelatorRank.GaschutzCohomologicalValue` states the Gaschütz value theorem in the **abstract**
normal closure (see `Submission/Work/ShafarevichKoch/README.md` §22, where that normalisation is
recorded as stronger than the classical theorem and as rejected by a prover), whereas the sibling
area `Submission/Work/AbstractDictionary` isolates the classical statement
`GaschutzPresentationExists` in the abstract normalisation *for one suitable family*, with no seam.
The following wrappers use that safer input. -/

/-- **The crux from the wall and the seam-free group-theoretic input.** -/
theorem kcProTwoPresentationInput_of_kcWingbergWall_seamFree
    (hpres : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.GaschutzPresentationExists (Work.ClassFieldTower.galoisGroup M))
    (h : KcWingbergWall) : Work.ShafarevichKoch.KcProTwoPresentationInput :=
  Work.ShafarevichKoch.kcProTwoPresentationInput_of_gaschutzPresentationExists hpres
    ⟨h.choose, contH2DimLe_six_of_shafarevichBound h.choose h.choose_spec⟩

/-- **`HasProTwoPresentation Kc 5 6` from the wall and the seam-free input.** -/
theorem hasProTwoPresentation_Kc_five_six_of_kcWingbergWall_seamFree
    (hpres : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.GaschutzPresentationExists (Work.ClassFieldTower.galoisGroup M))
    (h : KcWingbergWall) : Work.ShafarevichKoch.HasProTwoPresentation Kc 5 6 :=
  Work.ShafarevichKoch.hasProTwoPresentation_six_of_input
    (kcProTwoPresentationInput_of_kcWingbergWall_seamFree hpres h)

/-- **The caller's `BoundedRdTowerWall` from the wall and the seam-free input.** -/
theorem boundedRdTowerWall_of_kcWingbergWall_seamFree
    (hpres : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.GaschutzPresentationExists (Work.ClassFieldTower.galoisGroup M))
    (h : KcWingbergWall) : Submission.NumberField.BoundedRdTowerWall :=
  Work.ShafarevichKoch.boundedRdTowerWall_of_gaschutzPresentationExists hpres
    ⟨h.choose, contH2DimLe_six_of_shafarevichBound h.choose h.choose_spec⟩

/-- **The benchmark from the wall, the seam-free input and the real-part clause.** -/
theorem benchmark_of_kcWingbergWall_seamFree_of_realPart
    (hpres : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.AbstractDictionary.GaschutzPresentationExists (Work.ClassFieldTower.galoisGroup M))
    (h : KcWingbergWall) (hreal : Work.HilbertTowerCM.RealPartWall Kc) :
    Work.CMRealSubfield.Benchmark :=
  Work.HilbertTowerCM.benchmark_of_infiniteProTwoExtension_Kc_of_realPart
    (Work.ShafarevichKoch.infiniteProTwoExtension_Kc_of_input
      (kcProTwoPresentationInput_of_kcWingbergWall_seamFree hpres h)) hreal

/-! ## The benchmark in the exact spelling of the target

`Work.CMRealSubfield.Benchmark` is definitionally the statement of
`Submission.exists_totallyReal_discr_le`; the following two theorems state the area's endgame in
that spelling, so that a caller does not have to unfold anything. -/

/-- **The benchmark (in the target's own spelling) from the wall, the group-theoretic input and
the real-part clause over `Kc`.** -/
theorem exists_totallyReal_discr_le_of_kcWingbergWall_of_realPart
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcWingbergWall) (hreal : Work.HilbertTowerCM.RealPartWall Kc) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d :=
  benchmark_of_kcWingbergWall_of_realPart hdict h hreal

/-- The same, with the CM-level clause. -/
theorem exists_totallyReal_discr_le_of_kcWingbergWall_of_cmLevels
    (hdict : ∀ M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Kc 2,
      Work.RelatorRank.GaschutzCohomologicalValue (Work.ClassFieldTower.galoisGroup M))
    (h : KcWingbergWall) (hcm : Work.HilbertTowerCM.CMLevelWall Kc) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d :=
  benchmark_of_kcWingbergWall_of_cmLevels hdict h hcm

end Work.WingbergRoute

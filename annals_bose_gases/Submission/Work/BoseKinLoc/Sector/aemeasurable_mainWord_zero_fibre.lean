import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Kinetic.fibre_lift_general
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The anchored (`u = 0`) fibre of FS's kinetic word `mainWord` is a.e. strongly measurable

`Work.BoseKinLoc.Kinetic.mainWord_fibre_aemeasurable` proves that the *joint* map

    `(u,q₂) ↦ mainWord ℓ d s εT u (z ↦ Ψ(kcInsN n i (z,q₂)))`

is a.e. strongly measurable for the product measure `volume × volume`.  The present lemma is the
`u = 0` **section** of that statement, with the measure on the *section* variable `r = q₂` alone
(`Work.BoseKinLoc.Kinetic.genFibre i Ψ r` is definitionally `z ↦ Ψ(kcInsN n i (z,r))`).

The point is that the corpus's proof gives the *strong* measurability of the momentum integral
`fibBC ℓ i F Ψ` (as a function of `(u,q₂)`), and strong measurability — unlike a.e. strong
measurability — is stable under composition with an arbitrary **measurable** map.  Composing with
the measurable section `r ↦ (0,r)` therefore gives strong measurability of the anchored fibre, no
null-set bookkeeping about the product measure required (a section of an a.e.-strongly-measurable
function at a fixed point is *not* in general a.e. strongly measurable, so this route genuinely
needs the strong form proved upstream).
-/

namespace Work.BoseKinLoc.Sector

open MeasureTheory

set_option linter.unusedVariables false

theorem aemeasurable_mainWord_zero_fibre {ℓ d s εT L : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L)
    {n : ℕ} {Ψ : Submission.BoseGases.X (n + 1) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ Submission.BoseGases.abox (n + 1) L) (i : Fin (n + 1)) :
    MeasureTheory.AEStronglyMeasurable
      (fun r : Submission.BoseGases.X n =>
        Work.BoseKinLoc.mainWord ℓ d s εT 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r))
      MeasureTheory.volume := by
  -- the measurable section `r ↦ (0, r)` of `ℝ³ × X n`
  have hsec : Measurable (fun r : Submission.BoseGases.X n =>
      ((0 : EuclideanSpace ℝ (Fin 3)), r)) :=
    measurable_const.prodMk measurable_id
  -- each `bsOneBody ℓ F 0` of the anchored fibre is strongly measurable in `r`
  have key : ∀ (F : ℝ → ℝ), Measurable F → StronglyMeasurable
      (fun r : Submission.BoseGases.X n =>
        Work.BSKinetic.bsOneBody ℓ F 0 (Work.BoseKinLoc.Kinetic.genFibre i Ψ r)) := by
    intro F hF
    have h := ((Work.BoseKinLoc.Kinetic.fibBC_stronglyMeasurable hΨ i ℓ hF).const_mul
      ((2 * Real.pi) ^ 3)⁻¹).comp_measurable hsec
    have h' : StronglyMeasurable (fun r : Submission.BoseGases.X n =>
        ((2 * Real.pi) ^ 3)⁻¹ *
          Work.BoseKinLoc.Kinetic.fibBC ℓ i F Ψ ((0 : EuclideanSpace ℝ (Fin 3)), r)) := h
    simpa [Work.BSKinetic.bsOneBody, Submission.BoseGases.kinFT,
      Work.BSKinetic.bsWin, Work.BSKinetic.bsQ, Work.BSKinetic.bsMean,
      Work.BoseKinLoc.Kinetic.fibBC, Work.BoseKinLoc.Kinetic.fibP,
      Work.BoseKinLoc.Kinetic.fibK, Work.BoseKinLoc.Kinetic.fibZ,
      Work.BoseKinLoc.Kinetic.fibMean, Work.BoseKinLoc.Kinetic.genFibre] using h'
  have h1 := (key (Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹))
    (Work.BoseKinLoc.Kinetic.measurable_fsKinCoeff _)).const_mul (1 - εT)
  have h2 := (key (Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹))
    (Work.BoseKinLoc.Kinetic.measurable_fsKinCoeff _)).const_mul εT
  simp only [Work.BoseKinLoc.mainWord]
  exact (h1.add h2).aestronglyMeasurable

end Work.BoseKinLoc.Sector

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.frame_lattice_ball
import Submission.Work.BoseBoxFock.qCoeff_eq_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory

/-! ### The bridge state `g = χ_Λ·(ψ − m)`

`FINDING_kinRow_lattice.md` §1 and `FINDING_kinRow_lattice_S2.md` §1: both sides of the kinematic
row are expressed through the single one-body state

`g = χ_Λ·(ψ − m)`,  `m = ℓ⁻³ ∫_{acube ℓ} ψ`,

via `qCoeff_eq_kinFT` (proved) and `mainWord_eq_winState` below.  These are the entry points of
the `Lab N`-sum assembly. -/

/-- The windowed, mean-free one-body state `g = χ_Λ·(ψ − m)` of `qCoeff_eq_kinFT`. -/
noncomputable def winState (ℓ : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    EuclideanSpace ℝ (Fin 3) → ℂ :=
  fun z => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) *
    (((ψ z - (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.acube ℓ, ψ x) : ℝ) : ℂ)

/-- `bsWin ℓ 0` is the corpus window `χ_Λ` (definitional, up to `x − ℓ·0 = x`). -/
lemma bsWin_zero_eq_chiLam (ℓ : ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    Work.BSKinetic.bsWin ℓ 0 z = Work.BoseK15.corpusBox.chiLam ℓ z := by
  simp [Work.BSKinetic.bsWin, Submission.BoseGases.chiScale, Work.BoseB4.BoxData.chiLam,
    Work.BoseK15.corpusBox]

/-- `bsQ ℓ 0 ψ = ψ − ℓ⁻³∫_{acube ℓ}ψ` (definitional, up to `ℓ·0 + z = z`). -/
lemma bsQ_zero (ℓ : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) (z : EuclideanSpace ℝ (Fin 3)) :
    Work.BSKinetic.bsQ ℓ 0 ψ z
      = ψ z - (ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.acube ℓ, ψ x := by
  simp [Work.BSKinetic.bsQ, Work.BSKinetic.bsMean]

/-- The windowed mean-free state of `bsOneBody` is `winState ℓ ψ`. -/
lemma winState_eq (ℓ : ℝ) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ) :
    (fun z => (Work.BSKinetic.bsWin ℓ 0 z : ℂ) * (Work.BSKinetic.bsQ ℓ 0 ψ z : ℂ))
      = winState ℓ ψ := by
  funext z
  simp [bsWin_zero_eq_chiLam, bsQ_zero, winState]

/-- **The left-hand side's coefficients are `kinFT (winState ℓ ψ)` at the lattice momenta**
(`qCoeff_eq_ft` + `qCoeff_eq_kinFT`, both proved). -/
theorem qCoeff_eq_winState {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hψsupp : tsupport ψ ⊆ Work.BoseK15.corpusBox.boxL ℓ) (n : Fin 3 → ℤ) :
    qCoeff ℓ (kmomInt ℓ n) ψ = Submission.BoseGases.kinFT (winState ℓ ψ) (kmomInt ℓ n) := by
  rw [qCoeff_eq_kinFT hℓ hψ hψsupp n, winState_eq]

/-- **The right-hand side is the two continuum integrals of `winState`**: `mainWord` unfolds to
`(1−eT)·(2π)⁻³∫F_{c₁}(‖p‖)‖kinFT g p‖² + eT·(2π)⁻³∫F_{c₂}(‖p‖)‖kinFT g p‖²`. -/
theorem mainWord_eq_winState {ℓ d s eT : ℝ} {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} :
    Work.BoseKinLoc.mainWord ℓ d s eT 0 ψ
      = (1 - eT) * (((2 * Real.pi) ^ 3)⁻¹ *
            ∫ p, Submission.BoseGases.fsKinCoeff ((2 * (s * ℓ))⁻¹) ‖p‖
              * ‖Submission.BoseGases.kinFT (winState ℓ ψ) p‖ ^ 2)
        + eT * (((2 * Real.pi) ^ 3)⁻¹ *
            ∫ p, Submission.BoseGases.fsKinCoeff ((2 * (d * s * ℓ))⁻¹) ‖p‖
              * ‖Submission.BoseGases.kinFT (winState ℓ ψ) p‖ ^ 2) := by
  rw [Work.BoseKinLoc.mainWord, Work.BSKinetic.bsOneBody, Work.BSKinetic.bsOneBody,
    winState_eq]

end Work.BoseBoxFock

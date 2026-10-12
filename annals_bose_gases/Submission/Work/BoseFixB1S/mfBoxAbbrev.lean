import ChallengeDeps
import Submission.Work.BoseFixB1S.mfRows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-- FS's `A₀` (`a0MainLocBox`) at FS's parameters. -/
abbrev mfA0 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  a0MainLocBox (mfV v μ u) μ (mfM1 h μ u) (mfS v μ n Φ u)

/-- FS's `ĝω(0)` (`g0w0Mass`). -/
abbrev mfC1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) : ℝ :=
  g0w0Mass (v := v) h

/-- The cut-off mass `∫χ_B² = chiMass M ℓ d u`. -/
abbrev mfChi (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u

/-- FS's spectral cut-off `(dsℓ)⁻¹ = sbCut μ (a v)`. -/
abbrev mfCut (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℝ :=
  sbCut μ (_root_.BoseGases.a v)

/-- The gap coefficient `½ε_T(1+π⁻²)⁻¹(ℓd)⁻²` of `𝒯_B`. -/
abbrev mfGapC (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℝ :=
  Work.SmallBoxTBWord.tbGapCoeff (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT

/-- The **spectral half** of `sbKin` (`𝒯_{B(u)}` without its gap term): the box-projected
`Q_Bχ_B[√−Δ−(dsℓ)⁻¹]₊²χ_BQ_B`. -/
abbrev mfSpec (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.UBBInputs8.tBwordKinInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (boxA v μ u) (mfV v μ u) (Submission.BoseGases.chiB
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (mfCut v μ) Φ

end

end Work.BoseFixB1S

import ChallengeDeps
import Submission.Work.BoseFixB1.boxMassGates
import Submission.Work.BoseFixB1.bqPotsplit
import Submission.Work.BoseFixB1S.boxC1_add_cnPlus
import Submission.Work.BoseFixB1S.boxM1Info
import Submission.Work.BoseFixB1S.boxQ0_ge_counts
import Submission.Work.BoseFixB1S.meanFieldAbbrev
import Submission.Work.BoseFixB1S.oneBodyB1.sqrtW.boxMassProdB1
import Submission.Work.BoseFixB1S.sectorPassageB1Pair
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

/-! ## The box at FS's parameters -/

/-- The sliding box `B(u) = dlBox ℓ d u` at FS's parameters. -/
abbrev boxA (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : Set (EuclideanSpace ℝ (Fin 3)) :=
  dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u

/-- FS's localised one-body kernel `w_{1,B(u)}` at FS's parameters. -/
abbrev boxW1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
  wSmall1Pair h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u

/-- The localised pair kernel `w_{B(u)}(g₂)` of the `A₂`-comparison at FS's parameters. -/
abbrev boxW2 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
  wSmallPair (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u (g2 v h)

/-- The localised pair kernel `w_{B(u)}(v)` at FS's parameters. -/
abbrev boxW {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
  wSmallPair (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u v

/-- The localised flat count `S = Σ_i∫(P_{B(u),i}Φ)²`. -/
abbrev mfS (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  boxFlatCount (mfV v μ u) (sideAt μ (a v)) (boxA v μ u) Φ

/-- The localised one-body mass `M₁ = ∬w_{1,B(u)}` (the `boxM1` of the box words). -/
abbrev mfM1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  boxM1 (sideAt μ (a v)) (boxA v μ u) (boxW1 h μ u)

/-- The localised pair mass `M₂ = ∬w_{B(u)}(g₂)` over `B(u) × B(u)`. -/
abbrev mfM2 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  boxM2 (mfV v μ u) (boxA v μ u) (boxW2 h μ u)

/-- The condensate word `boxQ₀` at FS's parameters. -/
abbrev mfQ0 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  boxQ0 (mfV v μ u) (sideAt μ (a v)) μ (boxA v μ u) (boxW1 h μ u) (boxW2 h μ u) Φ

/-- The five-word sum `boxQSum` at FS's parameters (the potsplit RHS of `qLHSwordB`). -/
abbrev mfQSum {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  boxQSum (mfV v μ u) (sideAt μ (a v)) μ (boxA v μ u) (boxW h μ u) (boxW1 h μ u)
    (boxW2 h μ u) (omC (Classical.choose h)) Φ

/-- FS's `μ`-free error coefficient of the flat branch: the `C` making the pure-real
inequality close, `C = 5K/2` with `K` the constant of `boxM1Info`. -/
abbrev mfC (K : ℝ) : ℝ := 5 * K / 2

/-! ## Definitional unfoldings, for the piece lemmas -/

theorem mfS_def (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    mfS v μ n Φ u
      = boxFlatCount (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) (sideAt μ (a v))
          (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u) Φ := rfl

theorem mfV_def (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) :
    mfV v μ u = boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u := rfl

theorem mfQ_def (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    mfQ v μ n Φ u
      = Work.UBBInputs8.cnPlusBoxInd (sideAt μ (a v))
          (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
          (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) Φ := rfl

end

end Work.BoseFixB1S

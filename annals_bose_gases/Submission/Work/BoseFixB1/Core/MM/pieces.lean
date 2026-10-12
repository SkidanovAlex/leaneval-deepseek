import ChallengeDeps
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.BoseFixB1.Core.MM.linearCombination
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Core.MM.pieces` — the assembly of the mean-mismatch step

Copied (namespace changed from `Work.BoseFixB1S` to `Work.BoseFixB1.Core.MM`, and with the
correction to the payment constant described below) from the *proved* assembly
`Work.BoseFixB1.Core.MM.cruxCorrB1_of_pieces` of `Submission/Work/BoseFixB1S/cruxCorrB1.lean`.  The
copied file carries a `sorry` only in its *final* theorem (which discharges the six interface
propositions), so the assembly theorem itself is `sorry`-free and can be transported here.

## The two edits relative to the original

* the payment constant is `b/(8ℓ²)` here (the mean-mismatch step of
  `Work.BoseFixB1.Core.meanMismatch_le`), where the original used `b/(4ℓ²)`, and the `(2π)⁻³`
  normalisation of the original's two `u`-integrals is **absent** — the target of
  `meanMismatch_le` is the unnormalised `bsW` word on both sides;
* the `Arith` proposition therefore carries the sharper comparison
  `A₁ + B₁ ≤ bValue/(8ℓ²)` (the two terms separately are `≤ bValue/(16ℓ²)`,
  `Work.BoseFixB1.Core.MM.mmArith`).

## The six interface propositions

`CutWords` (the window's two cut words are `≤ Cℓ⁻²`, uniformly in `u`), `MeanSq` (the `u`-integral
of the squared sliding box mean), `Marginal` (the `u`-marginal integrability of the two `bsW`
forms and the window partition), `ChiL2` (the `χ_ℓ`-weighted `L²` bound), `PlanchMarg` (the
`u`-marginal Plancherel identity) and `Arith` (the parameter arithmetic).  They are discharged in
`Submission/Work/BoseFixB1/Core/meanMismatch_le.lean`.
-/

noncomputable section
open MeasureTheory
open scoped Real Topology BigOperators ContDiff ENNReal

namespace Work.BoseFixB1.Core.MM

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Submission.BoseGases

/-! ## 4.  The three delegated pieces, as predicates -/

/-- The conclusion of `Work.BoseFixB1.Core.MM.corrCutWordsSharp` at `v`. -/
def CutWords (v : E3 → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ u : E3,
      MeasureTheory.Integrable (fun p : E3 =>
          (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ‖p‖) ^ 2 *
            ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 =>
              Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z) p‖ ^ 2)
      ∧ (Work.BSKinetic.Decomp.bsW
            (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
            (fun z : E3 =>
              Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z)
          ≤ C * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2)
      ∧ ((∫ p : E3,
              (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ‖p‖) ^ 2 *
                ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 =>
                  Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z) p‖ ^ 2)
          ≤ C * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2)

/-- The conclusion of `Work.BoseFixB1.Core.MM.corrMeanSq` at `v`. -/
def MeanSq (v : E3 → ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ w : E3 → ℝ, ContDiff ℝ (⊤ : ENat) w →
        MeasureTheory.Integrable (fun u : E3 =>
            ((1 / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
              ∫ z in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z) ^ 2)
        ∧ ((∫ u : E3,
              ((1 / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
                ∫ z in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z) ^ 2)
            ≤ C * (1 + ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)⁻¹
                    + |Real.log ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)|) ^ 3
                * (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹
                * (∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                    (w z) ^ 2))

/-- The conclusion of `Work.BoseFixB1.Core.MM.corrMarginal` at `v`. -/
def Marginal (v : E3 → ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    ∀ w : E3 → ℝ, ContDiff ℝ (⊤ : ENat) w →
      MeasureTheory.Integrable (fun u : E3 =>
          Work.BSKinetic.Decomp.bsW
            (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
            (fun z : E3 =>
              Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z * w z))
      ∧ MeasureTheory.Integrable (fun u : E3 =>
          Work.BSKinetic.Decomp.bsW
            (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
            (fun z : E3 =>
              Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z *
              (w z - (1 / Work.SmallBoxSliding.boxMass
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
                (∫ z' in Submission.BoseGases.dlBox
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z'))))
      ∧ MeasureTheory.Integrable (fun u : E3 =>
          ∫ z : E3,
            (Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z) ^ 2 * (w z) ^ 2)
      ∧ (∫ u : E3, ∫ z : E3,
            (Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z) ^ 2 * (w z) ^ 2)
        = (∫ z : E3,
            (Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) z) ^ 2 * (w z) ^ 2)

/-! ## 6.  The three further helper lemmas, as predicates, and the assembly -/

/-- `√(aQ)·√(bQ) = √(ab)·Q` for nonnegative `a, b, Q`. -/
lemma sqrt_mul_sqrt_mul {a b Q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hQ : 0 ≤ Q) :
    Real.sqrt (a * Q) * Real.sqrt (b * Q) = Real.sqrt (a * b) * Q := by
  have hsq : Real.sqrt Q * Real.sqrt Q = Q := by
    nlinarith [Real.sq_sqrt hQ]
  calc Real.sqrt (a * Q) * Real.sqrt (b * Q)
      = (Real.sqrt a * Real.sqrt b) * (Real.sqrt Q * Real.sqrt Q) := by
        rw [Real.sqrt_mul ha Q, Real.sqrt_mul hb Q]; ring
    _ = (Real.sqrt a * Real.sqrt b) * Q := by rw [hsq]
    _ = Real.sqrt (a * b) * Q := by rw [Real.sqrt_mul ha b]

/-- The conclusion of `Work.BoseFixB1.Core.MM.corrChiScaleL2`. -/
def ChiL2 : Prop :=
  ∀ ℓ : ℝ, 0 < ℓ → ∀ w : E3 → ℝ, Continuous w →
    (∫ z : E3, (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2)
      ≤ (Submission.BoseGases.chiNormSq)⁻¹ *
        (∫ z in Submission.BoseGases.acube ℓ, (w z) ^ 2)

/-- The conclusion of `Work.BoseFixB1.Core.MM.corrPlanchMarg`. -/
def PlanchMarg : Prop :=
  ∀ ℓ d : ℝ, 0 < ℓ → 0 < d → ∀ w : E3 → ℝ, ContDiff ℝ (⊤ : ENat) w →
    MeasureTheory.Integrable (fun u : E3 =>
      ∫ z : E3, (Submission.BoseGases.chiB ℓ d u z) ^ 2 * (w z) ^ 2) →
    (∫ u : E3, ∫ z : E3, (Submission.BoseGases.chiB ℓ d u z) ^ 2 * (w z) ^ 2)
      = ∫ z : E3, (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2 →
    MeasureTheory.Integrable (fun u : E3 =>
        ∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 =>
          Submission.BoseGases.chiB ℓ d u z * w z) p‖ ^ 2)
      ∧ (∫ u : E3, ∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi (fun z : E3 =>
            Submission.BoseGases.chiB ℓ d u z * w z) p‖ ^ 2)
        = (2 * Real.pi) ^ 3 *
            (∫ z : E3, (Submission.BoseGases.chiScale ℓ z) ^ 2 * (w z) ^ 2)

/-- The conclusion of `Work.BoseFixB1.Core.MM.corrArith`. -/
def Arith (v : E3 → ℝ) : Prop :=
  0 < _root_.BoseGases.a v →
  ∀ C₀ C₁ Cχ : ℝ, 0 ≤ C₀ → 0 ≤ C₁ → 0 ≤ Cχ →
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ →
      (let ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
       let d : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
       let L : ℝ := 1 + (ℓ * d)⁻¹ + |Real.log d|
       (C₀ * (ℓ⁻¹) ^ 2 * (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹)
          ≤ Work.BoseBox.bValue / (16 * ℓ ^ 2))
        ∧ (2 * Real.sqrt (C₀ * (ℓ⁻¹) ^ 2) *
            Real.sqrt (C₁ * L ^ 3 * ((ℓ * d) ^ 3)⁻¹ * (2 * Real.pi) ^ 3 * Cχ)
          ≤ Work.BoseBox.bValue / (16 * ℓ ^ 2)))

/-! ### 6.1  The abbreviations of the correction step -/

/-- The `u`-windowed mean-free state `χ_{B(u)}·(w − c)` at FS's parameters. -/
def corrSt (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) : E3 → E3 → ℝ :=
  fun u z => Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z * (w z - c)

/-- The sliding-box mean `|B(u)|⁻¹∫_{B(u)}w` at FS's parameters. -/
def corrBC (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (u : E3) : ℝ :=
  (1 / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
    ∫ z' in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z'

/-- The flat mean `ℓ⁻³∫_{acube ℓ}w` at FS's parameters. -/
def corrMean (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) : ℝ :=
  (1 / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) *
    ∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), w z

/-- The flat mean-square `Q` of the correction step. -/
def corrQ (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) : ℝ :=
  ∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
    (w z - corrMean v μ w) ^ 2

/-- The sliding-mean form on the left of the correction inequality. -/
def corrA (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) : E3 → ℝ :=
  fun u => Work.BSKinetic.Decomp.bsW
    (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
    (corrSt v μ w (corrBC v μ w u) u)

/-- The flat-mean form on the right of the correction inequality. -/
def corrB (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) : E3 → ℝ :=
  fun u => Work.BSKinetic.Decomp.bsW
    (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
    (corrSt v μ w c u)

/-- The squared sliding mean of `w − c`. -/
def corrBm (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) : E3 → ℝ :=
  fun u => (corrBC v μ (fun z => w z - c) u) ^ 2

/-- The `L²`-norm of the `p`-transform of the mean-free state. -/
def corrH (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) : E3 → ℝ :=
  fun u => Real.sqrt (∫ p : E3,
    ‖Work.BSKinetic.Decomp.bsPsi (corrSt v μ w c u) p‖ ^ 2)

/-- The cross term of the mean-shift expansion. -/
def corrX (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) : E3 → ℝ :=
  fun u => |corrBC v μ (fun z => w z - c) u| * corrH v μ w c u

/-- The logarithmic factor `L = 1 + (ℓd)⁻¹ + |log d|` of `MeanSq`, at FS's parameters. -/
def corrL (v : E3 → ℝ) (μ : ℝ) : ℝ :=
  1 + ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)⁻¹
    + |Real.log ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)|

/-! ### 6.2  The unfolding equations of the abbreviations -/

lemma corrSt_eq (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) (u : E3) :
    corrSt v μ w c u = fun z => Submission.BoseGases.chiB
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z * (w z - c) := rfl

lemma corrBC_eq (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (u : E3) :
    corrBC v μ w u = (1 / Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
      ∫ z' in Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, w z' := rfl

lemma corrBm_eq (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) (u : E3) :
    corrBm v μ w c u = (corrBC v μ (fun z => w z - c) u) ^ 2 := rfl

lemma corrH_eq (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) (u : E3) :
    corrH v μ w c u = Real.sqrt (∫ p : E3,
      ‖Work.BSKinetic.Decomp.bsPsi (corrSt v μ w c u) p‖ ^ 2) := rfl

lemma corrX_eq (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) (u : E3) :
    corrX v μ w c u = |corrBC v μ (fun z => w z - c) u| * corrH v μ w c u := rfl

lemma corrA_eq (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (u : E3) :
    corrA v μ w u = Work.BSKinetic.Decomp.bsW
      (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
      (corrSt v μ w (corrBC v μ w u) u) := rfl

lemma corrB_eq (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) (c : ℝ) (u : E3) :
    corrB v μ w c u = Work.BSKinetic.Decomp.bsW
      (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
      (corrSt v μ w c u) := rfl

lemma corrQ_eq (v : E3 → ℝ) (μ : ℝ) (w : E3 → ℝ) :
    corrQ v μ w = ∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (w z - corrMean v μ w) ^ 2 := rfl


/-! ### 6.2  The assembly -/

/-- **The assembly**: the six pieces imply the target.  From `crux_pt` one derives
`∫_u (A_u − B_u) ≤ Kq∫_u bm² + 2√Kq ∫_u |bm|·H` by `integral_mono`,
then the `u`-Cauchy–Schwarz, Plancherel + the window partition and the arithmetic. -/
theorem mm_of_pieces {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hCut : CutWords v) (hMean : MeanSq v) (hMarg : Marginal v)
    (hArith : Arith v) (hChi : ChiL2) (hPlanch : PlanchMarg) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ g : E3 → ℝ, ContDiff ℝ (⊤ : ENat) g →
      (∫ u : E3, Work.BSKinetic.Decomp.bsW
            (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
            (fun z : E3 =>
              Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z *
              (g z - (1 / Work.SmallBoxSliding.boxMass
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) *
                ∫ z' in Submission.BoseGases.dlBox
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u, g z')))
        ≤ (∫ u : E3, Work.BSKinetic.Decomp.bsW
              (Submission.BoseGases.fsKinCoeff (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)))
              (fun z : E3 =>
                Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u z *
                (g z - (1 / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) *
                  ∫ z' in Submission.BoseGases.acube
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), g z')))
          + (Work.BoseBox.bValue / (8 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2)) *
              (∫ z in Submission.BoseGases.acube
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (g z - (1 / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3) *
                  ∫ z' in Submission.BoseGases.acube
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), g z') ^ 2) := by
  obtain ⟨C₀, hC₀nn, ε_c, hεc, hcut⟩ := hCut
  obtain ⟨ε_m, hεm, C₁, hC₁nn, hmean⟩ := hMean
  obtain ⟨ε_g, hεg, hmarg⟩ := hMarg
  by_cases hav : 0 < _root_.BoseGases.a v
  · obtain ⟨ε_a, hεa, harith⟩ := hArith hav C₀ C₁ (Submission.BoseGases.chiNormSq)⁻¹
      hC₀nn hC₁nn
      (inv_nonneg.mpr (le_of_lt Submission.BoseGases.chiNormSq_pos))
    refine ⟨min (min ε_c (min ε_m ε_g)) ε_a,
      lt_min (lt_min hεc (lt_min hεm hεg)) hεa, ?_⟩
    intro μ hμ g hg
    have hεcm : min (min ε_c (min ε_m ε_g)) ε_a ≤ ε_c :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    have hεmm : min (min ε_c (min ε_m ε_g)) ε_a ≤ ε_m :=
      le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hεgm : min (min ε_c (min ε_m ε_g)) ε_a ≤ ε_g :=
      le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have hεam : min (min ε_c (min ε_m ε_g)) ε_a ≤ ε_a := min_le_right _ _
    have hμc : Work.BoseBoxFix.Adm v ε_c μ := Work.BoseFixB1.Adm.mono hμ hεcm
    have hμm : Work.BoseBoxFix.Adm v ε_m μ := Work.BoseFixB1.Adm.mono hμ hεmm
    have hμg : Work.BoseBoxFix.Adm v ε_g μ := Work.BoseFixB1.Adm.mono hμ hεgm
    have hμ0 : 0 < μ := Work.BoseFixB1.adm_mu_pos hμ
    have hℓp : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hμ
    have hdp : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hμ
    have hμd : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε_a :=
      le_trans (Work.BoseFixB1.adm_dilute hμ) hεam
    have hLnn : 0 ≤ corrL v μ := by
      rw [corrL]
      have h1 : 0 < ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)⁻¹ :=
        inv_pos.mpr (mul_pos hℓp hdp)
      have h2 : 0 ≤ |Real.log ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)| :=
        abs_nonneg _
      linarith
    have hCχnn : 0 ≤ (Submission.BoseGases.chiNormSq)⁻¹ :=
      inv_nonneg.mpr (le_of_lt Submission.BoseGases.chiNormSq_pos)
    have hQnn : 0 ≤ corrQ v μ g := integral_nonneg fun z => sq_nonneg _
    have hsubd : ContDiff ℝ (⊤ : ENat) (fun z : E3 => g z - corrMean v μ g) :=
      hg.sub contDiff_const
    have hsubc : Continuous (fun z : E3 => g z - corrMean v μ g) := hsubd.continuous
    have hAint : MeasureTheory.Integrable (corrA v μ g) := (hmarg μ hμg g hg).2.1
    have hBint : MeasureTheory.Integrable (corrB v μ g (corrMean v μ g)) :=
      (hmarg μ hμg (fun z : E3 => g z - corrMean v μ g) hsubd).1
    obtain ⟨hBmint, hBmbound⟩ := hmean μ hμm (fun z : E3 => g z - corrMean v μ g) hsubd
    have hPlan := hPlanch (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d hℓp hdp
      (fun z : E3 => g z - corrMean v μ g) hsubd
      (hmarg μ hμg (fun z : E3 => g z - corrMean v μ g) hsubd).2.2.1
      (hmarg μ hμg (fun z : E3 => g z - corrMean v μ g) hsubd).2.2.2
    have hH2int : MeasureTheory.Integrable
        (fun u : E3 => (corrH v μ g (corrMean v μ g) u) ^ 2) := by
      refine hPlan.1.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [corrH_eq]
      exact (Real.sq_sqrt (integral_nonneg fun p => sq_nonneg _)).symm
    have hH2val : ∫ u : E3, (corrH v μ g (corrMean v μ g) u) ^ 2
        = (2 * Real.pi) ^ 3 *
          (∫ z : E3, (Submission.BoseGases.chiScale
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) z) ^ 2
            * (g z - corrMean v μ g) ^ 2) := by
      calc ∫ u : E3, (corrH v μ g (corrMean v μ g) u) ^ 2
          = ∫ u : E3, ∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
              (corrSt v μ g (corrMean v μ g) u) p‖ ^ 2 := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
            simp only [corrH_eq]
            exact Real.sq_sqrt (integral_nonneg fun p => sq_nonneg _)
        _ = (2 * Real.pi) ^ 3 *
            (∫ z : E3, (Submission.BoseGases.chiScale
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) z) ^ 2
              * (g z - corrMean v μ g) ^ 2) := hPlan.2
    have hH2bound : ∫ u : E3, (corrH v μ g (corrMean v μ g) u) ^ 2
        ≤ (2 * Real.pi) ^ 3 * (Submission.BoseGases.chiNormSq)⁻¹ * corrQ v μ g := by
      rw [hH2val]
      have hchi := hChi (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) hℓp
        (fun z : E3 => g z - corrMean v μ g) hsubc
      calc (2 * Real.pi) ^ 3 *
            (∫ z : E3, (Submission.BoseGases.chiScale
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) z) ^ 2
              * (g z - corrMean v μ g) ^ 2)
          ≤ (2 * Real.pi) ^ 3 * ((Submission.BoseGases.chiNormSq)⁻¹ *
              (∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
                (g z - corrMean v μ g) ^ 2)) :=
            mul_le_mul_of_nonneg_left hchi (by positivity)
        _ = (2 * Real.pi) ^ 3 * (Submission.BoseGases.chiNormSq)⁻¹ * corrQ v μ g := by
            simp only [corrQ_eq]
            ring
    have hAbsBm : AEStronglyMeasurable
        (fun u : E3 => |corrBC v μ (fun z : E3 => g z - corrMean v μ g) u|) := by
      have h1 : AEStronglyMeasurable
          (fun u : E3 => Real.sqrt (corrBm v μ g (corrMean v μ g) u)) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable hBmint.aestronglyMeasurable
      refine h1.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [corrBm_eq]
      exact Real.sqrt_sq_eq_abs _
    have hHaes : AEStronglyMeasurable (corrH v μ g (corrMean v μ g)) := by
      have h1 : AEStronglyMeasurable
          (fun u : E3 => Real.sqrt (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
            (corrSt v μ g (corrMean v μ g) u) p‖ ^ 2)) :=
        Real.continuous_sqrt.comp_aestronglyMeasurable hPlan.1.aestronglyMeasurable
      exact h1
    have hBm_memLp : MeasureTheory.MemLp
        (fun u : E3 => |corrBC v μ (fun z : E3 => g z - corrMean v μ g) u|) 2 := by
      refine (MeasureTheory.memLp_two_iff_integrable_sq hAbsBm).mpr ?_
      refine hBmint.congr (Filter.Eventually.of_forall fun u => ?_)
      simp only [corrBm_eq]
      exact (sq_abs _).symm
    have hH_memLp : MeasureTheory.MemLp (corrH v μ g (corrMean v μ g)) 2 :=
      (MeasureTheory.memLp_two_iff_integrable_sq hHaes).mpr hH2int
    have hXcs : ∫ u : E3, corrX v μ g (corrMean v μ g) u
        ≤ Real.sqrt (C₁ * (corrL v μ) ^ 3
              * (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹ * corrQ v μ g)
          * Real.sqrt ((2 * Real.pi) ^ 3 * (Submission.BoseGases.chiNormSq)⁻¹ * corrQ v μ g) := by
      have hcs := Work.BSKinetic.Decomp.abs_integral_mul_le_sqrt_mul_sqrt hBm_memLp hH_memLp
      have h1 : ∫ u : E3, corrX v μ g (corrMean v μ g) u
          ≤ Real.sqrt (∫ u : E3, (|corrBC v μ (fun z : E3 => g z - corrMean v μ g) u|) ^ 2)
            * Real.sqrt (∫ u : E3, (corrH v μ g (corrMean v μ g) u) ^ 2) :=
        le_trans (le_abs_self _) hcs
      refine le_trans h1 (mul_le_mul ?_ (Real.sqrt_le_sqrt hH2bound)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      refine Real.sqrt_le_sqrt (le_trans ?_ hBmbound)
      exact le_of_eq (integral_congr_ae (Filter.Eventually.of_forall fun u => by
        simp only [corrBm_eq]
        exact sq_abs _))
    have hpt : ∀ u : E3, corrA v μ g u
        ≤ corrB v μ g (corrMean v μ g) u
          + (C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2)
              * corrBm v μ g (corrMean v μ g) u
          + 2 * Real.sqrt (C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2)
              * corrX v μ g (corrMean v μ g) u := by
      intro u
      obtain ⟨hInt_u, hQ_u, hE_u⟩ := hcut μ hμc u
      have hKqnn : 0 ≤ C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2 :=
        mul_nonneg hC₀nn (sq_nonneg _)
      have hcrux := crux_pt (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
        (κ := Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
        hℓp hdp hg u hKqnn hQ_u hE_u hInt_u (corrMean v μ g)
      have hring : 2 * (|corrBC v μ (fun z : E3 => g z - corrMean v μ g) u| *
            Real.sqrt (C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2) *
            Real.sqrt (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
              (corrSt v μ g (corrMean v μ g) u) p‖ ^ 2))
          = 2 * Real.sqrt (C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2) *
            (|corrBC v μ (fun z : E3 => g z - corrMean v μ g) u| *
              Real.sqrt (∫ p : E3, ‖Work.BSKinetic.Decomp.bsPsi
                (corrSt v μ g (corrMean v μ g) u) p‖ ^ 2)) := by ring
      simp only [corrA_eq, corrB_eq, corrBm_eq, corrX_eq, corrH_eq, corrSt_eq, corrBC_eq]
        at hcrux hring ⊢
      linarith only [hcrux, hring]
    have hXint : MeasureTheory.Integrable (corrX v μ g (corrMean v μ g)) := by
      have hdom : MeasureTheory.Integrable (fun u : E3 =>
          (corrBm v μ g (corrMean v μ g) u + (corrH v μ g (corrMean v μ g) u) ^ 2) / 2) :=
        (hBmint.add hH2int).div_const 2
      refine hdom.mono' (hAbsBm.mul hHaes) ?_
      refine Filter.Eventually.of_forall fun u => ?_
      simp only [Real.norm_eq_abs, corrX_eq]
      have hb : 0 ≤ |corrBC v μ (fun z : E3 => g z - corrMean v μ g) u| := abs_nonneg _
      have hh : 0 ≤ corrH v μ g (corrMean v μ g) u := Real.sqrt_nonneg _
      simp only [abs_of_nonneg (mul_nonneg hb hh), corrBm_eq]
      nlinarith [sq_nonneg (|corrBC v μ (fun z : E3 => g z - corrMean v μ g) u|
          - corrH v μ g (corrMean v μ g) u),
        sq_abs (corrBC v μ (fun z : E3 => g z - corrMean v μ g) u)]
    have hXint' : MeasureTheory.Integrable
        (fun u : E3 => 2 * Real.sqrt (C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2)
          * corrX v μ g (corrMean v μ g) u) :=
      hXint.const_mul _
    have hBmint' : MeasureTheory.Integrable
        (fun u : E3 => (C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2)
          * corrBm v μ g (corrMean v μ g) u) :=
      hBmint.const_mul _
    have hsumint : MeasureTheory.Integrable
        (fun u : E3 => (corrB v μ g (corrMean v μ g) u
            + (C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2)
                * corrBm v μ g (corrMean v μ g) u)
          + 2 * Real.sqrt (C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2)
              * corrX v μ g (corrMean v μ g) u) :=
      (hBint.add hBmint').add hXint'
    let Kq : ℝ := C₀ * ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 2
    let sB : ℝ := (((Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹
    let A₁ : ℝ := Kq * (C₁ * (corrL v μ) ^ 3 * sB)
    let B₁ : ℝ := 2 * Real.sqrt Kq
      * Real.sqrt (C₁ * (corrL v μ) ^ 3 * sB * (2 * Real.pi) ^ 3
          * (Submission.BoseGases.chiNormSq)⁻¹)
    have hA₁ : A₁ = Kq * (C₁ * (corrL v μ) ^ 3 * sB) := rfl
    have hB₁ : B₁ = 2 * Real.sqrt Kq
        * Real.sqrt (C₁ * (corrL v μ) ^ 3 * sB * (2 * Real.pi) ^ 3
            * (Submission.BoseGases.chiNormSq)⁻¹) := rfl
    have hKqnn : 0 ≤ Kq := mul_nonneg hC₀nn (sq_nonneg _)
    have hsBnn : 0 ≤ sB := inv_nonneg.mpr (pow_nonneg (mul_pos hℓp hdp).le 3)
    have hcanon : A₁ + B₁
        ≤ Work.BoseBox.bValue / (8 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2) := by
      obtain ⟨hcan1, hcan2⟩ := harith μ hμ0 hμd
      have h1 : A₁ ≤ Work.BoseBox.bValue
          / (16 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2) := hcan1
      have h2 : B₁ ≤ Work.BoseBox.bValue
          / (16 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2) := hcan2
      have hkey : Work.BoseBox.bValue
            / (16 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2)
          + Work.BoseBox.bValue
            / (16 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2)
          = Work.BoseBox.bValue
            / (8 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2) := by
        by_cases hx : Work.BoseBox.sideAt μ (_root_.BoseGases.a v) = 0
        · rw [hx]; norm_num
        · field_simp
          ring
      linarith only [h1, h2, hkey]
    have hchain : ∫ u : E3, corrA v μ g u
        ≤ (∫ u : E3, corrB v μ g (corrMean v μ g) u)
          + (Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u)
              + 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u)) := by
      have hI1 : ∫ u : E3, ((fun u : E3 => corrB v μ g (corrMean v μ g) u)
            + (fun u : E3 => Kq * corrBm v μ g (corrMean v μ g) u)) u
          = (∫ u : E3, corrB v μ g (corrMean v μ g) u)
            + (∫ u : E3, (fun u : E3 => Kq * corrBm v μ g (corrMean v μ g) u) u) :=
        MeasureTheory.integral_add hBint hBmint'
      have hI2 : (∫ u : E3, (fun u : E3 => Kq * corrBm v μ g (corrMean v μ g) u) u)
          = Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u) :=
        MeasureTheory.integral_const_mul _ _
      have hI3 : ∫ u : E3, (((fun u : E3 => corrB v μ g (corrMean v μ g) u)
            + (fun u : E3 => Kq * corrBm v μ g (corrMean v μ g) u))
            + (fun u : E3 => 2 * Real.sqrt Kq * corrX v μ g (corrMean v μ g) u)) u
          = (∫ u : E3, ((fun u : E3 => corrB v μ g (corrMean v μ g) u)
                + (fun u : E3 => Kq * corrBm v μ g (corrMean v μ g) u)) u)
            + (∫ u : E3, (fun u : E3 => 2 * Real.sqrt Kq
                * corrX v μ g (corrMean v μ g) u) u) :=
        MeasureTheory.integral_add (hBint.add hBmint') hXint'
      have hI4 : (∫ u : E3, (fun u : E3 => 2 * Real.sqrt Kq
              * corrX v μ g (corrMean v μ g) u) u)
          = 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u) :=
        MeasureTheory.integral_const_mul _ _
      have hmono := MeasureTheory.integral_mono hAint hsumint hpt
      calc ∫ u : E3, corrA v μ g u
          ≤ ∫ u : E3, (((fun u : E3 => corrB v μ g (corrMean v μ g) u)
                + (fun u : E3 => Kq * corrBm v μ g (corrMean v μ g) u))
              + (fun u : E3 => 2 * Real.sqrt Kq * corrX v μ g (corrMean v μ g) u)) u := hmono
        _ = (∫ u : E3, corrB v μ g (corrMean v μ g) u)
              + (Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u)
                + 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u)) := by
            rw [hI3, hI1, hI2, hI4]; ring_nf
    have hA1 : Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u) ≤ A₁ * corrQ v μ g := by
      calc Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u)
          ≤ Kq * (C₁ * (corrL v μ) ^ 3 * sB * corrQ v μ g) :=
            mul_le_mul_of_nonneg_left hBmbound hKqnn
        _ = A₁ * corrQ v μ g := by rw [hA₁]; ring
    have hA2 : 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u)
        ≤ B₁ * corrQ v μ g := by
      have hsq := sqrt_mul_sqrt_mul (a := C₁ * (corrL v μ) ^ 3 * sB)
        (b := (2 * Real.pi) ^ 3 * (Submission.BoseGases.chiNormSq)⁻¹) (Q := corrQ v μ g)
        (mul_nonneg (mul_nonneg hC₁nn (pow_nonneg hLnn 3)) hsBnn)
        (mul_nonneg (by positivity) hCχnn) hQnn
      calc 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u)
          ≤ 2 * Real.sqrt Kq * (Real.sqrt (C₁ * (corrL v μ) ^ 3 * sB * corrQ v μ g)
              * Real.sqrt ((2 * Real.pi) ^ 3 * (Submission.BoseGases.chiNormSq)⁻¹
                  * corrQ v μ g)) :=
            mul_le_mul_of_nonneg_left hXcs (by positivity)
        _ = B₁ * corrQ v μ g := by rw [hsq, hB₁]; ring
    have hcorr : Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u)
          + 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u)
        ≤ (A₁ + B₁) * corrQ v μ g := by
      calc _ ≤ A₁ * corrQ v μ g + B₁ * corrQ v μ g := add_le_add hA1 hA2
        _ = (A₁ + B₁) * corrQ v μ g := by rw [hA₁, hB₁]; ring
    have hfinal : (∫ u : E3, corrA v μ g u)
        ≤ (∫ u : E3, corrB v μ g (corrMean v μ g) u)
          + (Work.BoseBox.bValue / (8 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2))
              * corrQ v μ g := by
      have hY : (Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u)
              + 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u))
          ≤ (Work.BoseBox.bValue / (8 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2))
              * corrQ v μ g := by
        calc (Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u)
                + 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u))
            ≤ (A₁ + B₁) * corrQ v μ g := hcorr
          _ ≤ (Work.BoseBox.bValue / (8 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2))
                * corrQ v μ g := mul_le_mul_of_nonneg_right hcanon hQnn
      calc (∫ u : E3, corrA v μ g u)
          ≤ (∫ u : E3, corrB v μ g (corrMean v μ g) u)
              + (Kq * (∫ u : E3, corrBm v μ g (corrMean v μ g) u)
                + 2 * Real.sqrt Kq * (∫ u : E3, corrX v μ g (corrMean v μ g) u)) := hchain
        _ ≤ (∫ u : E3, corrB v μ g (corrMean v μ g) u)
              + (Work.BoseBox.bValue / (8 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2))
                  * corrQ v μ g := add_le_add (le_refl _) hY
    exact hfinal
  · exact ⟨1, one_pos, fun μ hμ g hg => absurd (Work.BoseFixB1.adm_a_pos hμ) hav⟩


end Work.BoseFixB1.Core.MM

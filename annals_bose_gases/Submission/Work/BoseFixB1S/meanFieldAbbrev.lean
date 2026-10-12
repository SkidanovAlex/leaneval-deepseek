import ChallengeDeps
import Submission.Work.BoseFixB1.AprioriPieces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.meanFieldAbbrev` — the abbreviations of the two sides of
# `Work.BoseFixB1S.perBoxMeanFieldB1`

FS `thm:smallbox` at the sliding box `B(u)` (`Papers/fournais_solovej/final_v2.tex`
l.3907–4065) in the sharp mean-field form at the FS density `n/|B(u)|` (`|B(u)|` the
*indicator* box mass `Work.SmallBoxSliding.boxMass`) and the coefficient `1/2` of
`Work.SmallBoxSliding.psiWeight`.

These `abbrev`s are the two sides of that inequality, kept in a module of their own so that
every piece of its proof (the gap branch, the flat branch, the count collapse) can state
its claim without importing the residual of `perBoxMeanFieldB1.lean`.
-/

namespace Work.BoseFixB1S

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## 0. Abbreviations for the two sides of the target inequality -/

/-- The box volume appearing in the target's density: the *indicator* mass `|B(u)|`. -/
abbrev mfV (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u

/-- FS's per-box mass `∬w_{1,B(u)}`. -/
abbrev mfW {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u

/-- The state norm `‖Φ‖² = ∫_{abox n ℓ} Φ²`. -/
abbrev mfI (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Φ x) ^ 2

/-- The box-excited count `n₊(B(u)) = Σᵢ‖Q_{B(u),i}Φ‖²`. -/
abbrev mfQ (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) Φ

/-- The target's error bracket `μ²(a v)(R²μ^{2/3} + K_B³(μ(a v)³)^{1/2})·χ_{B(u)}
+ μ(a v)`. -/
abbrev mfBracket (v : EuclideanSpace ℝ (Fin 3) → ℝ) (R μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  μ ^ 2 * (_root_.BoseGases.a v)
      * (R ^ 2 * μ ^ (2 / 3 : ℝ) + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
      * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
    + μ * (_root_.BoseGases.a v)

/-- The left-hand side of the target inequality. -/
abbrev mfLhs {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (R C μ : ℝ)
    (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (1 / 2) * (Work.SmallBoxSliding.psiWeight 1 μ ((n : ℝ) / mfV v μ u))
      * mfW h μ u * mfI v μ n Φ
    - (1 / 2) * μ ^ 2 * mfW h μ u * mfI v μ n Φ
    - C * mfBracket v R μ u * mfI v μ n Φ

/-- The right-hand side of the target inequality. -/
abbrev mfRhs {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ : ℝ)
    (n : ℕ) (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u Φ
    + Work.SmallBoxSliding.qLHSwordB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ u Φ

/-- The box-support hypothesis of the target. -/
abbrev mfSupp (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∀ᵐ x ∂(MeasureTheory.volume.restrict
      (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
    Φ x ≠ 0 → ∀ i : Fin n, x i ∈ Submission.BoseGases.dlBox
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u

/-- The interior hypothesis of the target. -/
abbrev mfInt (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) : Prop :=
  u ∈ Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ


end

end Work.BoseFixB1S

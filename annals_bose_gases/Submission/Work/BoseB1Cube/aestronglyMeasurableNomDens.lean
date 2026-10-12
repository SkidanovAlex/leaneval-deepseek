import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseB1Cube.aestronglyMeasurable_nomBoxInner
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `aestronglyMeasurableNomDens` — measurability of the nominal density `t(u)` in the sliding
parameter

The companion of `aestronglyMeasurable_nomBoxInner`: the nominal (indicator-count) density

    nomDens h μ Φ u = (∫_{abox} Φ² · n(u)) / (‖Φ‖² · |B(u)|) ,
    n(u) = Σᵢ 1_{B(u)}(xᵢ) ,

is a.e. strongly measurable as a function of `u` for an arbitrary smooth box state `Φ`.  As for
`nomBoxInner`, no positivity, smallness or support hypothesis is used: the numerator is a
parametric integral of the jointly measurable integrand `(u,x) ↦ Φ x² · n(u) x`
(`AEStronglyMeasurable.integral_prod_right'`), the denominator is the constant `‖Φ‖²` times the
measurable function `u ↦ |B(u)|` (`measurable_boxMass_cube`), and `AEStronglyMeasurable.div₀`
closes the argument (`ℝ` is a `GroupWithZero` with continuous multiplication and inversion, so
division in `ℝ` needs no nonvanishing hypothesis).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Joint measurability of the nominal-count integrand** `(u,x) ↦ Φ x² · n(u) x`. -/
lemma measurable_nomDens_integrand (ℓ d : ℝ) {n : ℕ} (Ψ : X n → ℝ) (hΨ : Continuous Ψ) :
    Measurable fun p : E3 × X n =>
      Ψ p.2 ^ 2 * Work.BoseB1Cube.nomCnt ℓ d p.1 p.2 := by
  have hΨm : Measurable fun p : E3 × X n => Ψ p.2 ^ 2 :=
    ((hΨ.measurable).comp measurable_snd).pow_const 2
  exact hΨm.mul (measurable_nomCnt_joint ℓ d n)

/-- **The per-box nominal density is a.e. strongly measurable in the sliding parameter `u`.**

This is the measurability that lets FS's `eq:appsliding` be integrated over `u` at the *sharp*
(indicator-count) density `t(u) = n(u)/|B(u)|`.  The statement carries no hypothesis at all
beyond `Φ` being a smooth box state. -/
theorem aestronglyMeasurableNomDens {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :
    MeasureTheory.AEStronglyMeasurable
      (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.BoseB1Cube.nomDens h μ (Φ : Submission.BoseGases.X n → ℝ) u)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
  -- the two geometric parameters of the sliding box, abbreviated
  have hboxMass : Measurable (fun u : E3 =>
      Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :=
    measurable_boxMass_cube _ _
  -- joint measurability of the count integrand `(u,x) ↦ Φ x² · n(u) x`
  have hint : Measurable (fun p : E3 × X n => (Φ : X n → ℝ) p.2 ^ 2 *
      Work.BoseB1Cube.nomCnt (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d p.1 p.2) :=
    measurable_nomDens_integrand _ _ _ Φ.contDiff.continuous
  have hAESM : MeasureTheory.AEStronglyMeasurable (fun p : E3 × X n => (Φ : X n → ℝ) p.2 ^ 2 *
      Work.BoseB1Cube.nomCnt (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d p.1 p.2)
      ((volume : Measure E3).prod
        ((volume : Measure (X n)).restrict
          (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))) :=
    (hint.aemeasurable).aestronglyMeasurable
  -- the numerator: a parametric integral over the box of a jointly measurable integrand
  have hnum : MeasureTheory.AEStronglyMeasurable (fun u : E3 =>
      ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        (Φ : X n → ℝ) x ^ 2 *
          Work.BoseB1Cube.nomCnt (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x)
      (volume : Measure E3) :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := (volume : Measure E3))
      (ν := (volume : Measure (X n)).restrict
              (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))
      hAESM
  -- the denominator: a constant (`‖Φ‖²`) times the measurable box volume
  have hden : MeasureTheory.AEStronglyMeasurable (fun u : E3 =>
      Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) *
        Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      (volume : Measure E3) :=
    ((measurable_const.mul hboxMass).aemeasurable).aestronglyMeasurable
  unfold Work.BoseB1Cube.nomDens
  exact hnum.div₀ hden

end Work.BoseB1Cube

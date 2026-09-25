import ChallengeDeps
import Submission.Helpers
import Submission.Work.BourgainPlan.Assembly.bourgain_of_parts
import Submission.Work.BourgainPlan.Maximal.maximal_statement
import Submission.Work.BourgainPlan.Oscillation.oscillation_statement

open LeanEval.Dynamics.BourgainErgodic
open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

namespace Submission

theorem bourgain_polynomial_ergodic [IsProbabilityMeasure μ] {p : ℝ≥0∞} (hp : 1 < p) (hp_ne_top : p ≠ ∞)
    {T : X → X} (hT : MeasurePreserving T μ μ)
    {a : ℕ → ℕ} (ha : IsIntegerPolynomialSequence a)
    {f : X → ℝ} (hf : MemLp f p μ) :
    ∃ F : X → ℝ,
      ∀ᵐ x ∂μ,
        Tendsto (fun n : ℕ => polynomialErgodicAverage a T f (n + 1) x) atTop (𝓝 (F x)) :=
  Work.BourgainPlan.Assembly.bourgain_of_parts Work.BourgainPlan.Maximal.maximal_statement
    Work.BourgainPlan.Oscillation.oscillation_statement hp hp_ne_top hT ha hf

end Submission

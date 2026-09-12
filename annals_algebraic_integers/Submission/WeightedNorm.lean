import Submission.PotentialDefs
import Submission.Serre
import Submission.SerreExample
import Submission.PotentialContinuity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Algebra.Polynomial

/-!
# Weighted n-norm for the converse machinery

First infrastructure block under Smith's Theorem squarefree (the first named
pass toward `smith_converse_interval`).  Following Smith's Definition defn:norm:

* the weight of a measure μ at real x:  `w_μ(x) = exp(U^μ(x))`, where
  `U^μ = logPotential μ` is the (classical-sign) logarithmic potential;
* the n-norm of an integer polynomial on the interval `[a,b]`:
  `‖P‖ = sup_{x ∈ [a,b]} w_μ(x)^n · |P(x)|`.

Basic analytic facts (contracts for this module; each is a classical lemma for
Hölder measures, specialized here to our `μ` = convex combination of the
equilibrium measure and its inversion image — the support interval
`[aSerre,bSerre]` is fixed by the application):
  (W1) finiteness: `logPotential μ x` is finite for all real x
       (integrable log singularities);
  (W2) continuity: `x ↦ logPotential μ (x:ℂ)` is continuous on ℝ
       (Hölder-type estimate on the log kernel);
  (W3) consequently the weight is finite and positive on `[a,b]`, and the map
       `x ↦ w_μ(x)^n·|P(x)|` is continuous on the compact `[a,b]`, so its sup
       is attained (a genuine max) and the n-norm is finite.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Submission.WeightedNorm

open Submission.PotentialDefs
open Submission.Serre
open Submission.SerreExample

/-- The weight `w_μ(x) = exp(U^μ(x))` of a measure at a real point. -/
noncomputable def weight (μ : Measure ℝ) (x : ℝ) : ℝ :=
  Real.exp (logPotential μ (x : ℂ))

/-- The n-norm of a polynomial with respect to `(μ, [a,b])`:
`sup_{x ∈ [a,b]} w_μ(x)^n · |P(x)|`. -/
noncomputable def weightedNorm (a b : ℝ) (μ : Measure ℝ) (n : ℕ) (P : Polynomial ℤ) : ℝ :=
  sSup ((fun x : ℝ => (weight μ x) ^ n * |Polynomial.aeval x P|) '' Set.Icc a b)

/-- The weight is strictly positive (exponential). -/
lemma weight_pos (μ : Measure ℝ) (x : ℝ) : 0 < weight μ x :=
  Real.exp_pos _

/-- (W3a) The weight function is continuous on `[a,b]` (composition of the
continuous potential with exp; the potential's continuity is W2, proved in
`Submission/PotentialContinuity.lean`). -/
lemma weight_continuous_on_Icc :
    ContinuousOn (fun x : ℝ => weight (serreMeasure gSerre aSerre bSerre) x) (Set.Icc aSerre bSerre) := by
  have hcont : Continuous (fun x : ℝ => Real.exp
      (logPotential (serreMeasure gSerre aSerre bSerre) (x : ℂ))) :=
    Real.continuous_exp.comp Submission.PotentialContinuity.logPotential_continuous_real
  exact hcont.continuousOn

/-- (W3b) The map whose sup defines the n-norm is continuous on the compact
interval, hence the sup is attained and the n-norm finite: stated as
boundedness of the map (sup of a bounded nonempty set exists by completeness). -/
lemma weightedSup_bounded (n : ℕ) (P : Polynomial ℤ) :
    BddAbove ((fun x : ℝ => (weight (serreMeasure gSerre aSerre bSerre) x) ^ n *
      |Polynomial.aeval x P|) '' Set.Icc aSerre bSerre) := by
  have hcontOn : ContinuousOn
      (fun x : ℝ => (weight (serreMeasure gSerre aSerre bSerre) x) ^ n *
        |Polynomial.aeval x P|) (Set.Icc aSerre bSerre) := by
    refine (weight_continuous_on_Icc.pow n).mul ?_
    exact (Polynomial.continuous_aeval P).continuousOn.abs
  have hcomp : IsCompact
      ((fun x : ℝ => (weight (serreMeasure gSerre aSerre bSerre) x) ^ n *
        |Polynomial.aeval x P|) '' Set.Icc aSerre bSerre) :=
    CompactIccSpace.isCompact_Icc.image_of_continuousOn hcontOn
  exact hcomp.bddAbove


/-- (W4) The weight is bounded above on the compact interval (continuous on
compact ⇒ bounded), so weighted norms compare with plain sup-norms:
`‖P‖_k ≤ M^k · ‖P‖_{sup}` for `M = max w_μ`. -/
lemma weight_bdd_on_Icc :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
        weight (serreMeasure gSerre aSerre bSerre) x ≤ M := by
  let f : ℝ → ℝ := fun x => weight (serreMeasure gSerre aSerre bSerre) x
  have hcomp : IsCompact (f '' Set.Icc aSerre bSerre) :=
    CompactIccSpace.isCompact_Icc.image_of_continuousOn weight_continuous_on_Icc
  rcases hcomp.bddAbove with ⟨M, hM⟩
  refine ⟨M, ?nonneg, ?bdd⟩
  · -- 0 ≤ M: f(aSerre) > 0 lies in the image, bounded by M
    have hmem : f aSerre ∈ f '' Set.Icc aSerre bSerre := by
      exact ⟨aSerre, ⟨le_rfl, a_le_b⟩, rfl⟩
    exact le_trans (weight_pos (serreMeasure gSerre aSerre bSerre) aSerre).le (hM hmem)
  · intro x hx
    exact hM ⟨x, hx, rfl⟩

end Submission.WeightedNorm

import Mathlib
import Submission.BVMain
import Submission.BVLevel
import Submission.LevelOfDistribution
import Submission.Commons.NumberTheory.BombieriVinogradov.siegel_walfisz_primEventual
import Submission.Commons.NumberTheory.BombieriVinogradov.bmvt_tail_bound
import Submission.Commons.NumberTheory.BombieriVinogradov.cleanBV_of_parts
import Submission.Commons.NumberTheory.BombieriVinogradov.sum_charSup_le_log_mul_primitive
import Submission.Commons.NumberTheory.BombieriVinogradov.basic_mean_value_theorem

open scoped BigOperators Topology
open Finset Filter
open Classical
open Submission.BV

/-!
# Bombieri--Vinogradov: the final assembly

This module glues the three shared-commons pieces of the Bombieri--Vinogradov
argument to the workspace-level statements:

* `Commons...BombieriVinogradov.siegel_walfisz_primEventual` — the small-moduli
  (Siegel--Walfisz) range;
* `Commons...BombieriVinogradov.bmvt_tail_bound` — the large-moduli range, from
  the Basic Mean Value Theorem (Vaughan's Theorem 1.2) by summation by parts;
* `Commons...BombieriVinogradov.cleanBV_of_parts` — the assembly.

The Basic Mean Value Theorem enters as the workspace-level hypothesis
`BMVTHypothesis` of `Submission/BVMain.lean`, which is exactly the statement of
`basic_mean_value_theorem`.  The conclusion
`Commons.NumberTheory.MaynardSieve.cleanBV_of_bmvt` yields
`Submission.BV.CleanBV`, i.e. the classical form of Bombieri--Vinogradov used by
`Submission/BVLevel.lean` to deduce the level of distribution for the shifted
`θ`-window.
-/

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

set_option maxHeartbeats 2000000

/-- `BMVTHypothesis` in the explicit form consumed by `bmvt_tail_bound`. -/
theorem bmvtHypothesis_expanded (h : BMVTHypothesis) :
    ∃ C : ℝ, 0 < C ∧ ∀ x q : ℕ, 2 ≤ x → 1 ≤ q →
      (∑ q' ∈ Finset.Icc 1 q, ((q' : ℝ) / (q'.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q' => χ.IsPrimitive)),
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q')‖)
                '' Set.Icc 1 x))
      ≤ C * ((x : ℝ) + (x : ℝ) ^ (5 / 6 : ℝ) * (q : ℝ)
          + (x : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ 2)
          * (Real.log ((x : ℝ) * (q : ℝ) + 2)) ^ 5 := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun x q hx hq => ?_⟩
  have h1 := hb x q hx hq
  simpa only [bmvtSum, bmvtTerm, chiSupIcc] using h1

/-- The statement of `basic_mean_value_theorem` (Vaughan's Theorem 1.2) in the
explicit `Icc`-sup form; it is exactly `BMVTHypothesis` after unfolding
`bmvtSum`, `bmvtTerm` and `chiSupIcc`. -/
theorem BMVTHypothesis_of_basic
    (h : ∃ C : ℝ, 0 < C ∧ ∀ x q : ℕ, 2 ≤ x → 1 ≤ q →
      (∑ q' ∈ Finset.Icc 1 q, ((q' : ℝ) / (q'.totient : ℝ)) *
        ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q' => χ.IsPrimitive)),
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.Icc 1 y,
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q')‖)
                '' Set.Icc 1 x))
      ≤ C * ((x : ℝ) + (x : ℝ) ^ (5 / 6 : ℝ) * (q : ℝ)
          + (x : ℝ) ^ (1 / 2 : ℝ) * (q : ℝ) ^ 2)
          * (Real.log ((x : ℝ) * (q : ℝ) + 2)) ^ 5) : BMVTHypothesis := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, hC, fun x q hx hq => ?_⟩
  have h1 := hb x q hx hq
  simpa only [bmvtSum, bmvtTerm, chiSupIcc] using h1

/-- **Bombieri--Vinogradov** from the Basic Mean Value Theorem. -/
theorem cleanBV_of_bmvt (h : BMVTHypothesis) : CleanBV := by
  have hBMVT := bmvtHypothesis_expanded h
  have hSW : ∀ A : ℝ, 0 < A → ∀ᶠ X : ℕ in Filter.atTop, ∀ R : ℕ,
      (R : ℝ) ≤ (Real.log (X : ℝ)) ^ (2 * A + 40) →
      (∑ q ∈ Finset.Icc 1 R, ((q.totient : ℕ) : ℝ)⁻¹ *
        ∑ χ ∈ (Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)),
          sSup ((fun y : ℕ => ‖∑ n ∈ Finset.range (y + 1),
              ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ ((n : ℕ) : ZMod q)
                - (if χ = 1 then (y : ℂ) else 0)‖) '' Set.Icc 1 X))
      ≤ (X : ℝ) * (Real.log (X : ℝ)) ^ (-(3 * A + 42)) := by
    intro A hA
    filter_upwards [Commons.NumberTheory.BombieriVinogradov.siegel_walfisz_primEventual
      A (2 * A + 40) hA (by linarith)] with X hX
    intro R hR
    have h1 := hX R hR
    rwa [show A + (2 * A + 40) + 2 = 3 * A + 42 by ring] at h1
  have hTail := Commons.NumberTheory.BombieriVinogradov.bmvt_tail_bound hBMVT
  have hCB := Commons.NumberTheory.BombieriVinogradov.cleanBV_of_parts hSW hTail
  simpa only [CleanBV, charSup, psiChar, deltaChar] using hCB

/-- **The level of distribution for the shifted `θ`-window**, deduced from the
Basic Mean Value Theorem through Bombieri--Vinogradov (`Submission/BVLevel.lean`). -/
theorem levelOfDistribution_of_bmvt (h : BMVTHypothesis) {ϑ : ℝ} (hϑ : ϑ < 1 / 2) :
    levelOfDistribution ϑ :=
  levelOfDistribution_of_cleanBV (cleanBV_of_bmvt h) hϑ

/-- **Bombieri--Vinogradov**, unconditionally: the Basic Mean Value Theorem
(Vaughan's Theorem 1.2, proved in the shared commons) is converted into
`BMVTHypothesis` by `BMVTHypothesis_of_basic` and fed to `cleanBV_of_bmvt`. -/
theorem cleanBV : CleanBV :=
  cleanBV_of_bmvt (BMVTHypothesis_of_basic
    Commons.NumberTheory.BombieriVinogradov.basic_mean_value_theorem)

/-- **The level of distribution `ϑ < 1/2` for the shifted `θ`-window**,
unconditionally (this is Bombieri--Vinogradov, now a theorem of this workspace). -/
theorem levelOfDistribution_of_BMVT {ϑ : ℝ} (hϑ : ϑ < 1 / 2) : levelOfDistribution ϑ :=
  levelOfDistribution_of_bmvt (BMVTHypothesis_of_basic
    Commons.NumberTheory.BombieriVinogradov.basic_mean_value_theorem) hϑ

end

end Commons.NumberTheory.MaynardSieve

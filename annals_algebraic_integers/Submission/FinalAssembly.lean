import Submission.Notions
import Submission.Serre
import Submission.SerreExample
import Submission.SerreMean
import Submission.SupportConcentration
import Submission.Assembly
import Submission.Reduction
import Submission.Helpers
import Submission.ArithmeticAssembly
import ChallengeDeps

/-!
# Final assembly: `theorem_1_1` conditional on the converse output

Proves the challenge theorem from the single remaining deep input: the output
of `Submission.Converse.smith_converse_interval` instantiated with Serre's
measure.  Hypothesis `hconv` is exactly that output: a sequence of monic
irreducible integer polynomials whose complex roots lie in the open Serre
interval `(aSerre, bSerre)` (hence are positive reals), with degrees → ∞ and
root means → the Serre first moment `m := ∫ x d(serreMeasure gSerre aSerre bSerre)`.

## Route
1. `m < 1.89831`: `Submission.SerreMean.serre_mean` (with `aSerre_pos`,
   `a_lt_b`, `gSerre_pos.le`, `gSerre_le_one`) gives
   `m = gSerre·√(aSerre·bSerre) + (1−gSerre)·(aSerre+bSerre)/2`, and
   `Submission.SerreExample.serre_moment_lt_189831` bounds that by `1.89831`.
2. Choose `c1` with `m < c1 < 1.89831` (e.g. `c1 := (m + 1.89831)/2`).
3. Roots positivity: from `(aSerre:ℂ) < z` and `0 < aSerre` (reals are
   ordered in ℂ by `ComplexOrder`), get `(0:ℂ) < z`.
4. `Submission.Assembly.family_of_converse_data` (with the root mean
   convergence and `m < c1`) yields the injective family `f` of totally
   positive algebraic integers with `trace (f n) < c1·degree (f n)`.
5. `Submission.Reduction.lambda_SSS_le_of_family c1 f ...` gives
   `lambda_SSS ≤ c1`, and `Submission.Helpers.lambda_SSS_lt_of_le` (with
   `c1 < 1.89831`) closes the theorem.
-/

noncomputable section

open MeasureTheory
open ComplexOrder
open Filter
open AlgebraicIntegers
open scoped Real ENNReal Topology

namespace Submission.FinalAssembly

open Submission.Notions
open Submission.Serre
open Submission.SerreExample
open Submission.SerreMean
open Submission.SupportConcentration
open Submission.Assembly
open Submission.Reduction
open Submission.Helpers

/-- `theorem_1_1` from the converse output on Serre's measure. -/
theorem theorem_1_1_of_converse
    (hconv : ∃ R : ℕ → Polynomial ℤ,
      (∀ n : ℕ, (R n).Monic ∧ Irreducible (R n) ∧ 1 ≤ (R n).natDegree) ∧
      (∀ n : ℕ, ∀ z : ℂ, Polynomial.aeval z (R n) = 0 → (aSerre : ℂ) < z ∧ z < (bSerre : ℂ)) ∧
      Tendsto (fun n : ℕ => (R n).natDegree) atTop atTop ∧
      Tendsto (fun n : ℕ => rootMeanReal (R n)) atTop
        (𝓝 (∫ x : ℝ, x ∂serreMeasure gSerre aSerre bSerre))) :
    lambda_SSS < 1.89831 := by
  rcases hconv with ⟨R, hR, hroots, hdeg, hmean⟩
  let m : ℝ := ∫ x : ℝ, x ∂serreMeasure gSerre aSerre bSerre
  have hmean_m : Tendsto (fun n : ℕ => rootMeanReal (R n)) atTop (𝓝 m) := by
    simpa [m] using hmean
  have hm_lt : m < 1.89831 := by
    have hm_eq : m = gSerre * Real.sqrt (aSerre * bSerre) +
        (1 - gSerre) * (aSerre + bSerre) / 2 := by
      dsimp [m]
      exact serre_mean (a := aSerre) (b := bSerre) (γ := gSerre)
        aSerre_pos a_lt_b gSerre_pos.le gSerre_le_one
    rw [hm_eq]
    exact serre_moment_lt_189831
  let c1 : ℝ := (m + 1.89831) / 2
  have hmc1 : m < c1 := by dsimp [c1]; linarith
  have hc1lt : c1 < 1.89831 := by dsimp [c1]; linarith
  have hpos : ∀ n : ℕ, ∀ z : ℂ, Polynomial.aeval z (R n) = 0 → (0 : ℂ) < z := by
    intro n z hz
    have hzab : (aSerre : ℂ) < z ∧ z < (bSerre : ℂ) := hroots n z hz
    rw [Complex.pos_iff]
    constructor
    · have hre_lt : (aSerre : ℂ).re < z.re := (Complex.lt_def.mp hzab.1).1
      have hre : aSerre < z.re := by simpa using hre_lt
      linarith [aSerre_pos]
    · have him : (aSerre : ℂ).im = z.im := (Complex.lt_def.mp hzab.1).2
      simpa using him
  obtain ⟨f, hinj, hfam⟩ := family_of_converse_data hR hpos hdeg hmean_m hmc1
  have hle : lambda_SSS ≤ c1 := lambda_SSS_le_of_family c1 f hinj hfam
  exact lambda_SSS_lt_of_le hc1lt hle

end Submission.FinalAssembly

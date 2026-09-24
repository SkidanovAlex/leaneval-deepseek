import Mathlib
import Submission.Commons.NumberTheory.Mertens.mertens_lower
import Submission.Commons.NumberTheory.Mertens.corr_partial_sums_tendsto_tsum
import Submission.Commons.NumberTheory.Mertens.sum_log_prime_ratio_real_tendsto
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

open Filter Finset
open scoped BigOperators Topology

namespace Commons.NumberTheory.Mertens

noncomputable section

/-- `Σ_{p ≤ x} log(p/(p-1))` with the floor convention for reals. -/
def pecLogRatioSum (x : ℝ) : ℝ :=
  ∑ p ∈ (⌊x⌋₊).primesLE, Real.log ((p : ℝ) / ((p : ℝ) - 1))

/-- `Σ_{p ≤ x} (log(p/(p-1)) - 1/p)` with the floor convention for reals. -/
def pecCorrPartSum (x : ℝ) : ℝ :=
  ∑ p ∈ (⌊x⌋₊).primesLE, (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - (1 : ℝ) / p)

lemma pecLogRatioSum_eq_add (x : ℝ) :
    pecLogRatioSum x = pecCorrPartSum x + primeRecips x := by
  unfold pecLogRatioSum pecCorrPartSum primeRecips
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro p hp
  ring

theorem prime_euler_constant_identity :
    ∀ ⦃M : ℝ⦄,
      Filter.Tendsto (fun x : ℝ =>
        Commons.NumberTheory.Mertens.primeRecips x - Real.log (Real.log x))
        Filter.atTop (nhds M) →
        M + (∑' p : Nat.Primes,
          (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - (1 : ℝ) / p)) =
          Real.eulerMascheroniConstant := by
  intro M hM
  let C : ℝ := ∑' p : Nat.Primes,
    (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - (1 : ℝ) / p)
  have hC : Tendsto pecCorrPartSum atTop (nhds C) := by
    change Tendsto (fun x : ℝ =>
        ∑ p ∈ (⌊x⌋₊).primesLE, (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - (1 : ℝ) / p))
        atTop (nhds (∑' p : Nat.Primes,
          (Real.log ((p : ℝ) / ((p : ℝ) - 1)) - (1 : ℝ) / p)))
    simpa [C] using corr_partial_sums_tendsto_tsum
  have hS : Tendsto (fun x => pecLogRatioSum x - Real.log (Real.log x)) atTop
      (nhds Real.eulerMascheroniConstant) := by
    change Tendsto (fun x : ℝ =>
        (∑ p ∈ (⌊x⌋₊).primesLE, Real.log ((p : ℝ) / ((p : ℝ) - 1))) -
          Real.log (Real.log x)) atTop (nhds Real.eulerMascheroniConstant)
    exact sum_log_prime_ratio_real_tendsto
  have hEq : (fun x : ℝ => pecCorrPartSum x + (primeRecips x - Real.log (Real.log x))) =
      fun x : ℝ => pecLogRatioSum x - Real.log (Real.log x) := by
    funext x
    rw [pecLogRatioSum_eq_add]
    ring
  have hSum : Tendsto (fun x : ℝ =>
      pecCorrPartSum x + (primeRecips x - Real.log (Real.log x))) atTop (nhds (C + M)) :=
    hC.add hM
  have hSum' : Tendsto (fun x : ℝ =>
      pecCorrPartSum x + (primeRecips x - Real.log (Real.log x))) atTop
      (nhds Real.eulerMascheroniConstant) := by
    simpa [hEq] using hS
  have hEqConst : C + M = Real.eulerMascheroniConstant := tendsto_nhds_unique hSum hSum'
  have hMadd : M + C = Real.eulerMascheroniConstant := by
    linarith
  simpa [C, add_comm, add_left_comm, add_assoc] using hMadd

end

end Commons.NumberTheory.Mertens

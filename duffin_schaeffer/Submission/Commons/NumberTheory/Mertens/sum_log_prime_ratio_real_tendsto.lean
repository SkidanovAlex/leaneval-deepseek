import Mathlib
import Submission.Commons.NumberTheory.Mertens.mertens_lower
import Submission.Commons.NumberTheory.Mertens.corr_partial_sums_tendsto_tsum
import Submission.Commons.NumberTheory.Mertens.second_mertens_converges
import Submission.Commons.NumberTheory.Mertens.primeZeta_pole
import Submission.Commons.NumberTheory.Mertens.primeSmoothLimit_of_secondMertens

open Filter Finset
open scoped BigOperators Topology

namespace Commons.NumberTheory.Mertens

noncomputable section

def logRatioSum (x : ℝ) : ℝ :=
  ∑ p ∈ (⌊x⌋₊).primesLE, Real.log ((p : ℝ) / ((p : ℝ) - 1))

def logRatioCorrSum (x : ℝ) : ℝ :=
  ∑ p ∈ (⌊x⌋₊).primesLE, corrTerm p

private lemma summand_eq {p : ℕ} (hp : 2 ≤ p) :
    Real.log ((p : ℝ) / ((p : ℝ) - 1)) = (1 : ℝ) / p + corrTerm p := by
  unfold corrTerm
  ring

private lemma main_decomp (x : ℝ) :
    logRatioSum x - Real.log (Real.log x) =
      (primeRecips x - Real.log (Real.log x)) + logRatioCorrSum x := by
  unfold logRatioSum logRatioCorrSum
  have hcong : (∑ p ∈ (⌊x⌋₊).primesLE,
      Real.log ((p : ℝ) / ((p : ℝ) - 1))) =
      ∑ p ∈ (⌊x⌋₊).primesLE, ((1 : ℝ) / p + corrTerm p) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    exact summand_eq (Nat.two_le_of_mem_primesLE hp)
  calc
    (∑ p ∈ (⌊x⌋₊).primesLE, Real.log ((p : ℝ) / ((p : ℝ) - 1))) -
        Real.log (Real.log x)
        = (∑ p ∈ (⌊x⌋₊).primesLE, ((1 : ℝ) / p + corrTerm p)) -
            Real.log (Real.log x) := by rw [hcong]
    _ = (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / p) -
        Real.log (Real.log x) + (∑ p ∈ (⌊x⌋₊).primesLE, corrTerm p) := by
        rw [Finset.sum_add_distrib]
        abel
    _ = (primeRecips x - Real.log (Real.log x)) + logRatioCorrSum x := by
        unfold primeRecips logRatioCorrSum
        rfl

private def corrTotal : ℝ :=
  ∑' p : Nat.Primes,
    (Real.log (((p : ℕ) : ℝ) / (((p : ℕ) : ℝ) - 1)) - (1 : ℝ) / ((p : ℕ) : ℝ))

-- identity: M + C = γ  (glue of B1 & B2)
private lemma mertens_identity {M : ℝ}
    (hM : Tendsto (fun x : ℝ => primeRecips x - Real.log (Real.log x)) atTop (nhds M)) :
    M + corrTotal = Real.eulerMascheroniConstant := by
  have hT1 : Tendsto (fun ε : ℝ =>
      (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + ε))) + Real.log ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (M - Real.eulerMascheroniConstant)) :=
    primeSmoothLimit_of_secondMertens hM
  have hshift : Tendsto (fun ε : ℝ => 1 + ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhdsWithin (1 : ℝ) (Set.Ioi (1 : ℝ))) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · apply tendsto_nhdsWithin_of_tendsto_nhds
      have hcont : Continuous (fun ε : ℝ => (1 : ℝ) + ε) :=
        (continuous_const : Continuous fun _ : ℝ => (1 : ℝ)).add continuous_id
      simpa using hcont.tendsto (0 : ℝ)
    · have hb : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), (0 : ℝ) < ε := eventually_mem_nhdsWithin
      filter_upwards [hb] with ε hε
      simp at hε ⊢
      linarith
  have hc := primeZeta_pole.comp hshift
  have heq : (fun ε : ℝ =>
        (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + ε))) + Real.log ε) =
      ((fun s : ℝ => (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-s)) + Real.log (s - 1)) ∘
        (fun ε : ℝ => 1 + ε)) := by
    funext ε
    dsimp
    rw [show ((1 : ℝ) + ε) - 1 = ε by ring]
  have hT2 : Tendsto (fun ε : ℝ =>
        (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + ε))) + Real.log ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds (- corrTotal)) := by
    rw [heq]
    exact hc
  have hEq : M - Real.eulerMascheroniConstant = -corrTotal :=
    tendsto_nhds_unique hT1 hT2
  linarith

-- corr partial sums (real version, converting tsum expression)
private lemma corr_partial_tendsto :
    Tendsto (fun x : ℝ => logRatioCorrSum x) atTop (nhds corrTotal) := by
  simpa [logRatioCorrSum, corrTotal, corrTerm] using corr_partial_sums_tendsto_tsum

-- MAIN
theorem sum_log_prime_ratio_real_tendsto :
    Filter.Tendsto (fun x : ℝ =>
      (∑ p ∈ (⌊x⌋₊).primesLE, Real.log ((p : ℝ) / ((p : ℝ) - 1))) -
        Real.log (Real.log x))
      Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  rcases second_mertens_converges with ⟨M, hM⟩
  have hId := mertens_identity hM
  have hCorr := corr_partial_tendsto
  have hAdd : Tendsto (fun x : ℝ =>
      (primeRecips x - Real.log (Real.log x)) + logRatioCorrSum x) atTop
      (nhds (M + corrTotal)) := hM.add hCorr
  have hMain : Tendsto (fun x : ℝ => logRatioSum x - Real.log (Real.log x)) atTop
      (nhds (M + corrTotal)) := by
    refine hAdd.congr' ?_
    filter_upwards with x
    exact (main_decomp x).symm
  have hFinal : Tendsto (fun x : ℝ => logRatioSum x - Real.log (Real.log x)) atTop
      (nhds Real.eulerMascheroniConstant) := by
    simpa [hId] using hMain
  simpa [logRatioSum] using hFinal

end

end Commons.NumberTheory.Mertens

import Mathlib
import Submission.Commons.NumberTheory.Mertens.mertens_lower
import Submission.Commons.NumberTheory.Mertens.tsum_primes_eq_sum_rpowDiff
import Submission.Commons.NumberTheory.Mertens.smoothLimit_of_tendsto_sub_loglog

open Filter Finset
open scoped BigOperators Topology

namespace Commons.NumberTheory.Mertens

noncomputable section

/-- `primeRecips` at a natural equals the sum of `1/p` over primes `p ≤ k`. -/
private lemma primeRecips_natCast (k : ℕ) :
    primeRecips (k : ℝ) = ∑ p ∈ k.primesLE, (1 : ℝ) / (p : ℝ) := by
  unfold primeRecips
  rw [Nat.floor_natCast]

/--
**Smooth limit from the second Mertens theorem.**

Assuming the sharp-cutoff second Mertens asymptotic
`Σ_{p ≤ x} 1/p − log log x → M`, the smooth (prime-zeta) sum satisfies
`Σ_p p^{-(1+ε)} + log ε → M − γ` as `ε → 0⁺`.
-/
theorem primeSmoothLimit_of_secondMertens {M : ℝ} :
    Filter.Tendsto (fun x : ℝ =>
      (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / p) - Real.log (Real.log x))
      Filter.atTop (nhds M) →
    Filter.Tendsto (fun ε : ℝ =>
      (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + ε))) + Real.log ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (M - Real.eulerMascheroniConstant)) := by
  intro hM
  -- The sequence-level hypothesis on `a k := primeRecips k` (values at integers).
  let a : ℕ → ℝ := fun k : ℕ => primeRecips (k : ℝ)
  have ha : Tendsto (fun k : ℕ => a k - Real.log (Real.log (k : ℝ))) atTop (nhds M) := by
    dsimp [a]
    have hM' : Tendsto (fun x : ℝ => primeRecips x - Real.log (Real.log x)) atTop (nhds M) := by
      simpa [primeRecips] using hM
    exact hM'.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  -- Apply the smooth-limit lemma for general weight sequences.
  have hlim := smoothLimit_of_tendsto_sub_loglog (a := a) (M := M) ha
  refine hlim.congr' ?_
  -- The two functions agree pointwise for every `ε > 0`.
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  have hG1 := tsum_primes_eq_sum_rpowDiff (ε := ε) hε0
  -- Inside the series, `primeRecips k` is the sum over `p ∈ k.primesLE`.
  have hfun : (fun k : ℕ => if 2 ≤ k then
        (∑ p ∈ k.primesLE, (1 : ℝ) / (p : ℝ)) *
          (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0)
      = fun k : ℕ => if 2 ≤ k then a k *
          (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0 := by
    funext k
    by_cases hk : 2 ≤ k
    · simp [hk, a, primeRecips_natCast]
    · simp [hk]
  calc
    (∑' k : ℕ, if 2 ≤ k then a k *
          (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0) + Real.log ε
        = (∑' k : ℕ, if 2 ≤ k then
            (∑ p ∈ k.primesLE, (1 : ℝ) / (p : ℝ)) *
              (((k : ℝ) ^ (-ε)) - ((((k + 1) : ℕ) : ℝ) ^ (-ε))) else 0) + Real.log ε := by
            rw [← hfun]
    _ = (∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(1 + ε))) + Real.log ε := by
            rw [← hG1]

end

end Commons.NumberTheory.Mertens

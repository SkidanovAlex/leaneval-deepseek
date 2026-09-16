import Submission.ZagierHoffmanProof.GenLSeries

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Polynomial PowerSeries Finset Filter
open scoped WithZero Topology

/-!
# The evaluation of the depth-one `L`-series at a point (N1 of the ζ_A ↔ CMPL bridge)

The paper's `L`-series is `𝓛(s;Q) = ∑_{i ≥ 0} (ω^s Q)^{(i)}` and its value at `θ` is what the
ζ_A ↔ CMPL bridge (Dac (4.2)) computes.  The workspace defines it coefficientwise (`atL1Gen`), so
its evaluation at a point `c` is a double sum

  `evalSeriesGen (atL1Gen q ω s Q) c = ∑'_n (∑'_i coeff n ((ω^sQ)^{(i)})) · c^n`,

and the content is the interchange of the two `tsum`s, which is justified by the *joint*
summability of `(n,i) ↦ coeff n (ψ^{(i)}) · c^n`, where `ψ := ω^s·Q` is both small and super-entire
(the two hypotheses the workspace has for every relevant object).  See
`LSeriesEvalSummable.summable_coeff_frobTwist_mul` for the proof of that summability.

## Main results

* `frobTwist_coeff_v` — `v (coeff n (ψ^{(i)})) = v (coeff n ψ) ^ (q^i)`.
* ★★★ `evalSeriesGen_atL1Gen` — **the depth-one evaluation**:
  `evalSeriesGen (atL1Gen q ω s 1) c = ∑'_i (evalSeriesGen (frobTwist i ω) c)^s`.
-/

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]

section Coeff

variable (q : ℕ) [FrobPow K q]

/-- The valuation of the coefficients of a Frobenius twist:
`v (coeff n (ψ^{(i)})) = v (coeff n ψ)^(q^i)`. -/
lemma frobTwist_coeff_v (i n : ℕ) (ψ : PowerSeries K) :
    Valued.v (PowerSeries.coeff n (frobTwist (R := K) (p := q) i ψ))
      = (Valued.v (PowerSeries.coeff n ψ)) ^ (q ^ i) := by
  rw [frobTwist_coeff, map_pow]

end Coeff

section Eval

variable (q : ℕ) [FrobPow K q]

/-- **The depth-one `L`-series evaluated at a point**: the double sum defining the value of
`atL1Gen q ω s 1` interchanges (given the joint summability of the double family, which holds for
small super-entire `ω` — see `LSeriesEvalSummable.summable_coeff_frobTwist_mul`). -/
theorem evalSeriesGen_atL1Gen {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    {ω : PowerSeries K} (hse : GSuperEntire γ ω) (s : ℕ) (hs : 1 ≤ s) (c : K)
    (hsum : Summable fun p : ℕ × ℕ =>
      PowerSeries.coeff p.1 (frobTwist (R := K) (p := q) p.2 (ω ^ s * 1)) * c ^ p.1) :
    evalSeriesGen (atL1Gen q ω s (1 : PowerSeries K)) c
      = ∑' i : ℕ, (evalSeriesGen (frobTwist (R := K) (p := q) i ω) c) ^ s := by
  classical
  set co : ℕ → ℕ → K := fun n i =>
    PowerSeries.coeff n (frobTwist (R := K) (p := q) i (ω ^ s * 1)) * c ^ n with hco
  have h1 : evalSeriesGen (atL1Gen q ω s (1 : PowerSeries K)) c = ∑' n, ∑' i, co n i := by
    rw [evalSeriesGen_def]
    refine tsum_congr fun n => ?_
    rw [coeff_atL1Gen, ← tsum_mul_right]
  have h2 : (∑' n, ∑' i, co n i) = ∑' i, ∑' n, co n i :=
    (Summable.tsum_comm (f := fun n i => co n i) hsum).symm
  rw [h1, h2]
  refine tsum_congr fun i => ?_
  have hfun : (fun n : ℕ => co n i)
      = fun n : ℕ => PowerSeries.coeff n ((frobTwist (R := K) (p := q) i ω) ^ s) * c ^ n := by
    funext n
    rw [hco]
    simp only [mul_one, frobTwist_pow]
  rw [hfun, ← evalSeriesGen_def]
  exact evalSeriesGen_pow hγ harch (hse.frobTwist hγ.le i) s c

end Eval

end ZagierHoffmanPositiveChar

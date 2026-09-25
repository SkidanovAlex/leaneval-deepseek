import Mathlib
import Submission.Work.RHContract.A.ca_margin_lower
import Submission.Commons.NumberTheory.Robin.robin_caFval_small

/-!
# Region I: the vocabulary

We prove Robin's inequality at the colossally abundant numbers `N_ε` whose largest prime
factor `ξ(ε)` lies in `[1530, 30000)` — unconditionally, by a certified computation.

This file fixes the vocabulary:

* `caS p k = p + p² + … + p^k` and `cF p k = log(1 + 1/caS p k)/log p`, the Nicolas (4.5)
  level function `F(p,k)`, which controls the exponent of `p` in `N_ε`:
  `k ≤ ⌊caMu p ε⌋₊ ↔ ε ≤ cF p k`;
* `logLowQ x ≤ Real.log x ≤ logUpQ x`, certified rational bounds for `log` at rationals;
* `Flo p k ≤ cF p k ≤ Fhi p k`, certified rational bounds for the level function.
-/

open scoped BigOperators

namespace Work.RHContract.RegionI

noncomputable section

/-- `S_k(p) = p + p² + … + p^k`. -/
def caS (p k : ℕ) : ℕ := ∑ i ∈ Finset.range k, p ^ (i + 1)

/-- The Nicolas level function `F(p,k) = log((p^{k+1}−1)/(p^{k+1}−p))/log p`.  Its relevance:
`k ≤ ⌊caMu p ε⌋₊ ↔ ε ≤ cF p k` (`Commons.NumberTheory.Robin.caMu_ge_iff_caF`). -/
def cF (p k : ℕ) : ℝ :=
  Real.log (((p : ℝ) ^ (k + 1) - 1) / (((p : ℝ) ^ (k + 1)) - (p : ℝ))) / Real.log (p : ℝ)

/-- The `N`-th Taylor polynomial `Σ_{i<N} (-1)^i t^{i+1}/(i+1)` of `log (1+t)`. -/
def altLog (t : ℚ) (N : ℕ) : ℚ :=
  ∑ i ∈ Finset.range N, (-1 : ℚ) ^ i * t ^ (i + 1) / ((i + 1 : ℕ) : ℚ)

def log2LoQ : ℚ := 6931471803 / 10 ^ 10
def log2UpQ : ℚ := 6931471809 / 10 ^ 10

/-- Certified rational **lower** bound for `Real.log (1+t)`, valid for `0 ≤ t ≤ 1`.
Three regimes keep the rationals small: a short alternating sum for small `t`, a longer one
up to `t ≤ 1/2`, and the `atanh`-type series for `t ≤ 1`. -/
def log1pLo (t : ℚ) : ℚ :=
  if t ≤ 1 / 1024 then altLog t 4
  else if t ≤ 1 / 32 then altLog t 10
  else if t ≤ 1 / 2 then altLog t 46
  else Commons.NumberTheory.Robin.RobinCaFval.logOneAddLower t

/-- Certified rational **upper** bound for `Real.log (1+t)`, valid for `0 ≤ t ≤ 1`. -/
def log1pUp (t : ℚ) : ℚ :=
  if t ≤ 1 / 1024 then altLog t 5
  else if t ≤ 1 / 32 then altLog t 11
  else if t ≤ 1 / 2 then altLog t 47
  else Commons.NumberTheory.Robin.RobinCaFval.logOneAddUpper t

/-- Certified rational lower bound for `Real.log x`, valid for `1 ≤ x < 2^26`. -/
def logLowAuxQ : ℚ → ℕ → ℚ
  | x, 0 => if x < 2 then log1pLo (x - 1) else 0
  | x, k + 1 => if x < 2 then log1pLo (x - 1) else log2LoQ + logLowAuxQ (x / 2) k

/-- Certified rational upper bound for `Real.log x`, valid for `1 ≤ x < 2^26`. -/
def logUpAuxQ : ℚ → ℕ → ℚ
  | x, 0 => if x < 2 then log1pUp (x - 1) else 0
  | x, k + 1 => if x < 2 then log1pUp (x - 1) else log2UpQ + logUpAuxQ (x / 2) k

/-- `logLowQ x ≤ Real.log x` for `1 ≤ x < 2^26`. -/
def logLowQ (x : ℚ) : ℚ := logLowAuxQ x 26

/-- `Real.log x ≤ logUpQ x` for `1 ≤ x < 2^26`. -/
def logUpQ (x : ℚ) : ℚ := logUpAuxQ x 26

/-- The rational argument of the logarithm in `cF`. -/
def cFr (p k : ℕ) : ℚ := ((p : ℚ) ^ (k + 1) - 1) / ((p : ℚ) ^ (k + 1) - (p : ℚ))

/-- Rational lower bound for `F(p,k) = log(cFr p k)/log p`. -/
def Flo (p k : ℕ) : ℚ := logLowQ (cFr p k) / logUpQ (p : ℚ)

/-- Rational upper bound for `F(p,k) = log(cFr p k)/log p`. -/
def Fhi (p k : ℕ) : ℚ := logUpQ (cFr p k) / logLowQ (p : ℚ)

/-- Round `q` down to `k` decimal places. -/
def rd (k : ℕ) (q : ℚ) : ℚ := (Rat.floor (q * (10 : ℚ) ^ k) : ℚ) / (10 : ℚ) ^ k

end

end Work.RHContract.RegionI

namespace Work.RHContract.RegionI

noncomputable section

/-- The corpus' computable primality test, as a `Bool`. -/
def isP (p : ℕ) : Bool := Commons.NumberTheory.Robin.RobinCaFval.isPrimeC p

lemma isP_iff (p : ℕ) : isP p = true ↔ Nat.Prime p :=
  Commons.NumberTheory.Robin.RobinCaFval.isPrimeC_iff p

/-- The primes `≤ N` as a list (computable). -/
def smallP (N : ℕ) : List ℕ := (List.range (N + 1)).filter isP

/-- `Σ_{p ≤ N, p prime} p^{-2}` as a computable rational (used for the `k = 1` part of the
correction sum). -/
def s2small (N : ℕ) : ℚ := ∑ p ∈ (smallP N).toFinset, (p : ℚ) ^ (-2 : ℤ)

/-- The number of levels `k < K` at which `p ≤ y k`. -/
def yA {K : ℕ} (y : Fin K → ℕ) (p : ℕ) : ℕ :=
  (Finset.univ.filter (fun k : Fin K => p ≤ y k)).card

/-- The small-prime part `Σ_{p ≤ y1} p^{-(A_p+1)}` of the correction sum `B`. -/
def bsmall {K : ℕ} (y : Fin K → ℕ) (y1 : ℕ) : ℚ :=
  ∑ p ∈ (smallP y1).toFinset, (p : ℚ) ^ (-(((yA y p : ℕ) : ℤ) + 1))

/-- The primes `≤ N` as a `Finset`, in a form the *kernel* can evaluate.

`(smallP N).toFinset` is useless for `decide`, because `List.toFinset` goes through
`List.dedup`, which is not structurally recursive and so does not reduce in the kernel.
`Finset.range` and `Finset.filter` do reduce, so this is the version to use in any
hypothesis that a `decide +kernel` certificate must discharge. -/
def pfinset (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter (fun p => isP p = true)

/-- `Σ_{p ≤ N} p^{-2}` as a computable rational, the kernel-friendly form of `s2small`. -/
def s2f (N : ℕ) : ℚ := ∑ p ∈ pfinset N, (p : ℚ) ^ (-2 : ℤ)

/-- `Σ_{p ≤ N} p^{-(A_p + 1)}`, the small-prime part of the correction sum `B` in the form
a `decide` certificate can evaluate. -/
def asum (A : ℕ → ℕ) (N : ℕ) : ℚ :=
  ∑ p ∈ pfinset N, (p : ℚ) ^ (-(((A p : ℕ) : ℤ) + 1))

end

end Work.RHContract.RegionI

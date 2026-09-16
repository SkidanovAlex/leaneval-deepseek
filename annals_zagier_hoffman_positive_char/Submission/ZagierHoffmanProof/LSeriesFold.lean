import Submission.ZagierHoffmanProof.LSeries

/-!
# The `k`-fold recursion for the depth-one `L`-series

Let `L = ∑_{i ≥ 0} (ω^s Q)^{(i)}` be the depth-one `L`-series of `LSeries.lean`.  The defining
recursion `L^{(k)} = L - ∑_{i < k}(ω^sQ)^{(i)}` has the following consequence, used throughout the
`t`-motive chapter: for every `k`,

  `L = ∑_{i < k} (ω^sQ)^{(i)} + L^{(k)}`    (`atL1_fold`).

Equivalently, the `k`-th Frobenius twist of `L` is the `k`-tail `∑_{i ≥ k}(ω^sQ)^{(i)}`
(`frobTwist_atL1`).  We also record that `L` is again *small* (`IsSmall.atL1`), which is what makes
the construction iterable to higher depth.

## Main results

* `frobTwist_atL1` — the `k`-th twist of `L` is the `k`-tail of the defining series.
* `atL1_fold` — `L = ∑_{i<k}(ω^sQ)^{(i)} + L^{(k)}`.
* `isSmall_atL1` — the `L`-series of a small series is small.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰] [CompleteSpace K] [NonarchimedeanAddGroup K]
variable {q : ℕ} [FrobPow K q]

/-- The `k`-th Frobenius twist of the depth-one `L`-series is the `k`-tail of its defining
family: `(∑_{i ≥ 0} (ω^sQ)^{(i)})^{(k)} = ∑_{i ≥ 0} (ω^sQ)^{(i+k)}`. -/
lemma frobTwist_atL1 (hq : 2 ≤ q) {ω : PowerSeries K} (hω : IsSmall ω)
    {Q : PowerSeries K} (hQ : IsSmall Q) (s : ℕ) (k : ℕ) :
    frobTwist (R := K) (p := q) k (atL1 q ω s Q)
      = PowerSeries.mk (fun n : ℕ => ∑' i : ℕ,
          PowerSeries.coeff n (frobTwist (R := K) (p := q) (i + k) (ω ^ s * Q))) := by
  ext n
  have hsum := summable_coeff_atL1_term q hq hω hQ s n
  rw [frobTwist_coeff, coeff_atL1, PowerSeries.coeff_mk,
    ZagierHoffmanPositiveChar.tsum_pow_frobPow hsum k]
  refine tsum_congr (fun i => ?_)
  simp only [frobTwist_coeff, pow_mul, pow_add]

/-- The tail form of `atL1`: the tail `∑_{i ≥ k}(ω^sQ)^{(i)}` is the `k`-th twist. -/
lemma atL1_shift (hq : 2 ≤ q) {ω : PowerSeries K} (hω : IsSmall ω)
    {Q : PowerSeries K} (hQ : IsSmall Q) (s : ℕ) (k : ℕ) :
    PowerSeries.mk (fun n : ℕ => ∑' i : ℕ,
        PowerSeries.coeff n (frobTwist (R := K) (p := q) (i + k) (ω ^ s * Q)))
      = frobTwist (R := K) (p := q) k (atL1 q ω s Q) :=
  (frobTwist_atL1 hq hω hQ s k).symm

/-- **The `k`-fold recursion of the depth-one `L`-series**:
`L = ∑_{i < k} (ω^sQ)^{(i)} + L^{(k)}`. -/
theorem atL1_fold (hq : 2 ≤ q) {ω : PowerSeries K} (hω : IsSmall ω)
    {Q : PowerSeries K} (hQ : IsSmall Q) (s : ℕ) (k : ℕ) :
    atL1 q ω s Q
      = (∑ i ∈ Finset.range k, frobTwist (R := K) (p := q) i (ω ^ s * Q))
        + frobTwist (R := K) (p := q) k (atL1 q ω s Q) := by
  ext n
  have hsum := summable_coeff_atL1_term q hq hω hQ s n
  rw [map_add (PowerSeries.coeff n), map_sum, coeff_atL1,
    frobTwist_atL1 hq hω hQ s k, PowerSeries.coeff_mk]
  rw [← Summable.sum_add_tsum_nat_add (f := fun i : ℕ =>
    PowerSeries.coeff n (frobTwist (R := K) (p := q) i (ω ^ s * Q))) k hsum]

/-- The depth-one `L`-series of a small series is again small. -/
lemma isSmall_atL1 {ω : PowerSeries K} (hq : 2 ≤ q) (hω : IsSmall ω)
    {Q : PowerSeries K} (hQ : IsSmall Q) (s : ℕ) : IsSmall (atL1 q ω s Q) := by
  intro n
  rw [coeff_atL1]
  refine Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le
    (summable_coeff_atL1_term q hq hω hQ s n) (fun i => ?_)
  rw [frobTwist_coeff, map_pow]
  have h2 : Valued.v (PowerSeries.coeff n (ω ^ s * Q)) ≤ WithZero.exp (-1) :=
    IsSmall.pow_mul hω hQ s n
  calc (Valued.v (PowerSeries.coeff n (ω ^ s * Q))) ^ (q ^ i)
      ≤ (WithZero.exp (-1)) ^ (q ^ i) := pow_le_pow_left' h2 _
    _ = WithZero.exp (-1 * (((q ^ i : ℕ)) : ℤ)) := expmul (-1) (q ^ i)
    _ ≤ WithZero.exp (-1) := by
        apply WithZero.exp_le_exp.mpr
        have h1 : (1 : ℤ) ≤ ((q ^ i : ℕ) : ℤ) := by
          have : 1 ≤ q ^ i := Nat.succ_le_of_lt (pow_pos (by omega : 0 < q) i)
          exact_mod_cast this
        omega

/-- The depth-one `L`-series of a small series has bounded coefficients. -/
lemma seriesBounded_atL1 {ω : PowerSeries K} (hq : 2 ≤ q) (hω : IsSmall ω)
    {Q : PowerSeries K} (hQ : IsSmall Q) (s : ℕ) : SeriesBounded (atL1 q ω s Q) :=
  ⟨-1, fun n => isSmall_atL1 hq hω hQ s n⟩

end ZagierHoffmanPositiveChar

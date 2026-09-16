import Submission.ZagierHoffmanProof.GenLSeries
import Submission.Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le_general

/-!
# The `k`-fold recursion for the depth-one `L`-series over an arbitrary value group

This is the generic version (arbitrary value group `Γ₀`, fixed small `γ`) of `LSeriesFold.lean`.
Let `L = ∑_{i ≥ 0} (ω^s Q)^{(i)}` be the depth-one `L`-series (`atL1Gen`).  The defining
recursion implies, for every `k`,

  `L = ∑_{i < k} (ω^sQ)^{(i)} + L^{(k)}`    (`atL1Gen_fold`),

equivalently `(∑_{i ≥ 0} (ω^sQ)^{(i)})^{(k)} = ∑_{i ≥ 0} (ω^sQ)^{(i+k)}`
(`frobTwist_atL1Gen`).  We also record that `L` is again *small* (`GIsSmall.atL1Gen`).

## Main results

* `frobTwist_atL1Gen`, `atL1Gen_shift`, `atL1Gen_fold`, `gIsSmall_atL1Gen`.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable [CompleteSpace K] [NonarchimedeanAddGroup K]
variable {q : ℕ} [FrobPow K q]

/-- The `k`-th Frobenius twist of the depth-one `L`-series is the `k`-tail of its defining
family: `(∑_{i ≥ 0} (ω^sQ)^{(i)})^{(k)} = ∑_{i ≥ 0} (ω^sQ)^{(i+k)}`. -/
lemma frobTwist_atL1Gen {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    {ω : PowerSeries K} {Q : PowerSeries K} (s k : ℕ) (hF : GIsSmall γ (ω ^ s * Q)) :
    frobTwist (R := K) (p := q) k (atL1Gen q ω s Q)
      = PowerSeries.mk (fun n : ℕ => ∑' i : ℕ,
          PowerSeries.coeff n (frobTwist (R := K) (p := q) (i + k) (ω ^ s * Q))) := by
  ext n
  have hsum := summable_coeff_atL1Gen_term q hγ harch hq s hF n
  rw [frobTwist_coeff, coeff_atL1Gen, PowerSeries.coeff_mk,
    ZagierHoffmanPositiveChar.tsum_pow_frobPow_general hsum k]
  refine tsum_congr (fun i => ?_)
  simp only [frobTwist_coeff, pow_mul, pow_add]

/-- The tail form of `atL1Gen`: the tail `∑_{i ≥ k}(ω^sQ)^{(i)}` is the `k`-th twist. -/
lemma atL1Gen_shift {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    {ω : PowerSeries K} {Q : PowerSeries K} (s k : ℕ) (hF : GIsSmall γ (ω ^ s * Q)) :
    PowerSeries.mk (fun n : ℕ => ∑' i : ℕ,
        PowerSeries.coeff n (frobTwist (R := K) (p := q) (i + k) (ω ^ s * Q)))
      = frobTwist (R := K) (p := q) k (atL1Gen q ω s Q) :=
  (frobTwist_atL1Gen hγ harch hq s k hF).symm

/-- **The `k`-fold recursion of the depth-one `L`-series**:
`L = ∑_{i < k} (ω^sQ)^{(i)} + L^{(k)}`. -/
theorem atL1Gen_fold {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    {ω : PowerSeries K} {Q : PowerSeries K} (s k : ℕ) (hF : GIsSmall γ (ω ^ s * Q)) :
    atL1Gen q ω s Q
      = (∑ i ∈ Finset.range k, frobTwist (R := K) (p := q) i (ω ^ s * Q))
        + frobTwist (R := K) (p := q) k (atL1Gen q ω s Q) := by
  ext n
  have hsum := summable_coeff_atL1Gen_term q hγ harch hq s hF n
  rw [map_add (PowerSeries.coeff n), map_sum, coeff_atL1Gen,
    frobTwist_atL1Gen hγ harch hq s k hF, PowerSeries.coeff_mk]
  rw [← Summable.sum_add_tsum_nat_add (f := fun i : ℕ =>
    PowerSeries.coeff n (frobTwist (R := K) (p := q) i (ω ^ s * Q))) k hsum]

/-- The depth-one `L`-series of a small series is again small. -/
lemma gIsSmall_atL1Gen {γ : Γ₀} (hγ : γ < 1) (harch : GammaArchimedean Γ₀) (hq : 2 ≤ q)
    {ω : PowerSeries K} {Q : PowerSeries K} (s : ℕ) (hF : GIsSmall γ (ω ^ s * Q)) :
    GIsSmall γ (atL1Gen q ω s Q) := by
  intro n
  rw [coeff_atL1Gen]
  refine Commons.Topology.Algebra.Valued.v_tsum_le_of_forall_le_general
    (summable_coeff_atL1Gen_term q hγ harch hq s hF n) (fun i => ?_)
  rw [frobTwist_coeff, map_pow]
  have h2 : Valued.v (PowerSeries.coeff n (ω ^ s * Q)) ≤ γ := hF n
  calc (Valued.v (PowerSeries.coeff n (ω ^ s * Q))) ^ (q ^ i)
      ≤ γ ^ (q ^ i) := pow_le_pow_left' h2 _
    _ ≤ γ ^ 1 := pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ γ) hγ.le
        (Nat.succ_le_of_lt (pow_pos (by omega : 0 < q) i))
    _ = γ := pow_one γ

end ZagierHoffmanPositiveChar

import Submission.ZagierHoffmanProof.FrobPow
import Mathlib.Topology.Algebra.Valued.ValuedField
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The Frobenius power of an infinite sum

`(∑' i, f i) ^ (q ^ n) = ∑' i, (f i) ^ (q ^ n)` for a summable family in a complete
nonarchimedean valued field, when `q` is a *Frobenius exponent* (`FrobPow`) rather than a prime
characteristic.  This is the `FrobPow`-generalisation of the commons lemmas
`Commons.Topology.Algebra.Valued.tsum_pow_expChar` / `tsum_pow_expChar_general`.
-/

set_option autoImplicit false
open Filter
open scoped WithZero BigOperators Topology

namespace ZagierHoffmanPositiveChar

/-- `(∑' i, f i) ^ (q ^ n) = ∑' i, (f i) ^ (q ^ n)` over `ℤᵐ⁰`. -/
theorem tsum_pow_frobPow {K : Type*} [Field K] [Valued K ℤᵐ⁰] [CompleteSpace K]
    [NonarchimedeanAddGroup K] {q : ℕ} [FrobPow K q] {ι : Type*} {f : ι → K} (hf : Summable f)
    (n : ℕ) : (∑' i, f i) ^ (q ^ n) = ∑' i, (f i) ^ (q ^ n) := by
  have hcont : Continuous fun x : K => x ^ (q ^ n) := continuous_pow _
  have hlim : Tendsto (fun s : Finset ι => (∑ i ∈ s, f i) ^ (q ^ n)) atTop
      (𝓝 ((∑' i, f i) ^ (q ^ n))) :=
    hcont.tendsto (∑' i, f i) |>.comp (show Tendsto (fun s : Finset ι => ∑ i ∈ s, f i) atTop
      (𝓝 (∑' i, f i)) from hf.hasSum)
  have hsum : HasSum (fun i => (f i) ^ (q ^ n)) ((∑' i, f i) ^ (q ^ n)) := by
    have := hlim
    rw [show (fun s : Finset ι => (∑ i ∈ s, f i) ^ (q ^ n))
        = fun s : Finset ι => ∑ i ∈ s, (f i) ^ (q ^ n) from
        funext fun s => FrobPow.sum_pow s f n] at this
    exact this
  exact hsum.tsum_eq.symm

/-- `(∑' i, f i) ^ (q ^ n) = ∑' i, (f i) ^ (q ^ n)` over an arbitrary value group. -/
theorem tsum_pow_frobPow_general {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀]
    [Valued K Γ₀] [CompleteSpace K] [NonarchimedeanAddGroup K] {q : ℕ} [FrobPow K q]
    {ι : Type*} {f : ι → K} (hf : Summable f) (n : ℕ) :
    (∑' i, f i) ^ (q ^ n) = ∑' i, (f i) ^ (q ^ n) := by
  have hcont : Continuous fun x : K => x ^ (q ^ n) := continuous_pow _
  have hlim : Tendsto (fun s : Finset ι => (∑ i ∈ s, f i) ^ (q ^ n)) atTop
      (𝓝 ((∑' i, f i) ^ (q ^ n))) :=
    hcont.tendsto (∑' i, f i) |>.comp (show Tendsto (fun s : Finset ι => ∑ i ∈ s, f i) atTop
      (𝓝 (∑' i, f i)) from hf.hasSum)
  have hsum : HasSum (fun i => (f i) ^ (q ^ n)) ((∑' i, f i) ^ (q ^ n)) := by
    have := hlim
    rw [show (fun s : Finset ι => (∑ i ∈ s, f i) ^ (q ^ n))
        = fun s : Finset ι => ∑ i ∈ s, (f i) ^ (q ^ n) from
        funext fun s => FrobPow.sum_pow s f n] at this
    exact this
  exact hsum.tsum_eq.symm

end ZagierHoffmanPositiveChar

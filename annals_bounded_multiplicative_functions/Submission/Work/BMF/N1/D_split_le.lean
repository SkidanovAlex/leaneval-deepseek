import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.N1

open Polynomial Finset Real Complex BoundedMultiplicativeFunctions
open Work.BMF
open scoped ComplexConjugate

/-- Pointwise bound for a single summand of the sum defining `𝔻`: since `‖f p‖, ‖g p‖ ≤ 1`,
the real part of `f p * conj (g p)` is at least `-1`, so the summand is at most `2 / p`. -/
private lemma D_term_le {f g : ℕ → ℂ} (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1)
    (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {p : ℕ} (hp : p.Prime) :
    (1 - (f p * conj (g p)).re) / (p : ℝ) ≤ 2 / (p : ℝ) := by
  have hnorm : ‖f p * conj (g p)‖ ≤ 1 := by
    rw [norm_mul, norm_conj]
    nlinarith [norm_nonneg (f p), norm_nonneg (g p), hf p hp, hg p hp]
  have hre : -(1 : ℝ) ≤ (f p * conj (g p)).re := by
    have h1 := Complex.abs_re_le_norm (f p * conj (g p))
    have h2 := neg_le_abs (f p * conj (g p)).re
    linarith
  exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg p)

/-- Each summand of the sum defining `𝔻` is nonnegative (under the boundedness hypotheses),
so the whole sum is nonnegative and `𝔻 f g Y ^ 2` is exactly that sum. -/
private lemma D_sum_nonneg {f g : ℕ → ℂ} (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1)
    (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) (m : ℕ) :
    0 ≤ ∑ p ∈ m.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ) := by
  apply Finset.sum_nonneg
  intro p hp
  have hpP : p.Prime := Nat.prime_of_mem_primesLE hp
  have hnorm : ‖f p * conj (g p)‖ ≤ 1 := by
    rw [norm_mul, norm_conj]
    nlinarith [norm_nonneg (f p), norm_nonneg (g p), hf p hpP, hg p hpP]
  have hre : (f p * conj (g p)).re ≤ 1 := by
    have h1 := Complex.re_le_norm (f p * conj (g p))
    linarith
  exact div_nonneg (by linarith) (Nat.cast_nonneg p)

/-- The core finite-sum estimate: for `m ≤ n`, the sum of the `𝔻`-summands over the primes
`≤ n` exceeds the same sum over the primes `≤ m` by at most twice the reciprocal-prime mass
of the primes in `(m, n]`. -/
private lemma D_sum_sdiff_le {f g : ℕ → ℂ} (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1)
    (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) {m n : ℕ} (hmn : m ≤ n) :
    (∑ p ∈ n.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ)) ≤
      (∑ p ∈ m.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ)) +
        2 * ((∑ p ∈ n.primesLE, (1 : ℝ) / p) - (∑ p ∈ m.primesLE, (1 : ℝ) / p)) := by
  have hsub : m.primesLE ⊆ n.primesLE := Nat.primesLE_mono hmn
  have hA : (∑ p ∈ n.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ))
      = (∑ p ∈ n.primesLE \ m.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ))
        + (∑ p ∈ m.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ)) :=
    (Finset.sum_sdiff (s₁ := m.primesLE) (s₂ := n.primesLE)
      (f := fun p => (1 - (f p * conj (g p)).re) / (p : ℝ)) hsub).symm
  have hB : (∑ p ∈ n.primesLE, (1 : ℝ) / p)
      = (∑ p ∈ n.primesLE \ m.primesLE, (1 : ℝ) / p) + (∑ p ∈ m.primesLE, (1 : ℝ) / p) :=
    (Finset.sum_sdiff (s₁ := m.primesLE) (s₂ := n.primesLE)
      (f := fun p => (1 : ℝ) / (p : ℝ)) hsub).symm
  have hC : (∑ p ∈ n.primesLE \ m.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ))
      ≤ ∑ p ∈ n.primesLE \ m.primesLE, 2 / (p : ℝ) := by
    apply Finset.sum_le_sum
    intro p hp
    exact D_term_le hf hg (Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1)
  have hD : (∑ p ∈ n.primesLE \ m.primesLE, 2 / (p : ℝ))
      = 2 * (∑ p ∈ n.primesLE \ m.primesLE, (1 : ℝ) / (p : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hE : (∑ p ∈ n.primesLE \ m.primesLE, (1 : ℝ) / (p : ℝ))
      = (∑ p ∈ n.primesLE, (1 : ℝ) / (p : ℝ))
        - (∑ p ∈ m.primesLE, (1 : ℝ) / (p : ℝ)) := by linarith [hB]
  calc (∑ p ∈ n.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ))
      = (∑ p ∈ n.primesLE \ m.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ))
        + (∑ p ∈ m.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ)) := hA
    _ ≤ (∑ p ∈ n.primesLE \ m.primesLE, 2 / (p : ℝ))
        + (∑ p ∈ m.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ)) :=
        add_le_add hC le_rfl
    _ = 2 * (∑ p ∈ n.primesLE \ m.primesLE, (1 : ℝ) / (p : ℝ))
        + (∑ p ∈ m.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ)) := by rw [hD]
    _ = 2 * ((∑ p ∈ n.primesLE, (1 : ℝ) / (p : ℝ))
          - (∑ p ∈ m.primesLE, (1 : ℝ) / (p : ℝ)))
        + (∑ p ∈ m.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ)) := by rw [hE]
    _ = (∑ p ∈ m.primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ))
        + 2 * ((∑ p ∈ n.primesLE, (1 : ℝ) / (p : ℝ))
          - (∑ p ∈ m.primesLE, (1 : ℝ) / (p : ℝ))) := by ring

/-- Splitting the prime sum defining `𝔻` at a lower scale `Y ≤ Z`: passing from `Y` to `Z`
costs at most twice the reciprocal-prime mass of the primes in `(Y, Z]`. -/
theorem D_split_le {f g : ℕ → ℂ} (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1)
    {Y Z : ℝ} (hYZ : Y ≤ Z) :
    𝔻 f g Z ≤ Real.sqrt (𝔻 f g Y ^ 2 +
      2 * ((∑ p ∈ (⌊Z⌋₊).primesLE, (1 : ℝ) / p) - (∑ p ∈ (⌊Y⌋₊).primesLE, (1 : ℝ) / p))) := by
  have hmn : ⌊Y⌋₊ ≤ ⌊Z⌋₊ := Nat.floor_mono hYZ
  have hZ : 𝔻 f g Z
      = Real.sqrt (∑ p ∈ (⌊Z⌋₊).primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ)) := by
    rw [BoundedMultiplicativeFunctions.𝔻, ← Real.sqrt_eq_rpow]
  have hY : 𝔻 f g Y
      = Real.sqrt (∑ p ∈ (⌊Y⌋₊).primesLE, (1 - (f p * conj (g p)).re) / (p : ℝ)) := by
    rw [BoundedMultiplicativeFunctions.𝔻, ← Real.sqrt_eq_rpow]
  rw [hZ, hY, Real.sq_sqrt (D_sum_nonneg hf hg ⌊Y⌋₊)]
  exact Real.sqrt_le_sqrt (D_sum_sdiff_le hf hg hmn)

end Work.BMF.N1

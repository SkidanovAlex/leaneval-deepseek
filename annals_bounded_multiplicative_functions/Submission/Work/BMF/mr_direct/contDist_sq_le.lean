import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.liouville.dist_algebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Monotonicity of the squared pretentious distance under enlarging the truncation

For `1`-bounded `f g : ℕ → ℂ` and `x ≤ X`,

`𝔻(f,g;X)² ≤ 𝔻(f,g;x)² + 2 ∑_{x < p ≤ X} 1/p`,

i.e. enlarging the truncation point of the pretentious distance costs at most the
logarithmic mass of the intervening primes.  This is the standard continuity / scale
down estimate for `𝔻`.
-/

namespace Work.BMF.mr_direct

open BoundedMultiplicativeFunctions
open scoped ComplexConjugate

theorem contDist_sq_le (f g : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    {x X : ℝ} (hxX : x ≤ X) :
    BoundedMultiplicativeFunctions.𝔻 f g X ^ 2
      ≤ BoundedMultiplicativeFunctions.𝔻 f g x ^ 2
        + 2 * ∑ p ∈ (Nat.primesLE ⌊X⌋₊ \ Nat.primesLE ⌊x⌋₊), (1 : ℝ) / p := by
  -- the inner prime set is contained in the outer one
  have hsub : Nat.primesLE ⌊x⌋₊ ⊆ Nat.primesLE ⌊X⌋₊ :=
    Nat.primesLE_mono (Nat.floor_mono hxX)
  -- pointwise bound for the summands of the difference of the two prime sets
  have key : ∀ p ∈ Nat.primesLE ⌊X⌋₊ \ Nat.primesLE ⌊x⌋₊,
      (1 - (f p * conj (g p)).re) / (p : ℝ) ≤ 2 * ((1 : ℝ) / p) := by
    intro p hp
    have hpA : p ∈ Nat.primesLE ⌊X⌋₊ := (Finset.mem_sdiff.mp hp).1
    have hpprime : p.Prime := Nat.prime_of_mem_primesLE hpA
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.two_le
    have hppos : (0 : ℝ) < (p : ℝ) := by linarith
    have hnorm : ‖f p * conj (g p)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_conj]
      nlinarith [norm_nonneg (f p), norm_nonneg (g p), hf p, hg p]
    have hre : -1 ≤ (f p * conj (g p)).re := by
      have h := Complex.re_le_norm (-(f p * conj (g p)))
      rw [Complex.neg_re, norm_neg] at h
      linarith
    calc (1 - (f p * conj (g p)).re) / (p : ℝ)
        ≤ 2 / (p : ℝ) := div_le_div_of_nonneg_right (by linarith) (le_of_lt hppos)
      _ = 2 * ((1 : ℝ) / p) := by ring
  -- the two squared identities for the pretentious distance
  rw [Work.BMF.liouville.dist_algebra.1 f g X hf hg,
      Work.BMF.liouville.dist_algebra.1 f g x hf hg]
  -- split the outer prime sum into the inner one plus the difference
  calc ∑ p ∈ Nat.primesLE ⌊X⌋₊, (1 - (f p * conj (g p)).re) / (p : ℝ)
      = ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (f p * conj (g p)).re) / (p : ℝ)
        + ∑ p ∈ Nat.primesLE ⌊X⌋₊ \ Nat.primesLE ⌊x⌋₊,
            (1 - (f p * conj (g p)).re) / (p : ℝ) := by
        rw [← Finset.sum_sdiff hsub, add_comm]
    _ ≤ ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (f p * conj (g p)).re) / (p : ℝ)
        + ∑ p ∈ Nat.primesLE ⌊X⌋₊ \ Nat.primesLE ⌊x⌋₊, 2 * ((1 : ℝ) / p) :=
        add_le_add (le_refl _) (Finset.sum_le_sum key)
    _ = ∑ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (f p * conj (g p)).re) / (p : ℝ)
        + 2 * ∑ p ∈ Nat.primesLE ⌊X⌋₊ \ Nat.primesLE ⌊x⌋₊, (1 : ℝ) / p := by
        rw [Finset.mul_sum]

end Work.BMF.mr_direct

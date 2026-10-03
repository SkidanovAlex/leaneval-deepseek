import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.NumberTheory.PrimeCounting

open scoped _root_.ArithmeticFunction.zeta

namespace Commons.NumberTheory.ArithmeticFunction

theorem sum_divisors_prod_primes (f : ℕ → ℝ)
    (hmul : ∀ m n : ℕ, Nat.Coprime m n → f (m * n) = f m * f n) (h1 : f 1 = 1) (z : ℕ) :
    (∑ n ∈ Nat.divisors (∏ p ∈ Nat.primesBelow z, p), f n)
      = ∏ p ∈ Nat.primesBelow z, (1 + f p) := by
  classical
  -- Extend `f` to an arithmetic function (which must vanish at `0`).
  let F : _root_.ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else f n, by simp⟩
  have hFpos : ∀ n, n ≠ 0 → F n = f n := by
    intro n hn
    change (if n = 0 then 0 else f n) = f n
    rw [if_neg hn]
  have hF1 : F 1 = 1 := by
    rw [hFpos 1 (by norm_num), h1]
  -- `F` is multiplicative.
  have hFmul : F.IsMultiplicative := by
    rw [_root_.ArithmeticFunction.IsMultiplicative.iff_ne_zero]
    refine ⟨hF1, ?_⟩
    intro m n hm hn hmn
    rw [hFpos (m * n) (Nat.mul_ne_zero hm hn), hFpos m hm, hFpos n hn]
    exact hmul m n hmn
  -- Hence the Dirichlet convolution `ζ * F` is multiplicative.
  have hGmult : ((_root_.ArithmeticFunction.zeta : _root_.ArithmeticFunction ℝ) * F).IsMultiplicative :=
    _root_.ArithmeticFunction.IsMultiplicative.mul
      (_root_.ArithmeticFunction.IsMultiplicative.natCast
        (f := _root_.ArithmeticFunction.zeta) _root_.ArithmeticFunction.isMultiplicative_zeta) hFmul
  -- Evaluate it on the product of the primes below `z`.
  have hkey := hGmult.map_prod_of_prime (Nat.primesBelow z)
    (fun p hp => Nat.prime_of_mem_primesBelow hp)
  -- Its value there is exactly the divisor sum.
  have hLHS : (∑ n ∈ Nat.divisors (∏ p ∈ Nat.primesBelow z, p), f n)
      = ((_root_.ArithmeticFunction.zeta : _root_.ArithmeticFunction ℝ) * F)
          (∏ p ∈ Nat.primesBelow z, p) := by
    rw [_root_.ArithmeticFunction.coe_zeta_mul_apply]
    refine Finset.sum_congr rfl fun n hn => ?_
    exact (hFpos n (Nat.pos_of_mem_divisors hn).ne').symm
  rw [hLHS, hkey]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp := Nat.prime_of_mem_primesBelow hp
  rw [_root_.ArithmeticFunction.coe_zeta_mul_apply, hpp.divisors]
  rw [Finset.sum_insert (by rw [Finset.mem_singleton]; exact fun h => hpp.ne_one h.symm)]
  simp [hF1, hFpos p hpp.ne_zero]

end Commons.NumberTheory.ArithmeticFunction
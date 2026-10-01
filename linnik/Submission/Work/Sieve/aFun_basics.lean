import Mathlib
import Submission.Work.LinnikAreas.Sieve.Defs

/-!
# Basic properties of Graham's function `a(n) = Σ_{d | n} χ₁(d)`

For a real character `χ₁` (`χ₁ ^ 2 = 1`, so `χ₁` takes only the values `0, ±1`) the function
`aFun χ₁ n = Σ_{d | n} χ₁(d)` is multiplicative on coprime arguments, non-negative everywhere, and
on a prime power `p ^ k` it is the geometric sum `1 + χ₁(p) + … + χ₁(p)^k`.

The proof is elementary: `χ₁` real makes `n ↦ (χ₁ n).re` a completely multiplicative real-valued
function on `ℕ`; `aFun` is its Dirichlet convolution with the constant-`1` function, hence
multiplicative, and evaluating on prime powers gives a geometric sum of ratio in `{0, ±1}`.
-/

open scoped BigOperators
open DirichletCharacter

namespace Work.Sieve

variable {q : ℕ}

/-- For a real character every value `χ₁ x` is a real number (`0`, `1` or `-1`). -/
private lemma aFun_im_eq_zero (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1) (x : ZMod q) :
    (χ₁ x).im = 0 := by
  have hq := (MulChar.isQuadratic_iff_sq_eq_one).mpr hreal
  rcases hq x with h | h | h <;> simp [h]

/-- On a real character, `re` is multiplicative. -/
private lemma aFun_re_mul (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1) (x y : ZMod q) :
    (χ₁ (x * y)).re = (χ₁ x).re * (χ₁ y).re := by
  have hq := (MulChar.isQuadratic_iff_sq_eq_one).mpr hreal
  rw [map_mul]
  rcases hq x with h | h | h <;> rcases hq y with h' | h' | h' <;> simp [h, h']

/-- On a real character, `re` commutes with powers. -/
private lemma aFun_pow_re (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1) (x : ZMod q) (j : ℕ) :
    (χ₁ (x ^ j)).re = ((χ₁ x).re) ^ j := by
  have hq := (MulChar.isQuadratic_iff_sq_eq_one).mpr hreal
  have hz : (χ₁ x).im = 0 := by rcases hq x with h | h | h <;> simp [h]
  have hx : χ₁ x = ((χ₁ x).re : ℂ) := by apply Complex.ext <;> simp [hz]
  rw [map_pow]
  conv_lhs => rw [hx]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- `aFun χ₁ 1 = 1`. -/
private lemma aFun_one (χ₁ : DirichletCharacter ℂ q) :
    Work.LinnikAreas.Sieve.aFun χ₁ 1 = 1 := by
  simp [Work.LinnikAreas.Sieve.aFun]

/-- **Prime power formula**: `a(p^k) = Σ_{j = 0}^{k} χ₁(p^j)`. -/
private lemma aFun_primePow (χ₁ : DirichletCharacter ℂ q) (p k : ℕ) (hp : p.Prime) :
    Work.LinnikAreas.Sieve.aFun χ₁ (p ^ k)
      = ∑ j ∈ Finset.range (k + 1), (χ₁ ((p : ℕ) ^ j : ZMod q)).re := by
  unfold Work.LinnikAreas.Sieve.aFun
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, Nat.cast_pow]

/-- **Multiplicativity of `aFun`** for a real character. -/
private lemma aFun_mul (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1) (m n : ℕ)
    (hmn : Nat.Coprime m n) :
    Work.LinnikAreas.Sieve.aFun χ₁ (m * n)
      = Work.LinnikAreas.Sieve.aFun χ₁ m * Work.LinnikAreas.Sieve.aFun χ₁ n := by
  have bn : ∀ a c : ℕ, (χ₁ ((a * c : ℕ) : ZMod q)).re
      = (χ₁ (a : ZMod q)).re * (χ₁ (c : ZMod q)).re := by
    intro a c; rw [Nat.cast_mul]; exact aFun_re_mul χ₁ hreal _ _
  unfold Work.LinnikAreas.Sieve.aFun
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image hmn.mul_injOn_divisors,
    Finset.sum_product]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => bn x y))]
  rw [Finset.sum_mul_sum]

/-- Non-negativity of a geometric sum whose ratio lies in `{0, 1, -1}`. -/
private lemma sum_pow_nonneg (k : ℕ) {r : ℝ} (hr : r = 0 ∨ r = 1 ∨ r = -1) :
    0 ≤ ∑ j ∈ Finset.range (k + 1), r ^ j := by
  rcases hr with h | h | h <;> rw [h]
  · rw [Finset.sum_range_succ']; simp
  · simp; positivity
  · have h2 : (2 : ℝ) * (∑ j ∈ Finset.range (k + 1), (-1 : ℝ) ^ j) = 1 + (-1 : ℝ) ^ k := by
      have h := geom_sum_mul (-1 : ℝ) (k + 1)
      rw [show ((-1 : ℝ) - 1) = -2 by ring, pow_succ] at h
      rcases neg_one_pow_eq_or (R := ℝ) k with hk | hk <;> rw [hk] at h <;> linarith
    rcases neg_one_pow_eq_or (R := ℝ) k with hk | hk <;> rw [hk] at h2 <;> linarith

/-- **Non-negativity of `a` on prime powers** for a real character. -/
private lemma aFun_primePow_nonneg (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1)
    (p k : ℕ) (hp : p.Prime) :
    0 ≤ Work.LinnikAreas.Sieve.aFun χ₁ (p ^ k) := by
  rw [aFun_primePow χ₁ p k hp]
  have hq := (MulChar.isQuadratic_iff_sq_eq_one).mpr hreal
  have hr : (χ₁ (p : ZMod q)).re = 0 ∨ (χ₁ (p : ZMod q)).re = 1
      ∨ (χ₁ (p : ZMod q)).re = -1 := by
    rcases hq (p : ZMod q) with h | h | h
    · left; rw [h]; simp
    · right; left; rw [h]; simp
    · right; right; rw [h]; simp
  have hsum : (∑ j ∈ Finset.range (k + 1), (χ₁ ((p : ℕ) ^ j : ZMod q)).re)
      = ∑ j ∈ Finset.range (k + 1), ((χ₁ (p : ZMod q)).re) ^ j :=
    Finset.sum_congr rfl (fun j _ => aFun_pow_re χ₁ hreal _ j)
  rw [hsum]
  exact sum_pow_nonneg k hr

/-- Multiplicativity of `aFun` over a finite pairwise-coprime family. -/
private lemma aFun_prod_of_pairwise (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1)
    (s : Finset ℕ) (g : ℕ → ℕ)
    (hcop : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → (g a).Coprime (g b)) :
    Work.LinnikAreas.Sieve.aFun χ₁ (∏ i ∈ s, g i)
      = ∏ i ∈ s, Work.LinnikAreas.Sieve.aFun χ₁ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [aFun_one]
  | insert a s has ih =>
    rw [Finset.prod_insert has, Finset.prod_insert has]
    have hca : (g a).Coprime (∏ i ∈ s, g i) :=
      Nat.Coprime.prod_right (fun i hi =>
        hcop a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
          (by rintro rfl; exact has hi))
    rw [aFun_mul χ₁ hreal (g a) (∏ i ∈ s, g i) hca]
    rw [ih (fun x hx y hy hxy =>
      hcop x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy)]

/-- **`a` is determined by its prime-power values** for a real character. -/
private lemma aFun_prod_primeFactors (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1)
    (n : ℕ) (hn : n ≠ 0) :
    Work.LinnikAreas.Sieve.aFun χ₁ n
      = ∏ p ∈ n.primeFactors, Work.LinnikAreas.Sieve.aFun χ₁ (p ^ n.factorization p) := by
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
  exact aFun_prod_of_pairwise χ₁ hreal n.primeFactors (fun p => p ^ n.factorization p)
    (fun a ha b hb hab =>
      Nat.Coprime.pow (n.factorization a) (n.factorization b)
        ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors ha)
          (Nat.prime_of_mem_primeFactors hb)).mpr hab))

/-- **Basic properties of Graham's function `a(n) = Σ_{d | n} χ₁(d)`.**

For a real character `χ₁` (`χ₁² = 1`), `a` is multiplicative and non-negative, and on prime powers
it is the geometric sum `a(p^k) = 1 + χ₁(p) + … + χ₁(p)^k`.  (Multiplicativity: `a = 1 ∗ χ₁` is a
Dirichlet convolution with a completely multiplicative real-valued character, via the divisor-pair
bijection.  Non-negativity then follows from the prime-power formula: the value is `k+1` when
`χ₁(p) = 1`, `0` or `1` when `χ₁(p) = -1`, and `1` when `χ₁(p) = 0`.)

Used by every step of the Selberg-sieve chapter (the monotonicity step in BGTZ Lemma 3.4, the
non-negativity `S(x) ≥ 1 - 1/x` in Lemma 2.8, and `a(n)χ(n) ≪ n^ε`). -/
theorem aFun_basics {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1) :
    (∀ m n : ℕ, Nat.Coprime m n →
        Work.LinnikAreas.Sieve.aFun χ₁ (m * n)
          = Work.LinnikAreas.Sieve.aFun χ₁ m * Work.LinnikAreas.Sieve.aFun χ₁ n) ∧
      (∀ n : ℕ, 0 ≤ Work.LinnikAreas.Sieve.aFun χ₁ n) ∧
      (∀ (p k : ℕ), p.Prime →
        Work.LinnikAreas.Sieve.aFun χ₁ (p ^ k)
          = ∑ j ∈ Finset.range (k + 1), (χ₁ ((p : ℕ) ^ j : ZMod q)).re) := by
  refine ⟨fun m n hmn => aFun_mul χ₁ hreal m n hmn, ?_, fun p k hp => aFun_primePow χ₁ p k hp⟩
  intro n
  rcases n with _ | m
  · simp [Work.LinnikAreas.Sieve.aFun]
  · rw [aFun_prod_primeFactors χ₁ hreal (m + 1) (Nat.succ_ne_zero m)]
    exact Finset.prod_nonneg (fun p hp =>
      aFun_primePow_nonneg χ₁ hreal p ((m + 1).factorization p)
        (Nat.prime_of_mem_primeFactors hp))

end Work.Sieve

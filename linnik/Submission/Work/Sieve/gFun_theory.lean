import Mathlib
import Submission.Work.LinnikAreas.Sieve.Defs
import Submission.Work.LinnikAreas.charValTri
import Submission.Work.Sieve.summable_div_prime_pow
import Submission.Work.Sieve.aFun_basics
import Submission.Work.Sieve.aFun_nonneg_le_card
import Submission.Work.Sieve.hFun_squarefree

/-!
# Theory of Graham's local sieve factors `g`, `h` and the sum `V`

Fix a real Dirichlet character `χ₁` mod `q` (`χ₁ ^ 2 = 1`), so that `χ₁` takes only the values
`0, ±1` (`Work.LinnikAreas.charValTri`).  With

* `aFun χ₁ n = Σ_{d | n} χ₁(d)`,
* `gPrime χ₁ p = (Σ_{k ≥ 1} aFun χ₁ (p^k) p^{-k})^{-1}`,
* `hPrime χ₁ p = gPrime χ₁ p + 1`, `hFun`, `gFun` their multiplicative extensions,
* `VFun χ₁ R = Σ_{ℓ ≤ R} μ²(ℓ)/gFun χ₁ ℓ`,

this file collects the elementary facts used by the Selberg sieve of Graham's proof of the
Deuring–Heilbronn phenomenon:

* every value of `χ₁` is `0, 1` or `-1`;
* `gPrime χ₁ p > 0` for every prime `p`;
* on a squarefree `n`, `hFun χ₁ n = ∏_{p | n} hPrime χ₁ p` and
  `gFun χ₁ n = ∏_{p | n} gPrime χ₁ p`;
* hence `gFun χ₁ n > 0` for squarefree `n` and `gFun` is multiplicative on coprime squarefree
  arguments;
* `VFun χ₁ R > 0` for `R ≥ 1`.
-/

namespace Work.Sieve
open Work.LinnikAreas.Sieve
open scoped BigOperators

/-- On a prime power `p ^ 2` the divisor sum `aFun χ₁ (p^2) = 1 + χ₁(p) + χ₁(p)^2 ≥ 1` for a real
character `χ₁` (the middle term can be `-1`, but then the last one is `+1`). -/
private theorem aFun_prime_sq_ge_one {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q)
    (hreal : χ₁ ^ 2 = 1) (p : ℕ) (hp : p.Prime) :
    1 ≤ Work.LinnikAreas.Sieve.aFun χ₁ (p ^ 2) := by
  have hb := Work.Sieve.aFun_basics χ₁ hreal
  rw [hb.2.2 p 2 hp]
  have hv := (Work.LinnikAreas.charValTri χ₁ hreal (p : ZMod q)).1
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [map_pow, zero_add]
  rcases hv with h | h | h <;> rw [h] <;> norm_num

/-- Positivity of the local sieve factor `gPrime χ₁ p` for a prime `p`.

`gPrime χ₁ p = (Σ_{k≥1} aFun χ₁ (p^k) p^{-k})^{-1}`, and the series is a sum of non-negative terms
(`aFun ≥ 0`, since `χ₁` is real) whose term at `k = 2` is `aFun χ₁ (p^2)/p^2 ≥ 1/p^2 > 0`; it
converges because `aFun χ₁ (p^k) ≤ k+1` (the number of divisors of `p^k`). -/
private theorem gPrime_pos {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1)
    (p : ℕ) (hp : p.Prime) : 0 < Work.LinnikAreas.Sieve.gPrime χ₁ p := by
  unfold Work.LinnikAreas.Sieve.gPrime
  rw [inv_pos]
  have hcard : ∀ k : ℕ, ((p ^ (k + 1)).divisors.card : ℝ) = (k : ℝ) + 2 := by
    intro k
    rw [Nat.divisors_prime_pow hp (k + 1), Finset.card_map, Finset.card_range]
    push_cast; ring
  have hsum : Summable
      (fun k : ℕ => Work.LinnikAreas.Sieve.aFun χ₁ (p ^ (k + 1)) / (p : ℝ) ^ (k + 1)) :=
    Summable.of_nonneg_of_le
      (fun k => div_nonneg (aFun_nonneg_le_card χ₁ hreal _).1 (by positivity))
      (fun k => by
        apply div_le_div_of_nonneg_right _ (by positivity)
        calc Work.LinnikAreas.Sieve.aFun χ₁ (p ^ (k + 1))
              ≤ ((p ^ (k + 1)).divisors.card : ℝ) := (aFun_nonneg_le_card χ₁ hreal _).2
          _ = (k : ℝ) + 2 := hcard k)
      (summable_div_prime_pow p hp)
  have hnonneg : ∀ k, 0 ≤ Work.LinnikAreas.Sieve.aFun χ₁ (p ^ (k + 1)) / (p : ℝ) ^ (k + 1) :=
    fun k => div_nonneg (aFun_nonneg_le_card χ₁ hreal _).1 (by positivity)
  have hpos1 : 0 < Work.LinnikAreas.Sieve.aFun χ₁ (p ^ ((1 : ℕ) + 1)) / (p : ℝ) ^ ((1 : ℕ) + 1) := by
    have hsq := aFun_prime_sq_ge_one χ₁ hreal p hp
    have h2 : ((1 : ℕ) + 1) = 2 := rfl
    rw [h2]
    exact div_pos (lt_of_lt_of_le zero_lt_one hsq)
      (pow_pos (by exact_mod_cast hp.pos) 2)
  exact Summable.tsum_pos hsum hnonneg 1 hpos1

/-- On a squarefree `n`, the local factor `gFun χ₁ n` is the product of the `gPrime χ₁ p`. -/
private theorem gFun_sqfree {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1)
    (n : ℕ) (hn : Squarefree n) :
    Work.LinnikAreas.Sieve.gFun χ₁ n
      = ∏ p ∈ n.primeFactors, Work.LinnikAreas.Sieve.gPrime χ₁ p := by
  unfold Work.LinnikAreas.Sieve.gFun
  rw [hFun_squarefree χ₁ n hn]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun p hp => ?_)
  have hp' : p.Prime := (Nat.mem_primeFactors.mp hp).1
  have hne : Work.LinnikAreas.Sieve.hPrime χ₁ p ≠ 0 := by
    have := gPrime_pos χ₁ hreal p hp'
    unfold Work.LinnikAreas.Sieve.hPrime
    positivity
  unfold Work.LinnikAreas.Sieve.hPrime at hne ⊢
  rw [mul_sub, mul_one, mul_inv_cancel₀ hne]
  ring

private theorem gFun_pos {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1)
    (n : ℕ) (hn : Squarefree n) : 0 < Work.LinnikAreas.Sieve.gFun χ₁ n := by
  rw [gFun_sqfree χ₁ hreal n hn]
  exact Finset.prod_pos (fun p hp => gPrime_pos χ₁ hreal p (Nat.mem_primeFactors.mp hp).1)

private theorem gFun_mul {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1)
    (m n : ℕ) (hm : Squarefree m) (hn : Squarefree n) (hcop : Nat.Coprime m n) :
    Work.LinnikAreas.Sieve.gFun χ₁ (m * n)
      = Work.LinnikAreas.Sieve.gFun χ₁ m * Work.LinnikAreas.Sieve.gFun χ₁ n := by
  have hmul : Squarefree (m * n) := (Nat.squarefree_mul hcop).mpr ⟨hm, hn⟩
  rw [gFun_sqfree χ₁ hreal (m * n) hmul, gFun_sqfree χ₁ hreal m hm,
      gFun_sqfree χ₁ hreal n hn, Nat.Coprime.primeFactors_mul hcop]
  exact Finset.prod_union hcop.disjoint_primeFactors

private theorem VFun_pos {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1)
    (R : ℕ) (hR : 1 ≤ R) : 0 < Work.LinnikAreas.Sieve.VFun χ₁ R := by
  unfold Work.LinnikAreas.Sieve.VFun
  apply Finset.sum_pos'
  · intro ℓ hℓ
    by_cases hsq : Squarefree ℓ
    · rw [if_pos hsq]
      exact div_nonneg zero_le_one (le_of_lt (gFun_pos χ₁ hreal ℓ hsq))
    · rw [if_neg hsq]; simp
  · refine ⟨1, ?_, ?_⟩
    · rw [Finset.mem_Icc]; exact ⟨le_refl 1, hR⟩
    · rw [if_pos squarefree_one]
      exact div_pos zero_lt_one (gFun_pos χ₁ hreal 1 squarefree_one)

theorem gFun_theory {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (hreal : χ₁ ^ 2 = 1) :
    (∀ x : ZMod q, χ₁ x = 0 ∨ χ₁ x = 1 ∨ χ₁ x = -1) ∧
    (∀ p : ℕ, p.Prime → 0 < Work.LinnikAreas.Sieve.gPrime χ₁ p) ∧
    (∀ n : ℕ, Squarefree n →
      Work.LinnikAreas.Sieve.hFun χ₁ n
        = ∏ p ∈ n.primeFactors, Work.LinnikAreas.Sieve.hPrime χ₁ p) ∧
    (∀ n : ℕ, Squarefree n →
      Work.LinnikAreas.Sieve.gFun χ₁ n
        = ∏ p ∈ n.primeFactors, Work.LinnikAreas.Sieve.gPrime χ₁ p) ∧
    (∀ n : ℕ, Squarefree n → 0 < Work.LinnikAreas.Sieve.gFun χ₁ n) ∧
    (∀ m n : ℕ, Squarefree m → Squarefree n → Nat.Coprime m n →
      Work.LinnikAreas.Sieve.gFun χ₁ (m * n)
        = Work.LinnikAreas.Sieve.gFun χ₁ m * Work.LinnikAreas.Sieve.gFun χ₁ n) ∧
    (∀ R : ℕ, 1 ≤ R → 0 < Work.LinnikAreas.Sieve.VFun χ₁ R) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; exact (Work.LinnikAreas.charValTri χ₁ hreal x).1
  · intro p hp; exact gPrime_pos χ₁ hreal p hp
  · intro n hn; exact hFun_squarefree χ₁ n hn
  · intro n hn; exact gFun_sqfree χ₁ hreal n hn
  · intro n hn; exact gFun_pos χ₁ hreal n hn
  · intro m n hm hn hcop; exact gFun_mul χ₁ hreal m n hm hn hcop
  · intro R hR; exact VFun_pos χ₁ hreal R hR

end Work.Sieve

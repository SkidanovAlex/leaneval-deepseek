import Mathlib
import Submission.Work.ChenPlan.LinearSieve.RI.basic
import Submission.Work.ChenPlan.LinearSieve.RI.lamMinus_sieve_lower

/-!
# The Rosser–Iwaniec `λ⁺` weight is upper Möbius

`Work.ChenPlan.LinearSieve.RI.upper_moebius`:
for every `P : ℕ` and every level `D : ℝ`, the Rosser–Iwaniec upper weight
`lamPlus P D` is a **majorant of the Möbius function**, in the sense of
`BoundingSieve.IsUpperMoebius`:

`∀ n, [n = 1] ≤ Σ_{d ∣ n} λ⁺(d)`.

## The mathematics

Write `Wp n D = Σ_{d ∣ n, rdPlus D d} μ(d)` for the Möbius sum over the upper-admissible
divisors.  The sibling file `RI.lamMinus_sieve_lower` establishes the pair of bounds
`Wm n D ≤ [n = 1]` and `[n = 1] ≤ Wp n D` for every *squarefree* `n` and `D ≥ 0`
(`Wm_Wp_bounds`).  The weight `lamPlus P D` differs from the indicator `rdPlus` by the extra
restriction `d ∣ P`, so the sum over `d ∣ n` is really a sum over the divisors of
`g = gcd n P`.  Since only squarefree `d` contribute (`μ d = 0` otherwise), that sum is the sum
over the divisors of the **squarefree kernel** `∏_{p ∣ g} p` of `g`, and the bound for squarefree
moduli applies.

For `D < 0` the admissibility condition can only hold for `d = 1` (a prime divisor `p` of any
`d ≥ 2` would force `p³ ≤ D < 0`), so the sum is `1`.
-/

namespace Work.ChenPlan.LinearSieve.RI

open Finset
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open Classical

attribute [local instance] Classical.propDecidable

/-! ## The squarefree kernel -/

/-- The **squarefree kernel** `∏_{p ∣ n} p` of `n`: the largest squarefree divisor of `n`. -/
def sqKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma sqKernel_ne_zero {n : ℕ} (hn : n ≠ 0) : sqKernel n ≠ 0 := by
  rw [sqKernel, Finset.prod_ne_zero_iff]
  intro p hp
  exact (Nat.mem_primeFactors.mp hp).1.ne_zero

lemma squarefree_sqKernel (n : ℕ) : Squarefree (sqKernel n) :=
  squarefree_prod_primes (fun p hp => (Nat.mem_primeFactors.mp hp).1)

lemma sqKernel_dvd (n : ℕ) : sqKernel n ∣ n := Nat.prod_primeFactors_dvd n

lemma sqKernel_one : sqKernel 1 = 1 := by simp [sqKernel]

/-- A squarefree divisor of `n` divides the squarefree kernel of `n`. -/
lemma dvd_sqKernel_of_squarefree_dvd {d n : ℕ} (hn : n ≠ 0) (hsq : Squarefree d) (h : d ∣ n) :
    d ∣ sqKernel n := by
  rw [sqKernel, ← Nat.prod_primeFactors_of_squarefree hsq]
  exact Finset.prod_dvd_prod_of_subset d.primeFactors n.primeFactors (fun p => p)
    (Nat.primeFactors_mono h hn)

/-! ## The main theorem -/

theorem upper_moebius (P : ℕ) (D : ℝ) :
    BoundingSieve.IsUpperMoebius (lamPlus P D) := by
  intro n
  rcases eq_or_ne n 0 with h0 | hn0
  · subst h0
    rw [Nat.divisors_zero, Finset.sum_empty]
    norm_num
  rcases lt_or_ge D 0 with hDneg | hD
  · -- `D < 0`: only `d = 1` is admissible
    have h1mem : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n, hn0⟩
    have hrd1 : rdPlus D 1 := by
      rw [rdPlus]
      intro e he hodd
      exact absurd hodd (by rw [Nat.dvd_one.mp (Nat.mem_divisors.mp he).1]; simp)
    have hterm : ∀ d ∈ n.divisors, lamPlus P D d = if d = 1 then (1 : ℝ) else 0 := by
      intro d hd
      rcases eq_or_ne d 1 with hd1 | hd1
      · subst hd1
        rw [lamPlus, if_pos ⟨one_dvd P, hrd1⟩, ArithmeticFunction.moebius_apply_one]
        norm_num
      · rw [if_neg hd1, lamPlus, if_neg]
        rintro ⟨-, hr⟩
        have hd0 : d ≠ 0 := div_ne_zero_of_dvd (Nat.mem_divisors.mp hd).1 hn0
        have hp : (d.minFac).Prime := Nat.minFac_prime hd1
        have hmem : d.minFac ∈ d.divisors := Nat.mem_divisors.mpr ⟨Nat.minFac_dvd d, hd0⟩
        have hodd : Odd (d.minFac).primeFactors.card := by
          rw [hp.primeFactors, Finset.card_singleton]; exact odd_one
        have hle := hr d.minFac hmem hodd
        rw [hp.minFac_eq] at hle
        have h2 : (2 : ℝ) ≤ (d.minFac : ℝ) := by exact_mod_cast hp.two_le
        have hcube : (d.minFac : ℝ) ^ 3 ≤ D := by
          calc (d.minFac : ℝ) ^ 3 = (d.minFac : ℝ) * (d.minFac : ℝ) ^ 2 := by ring
            _ ≤ D := hle
        have h8 : (2 : ℝ) ^ 3 ≤ (d.minFac : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
        linarith
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' n.divisors 1 (fun _ => (1 : ℝ)),
      if_pos h1mem]
    split <;> norm_num
  · -- `D ≥ 0`: reduce to the squarefree kernel of `gcd n P`
    have hg0 : Nat.gcd n P ≠ 0 := fun h => hn0 (Nat.gcd_eq_zero_iff.mp h).1
    have hfilt : n.divisors.filter (fun d => d ∣ P) = (Nat.gcd n P).divisors := by
      ext d
      rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdn, -⟩, hdP⟩
        exact ⟨Nat.dvd_gcd hdn hdP, hg0⟩
      · rintro ⟨hd, -⟩
        exact ⟨⟨dvd_trans hd (Nat.gcd_dvd_left n P), hn0⟩,
          dvd_trans hd (Nat.gcd_dvd_right n P)⟩
    have hstep1 : ∑ d ∈ n.divisors, lamPlus P D d
        = ∑ d ∈ (Nat.gcd n P).divisors,
            (if rdPlus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) := by
      have h1 : ∑ d ∈ n.divisors, lamPlus P D d
          = ∑ d ∈ n.divisors, (if d ∣ P then
              (if rdPlus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) else 0) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [lamPlus]
        by_cases hP : d ∣ P <;> by_cases hr : rdPlus D d <;> simp [hP, hr]
      rw [h1, ← Finset.sum_filter, hfilt]
    have hk0 : sqKernel (Nat.gcd n P) ≠ 0 := sqKernel_ne_zero hg0
    have hsub : (sqKernel (Nat.gcd n P)).divisors ⊆ (Nat.gcd n P).divisors := by
      intro d hd
      exact Nat.mem_divisors.mpr
        ⟨dvd_trans (Nat.mem_divisors.mp hd).1 (sqKernel_dvd _), hg0⟩
    have hzero : ∀ d ∈ (Nat.gcd n P).divisors, d ∉ (sqKernel (Nat.gcd n P)).divisors →
        (if rdPlus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) = 0 := by
      intro d hd hnot
      have hnsq : ¬ Squarefree d := fun hsq =>
        hnot (Nat.mem_divisors.mpr
          ⟨dvd_sqKernel_of_squarefree_dvd hg0 hsq (Nat.mem_divisors.mp hd).1, hk0⟩)
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hnsq]
      split <;> norm_num
    have hbound := (Wm_Wp_bounds (sqKernel (Nat.gcd n P)) (squarefree_sqKernel _)).2 D hD
    have hkn : (if n = 1 then (1 : ℝ) else 0)
        ≤ (if sqKernel (Nat.gcd n P) = 1 then (1 : ℝ) else 0) := by
      by_cases hn1 : n = 1
      · subst hn1
        rw [if_pos rfl, if_pos (by rw [Nat.gcd_one_left, sqKernel_one])]
      · rw [if_neg hn1]
        split <;> norm_num
    calc (if n = 1 then (1 : ℝ) else 0)
        ≤ (if sqKernel (Nat.gcd n P) = 1 then (1 : ℝ) else 0) := hkn
      _ ≤ Wp (sqKernel (Nat.gcd n P)) D := hbound
      _ = ∑ d ∈ (Nat.gcd n P).divisors,
            (if rdPlus D d then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) :=
          Finset.sum_subset hsub hzero
      _ = ∑ d ∈ n.divisors, lamPlus P D d := hstep1.symm

end

end Work.ChenPlan.LinearSieve.RI

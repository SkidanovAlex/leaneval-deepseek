/-
  Companion paper, §9: the Euler-product tools for the identity (9.9)

      `g̃(d)·G = ∑'_ν μ(ν)·g([ν²,d])`,      (9.9)

  where `d` is squarefree, `g` is multiplicative with `g 1 = 1`, `|g(p²)| ≤ C/p²`,
  `g̃(d) = ∏_{p|d} (g p − g(p²))/(1 − g(p²))` and `G = ∏'_p (1 − g(p²))`.

  This file contains the two product identities that the proof of (9.9) rests on:

  * `tsum_moebius_mul_coprime_eq_tprod` — the **coprime-restricted Euler product**
    `∑_{(ν,m)=1} μ(ν)f(ν) = ∏'_p (1 − [p ∣ m]·f p)` (from the common Euler product applied
    to the multiplicative function `ν ↦ f ν·[Coprime ν m]`);

  * `Gprod_eq_prod_filter_mul` — the **splitting of the Euler product at a finite set `S`**
    `∏'_p (1 − g(p²)) = (∏_{p ∈ S, p prime}(1 − g(p²))) · ∏'_p (1 − g(p²))^{[p ∉ S]}`.
-/
import Mathlib
import Submission.ASP.S9k
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Submission.Commons.NumberTheory.ArithmeticFunction.g_eq_prod_primeFactors
import Submission.Commons.Data.Nat.squarefree_prod_primes

set_option maxHeartbeats 800000

namespace Submission.ASP

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-! ### The coprime-restricted Möbius–Euler product -/

/-! ### Splitting the Euler product at a finite set of primes -/

/-- **Splitting the Euler product at a finite set of primes.**  For any finset `S` of naturals
and any `g` with `|g(p²)| ≤ C/p²` on primes,

    `∏'_p (1 − g(p²)) = (∏_{p ∈ S, p prime} (1 − g(p²))) · ∏'_p (1 − g(p²))^{[p ∉ S]}`. -/
theorem Gprod_eq_prod_filter_mul (g : ℕ → ℝ) (S : Finset ℕ) {C : ℝ} (hC : 0 < C)
    (hbd : ∀ p : ℕ, p.Prime → |g (p ^ 2)| ≤ C / (p : ℝ) ^ 2) :
    Gprod g
      = (∏ p ∈ S.filter Nat.Prime, (1 - g (p ^ 2)))
        * ∏' p : {p : ℕ // p.Prime}, (if (p : ℕ) ∈ S then 1 else 1 - g ((p : ℕ) ^ 2)) := by
  classical
  have hnorm : Summable (fun x : ℕ => ‖(if x.Prime then -g (x ^ 2) else 0 : ℝ)‖) := by
    have hbase : Summable (fun x : ℕ => C / (x : ℝ) ^ 2) := by
      have h := ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num : (1:ℕ) < 2)).mul_left C
      simpa [div_eq_mul_inv] using h
    refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) hbase
    by_cases hx : x.Prime
    · rw [if_pos hx, norm_neg, Real.norm_eq_abs]; exact hbd x hx
    · rw [if_neg hx, norm_zero]; positivity
  have hsum : Summable (fun x : ℕ => (if x.Prime then -g (x ^ 2) else 0 : ℝ)) := hnorm.of_norm
  have hS : Summable (fun x : ↑(S : Set ℕ) => ‖(if (x:ℕ).Prime then -g ((x:ℕ) ^ 2) else 0 : ℝ)‖) :=
    hnorm.subtype _
  have hSc : Summable (fun x : ↑(S : Set ℕ)ᶜ => ‖(if (x:ℕ).Prime then -g ((x:ℕ) ^ 2) else 0 : ℝ)‖) :=
    hnorm.subtype _
  have hmS : Multipliable (fun x : ↑(S : Set ℕ) =>
      (1 + (if (x:ℕ).Prime then -g ((x:ℕ) ^ 2) else 0 : ℝ))) :=
    multipliable_one_add_of_summable hS
  have hmSc : Multipliable (fun x : ↑(S : Set ℕ)ᶜ =>
      (1 + (if (x:ℕ).Prime then -g ((x:ℕ) ^ 2) else 0 : ℝ))) :=
    multipliable_one_add_of_summable hSc
  have hG : Gprod g = ∏' x : ℕ, (1 + (if x.Prime then -g (x ^ 2) else 0 : ℝ)) := by
    rw [Gprod]
    trans ∏' x : ℕ, Set.mulIndicator {x : ℕ | x.Prime} (fun x => 1 - g (x ^ 2)) x
    · exact tprod_subtype {x : ℕ | x.Prime} (fun x => 1 - g (x ^ 2))
    · refine tprod_congr fun x => ?_
      by_cases hx : x.Prime
      · rw [Set.mulIndicator_of_mem (by simpa using hx), if_pos hx]; ring
      · rw [Set.mulIndicator_of_notMem (by simpa using hx)]; simp [hx]
  rw [hG]
  have hsplit := Multipliable.tprod_mul_tprod_compl
    (f := fun x : ℕ => (1 + (if x.Prime then -g (x ^ 2) else 0 : ℝ))) hmS hmSc
  rw [← hsplit]
  congr 1
  · rw [tprod_fintype]
    rw [show (∏ x : ↑(S : Set ℕ), (1 + (if (x:ℕ).Prime then -g ((x:ℕ) ^ 2) else 0 : ℝ)))
        = ∏ x ∈ S, (1 + (if x.Prime then -g (x ^ 2) else 0 : ℝ)) from
      (Finset.prod_subtype (s := S) (p := fun x => x ∈ S) (fun x => Iff.rfl)
        (fun y => (1 + (if y.Prime then -g (y ^ 2) else 0 : ℝ)))).symm]
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun x hx => ?_
    by_cases hx' : x.Prime
    · rw [if_pos hx', if_pos hx']; ring
    · rw [if_neg hx', if_neg hx']; ring
  · change (∏' (x : ↑{x : ℕ | x ∉ S}), (1 + (if (x:ℕ).Prime then -g ((x:ℕ) ^ 2) else 0 : ℝ)))
      = ∏' p : {p : ℕ // p.Prime}, (if (p:ℕ) ∈ S then 1 else 1 - g ((p:ℕ) ^ 2))
    rw [tprod_subtype {x : ℕ | x ∉ S}
      (fun x => (1 + (if x.Prime then -g (x ^ 2) else 0 : ℝ)))]
    trans ∏' x : ℕ, Set.mulIndicator {x : ℕ | x.Prime}
        (fun x => (if x ∈ S then 1 else 1 - g (x ^ 2))) x
    · refine tprod_congr fun x => ?_
      by_cases hxS : x ∈ S <;> by_cases hx : x.Prime <;>
        simp_all only [Set.mulIndicator_apply, Set.mem_ofPred_eq, not_true_eq_false,
          not_false_eq_true, ↓reduceIte] <;> ring
    · exact (tprod_subtype {x : ℕ | x.Prime}
        (fun x => (if x ∈ S then 1 else 1 - g (x ^ 2)))).symm

end

end Submission.ASP

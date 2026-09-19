import Mathlib.Data.Nat.Choose.Multinomial
import Submission.Commons.Data.Nat.mul_div_gcd_eq_lcm

namespace Commons.Data.Nat

open Finset
open scoped BigOperators
open scoped _root_.Nat

/-- Product form: for `1 ≤ n q`, the full factorial product agrees with `n q` times the
factorial product of `n - e_q`. -/
lemma prod_factorial_eq_mul_prod_sub_single (n : Fin 12 → ℕ) (q : Fin 12) (hq : 1 ≤ n q) :
    ∏ i, (n i)! = n q * ∏ i, ((n - (Pi.single q (1:ℕ) : Fin 12 → ℕ)) i)! := by
  have hfac : (n q)! = n q * (n q - 1)! := by
    rw [← Nat.sub_add_cancel hq]
    exact Nat.factorial_succ (n q - 1)
  have hL : ∏ i, (n i)! = n q * ((n q - 1)! * ∏ i ∈ Finset.univ.erase q, (n i)!) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun i => (n i)!) (Finset.mem_univ q), hfac]
    ring
  have hR : ∏ i, ((n - (Pi.single q (1:ℕ) : Fin 12 → ℕ)) i)!
      = (n q - 1)! * ∏ i ∈ Finset.univ.erase q, (n i)! := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => ((n - (Pi.single q (1:ℕ) : Fin 12 → ℕ)) i)!) (Finset.mem_univ q)]
    rw [show (n - (Pi.single q (1:ℕ) : Fin 12 → ℕ)) q = n q - 1 by simp [Pi.sub_apply]]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_erase] at hi
    simp [Pi.sub_apply, Pi.single_eq_of_ne hi.1]
  rw [hL, hR]

/-- Sum form: for `1 ≤ n q`, subtracting `e_q` lowers the total sum by one. -/
lemma sum_eq_sub_one_of_sub_single (n : Fin 12 → ℕ) (q : Fin 12) (hq : 1 ≤ n q) :
    ∑ i, ((n - (Pi.single q (1:ℕ) : Fin 12 → ℕ)) i) = (∑ i, n i) - 1 := by
  rw [← Finset.add_sum_erase Finset.univ
    (fun i => ((n - (Pi.single q (1:ℕ) : Fin 12 → ℕ)) i)) (Finset.mem_univ q)]
  rw [show (n - (Pi.single q (1:ℕ) : Fin 12 → ℕ)) q = n q - 1 by simp [Pi.sub_apply]]
  have hrest : ∑ i ∈ Finset.univ.erase q, ((n - (Pi.single q (1:ℕ) : Fin 12 → ℕ)) i)
      = ∑ i ∈ Finset.univ.erase q, n i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_erase] at hi
    simp [Pi.sub_apply, Pi.single_eq_of_ne hi.1]
  rw [hrest]
  have hsum : n q + ∑ i ∈ Finset.univ.erase q, n i = ∑ i, n i :=
    Finset.add_sum_erase Finset.univ n (Finset.mem_univ q)
  omega

/-- Cleared form of the descent step: `n q · (n - e_q).multinomial · ∏ n_i! = n q · (N-1)!`. -/
lemma multinomial_sub_single_mul (n : Fin 12 → ℕ) (q : Fin 12) (hq : 1 ≤ n q) :
    Nat.multinomial Finset.univ (n - (Pi.single q (1:ℕ) : Fin 12 → ℕ)) * (∏ i, (n i)!)
      = n q * ((∑ i, n i) - 1)! := by
  have hspec : (∏ i, ((n - (Pi.single q (1:ℕ) : Fin 12 → ℕ)) i)!)
      * Nat.multinomial Finset.univ (n - (Pi.single q (1:ℕ) : Fin 12 → ℕ))
      = ((∑ i, n i) - 1)! := by
    have := Nat.multinomial_spec Finset.univ (n - (Pi.single q (1:ℕ) : Fin 12 → ℕ))
    rwa [sum_eq_sub_one_of_sub_single n q hq] at this
  rw [prod_factorial_eq_mul_prod_sub_single n q hq]
  calc Nat.multinomial Finset.univ (n - (Pi.single q (1:ℕ) : Fin 12 → ℕ))
        * (n q * ∏ i, ((n - (Pi.single q (1:ℕ) : Fin 12 → ℕ)) i)!)
      = n q * ((∏ i, ((n - (Pi.single q (1:ℕ) : Fin 12 → ℕ)) i)!)
          * Nat.multinomial Finset.univ (n - (Pi.single q (1:ℕ) : Fin 12 → ℕ))) := by ring
    _ = n q * ((∑ i, n i) - 1)! := by rw [hspec]

/-- **The Pascal-type recursion for the factorisation's scalar factor.**
With `ι = Fin 12` and `Mc k n = (∑ i, n i).choose k * n.multinomial`, the identity
`Mc (k+1) n = Mc k n + ∑_{q : n q ≥ 1} Mc k (n - e_q)` holds: the `(k+1)`-st binomial factor
splits by Pascal's rule and the multinomial factor of `n - e_q` is `n q` times that of `n`
after clearing denominators `∏ᵢ (n i)!`. -/
theorem multinomial_factor_rec (k : ℕ) (n : Fin 12 → ℕ) :
    Nat.choose (k + 1) (∑ i, n i) * Nat.multinomial Finset.univ n
      = Nat.choose k (∑ i, n i) * Nat.multinomial Finset.univ n
        + ∑ q : Fin 12, if 1 ≤ n q then
            Nat.choose k (∑ i, n i - 1)
              * Nat.multinomial Finset.univ (n - (Pi.single q (1:ℕ) : Fin 12 → ℕ))
          else 0 := by
  classical
  rcases Nat.eq_zero_or_pos (∑ i, n i) with hN0 | hNpos
  · have hn : n = 0 := by
      funext i
      exact (Finset.sum_eq_zero_iff.mp hN0) i (Finset.mem_univ i)
    rw [hn]
    simp [Nat.multinomial]
  · have hN1 : 1 ≤ ∑ i, n i := hNpos
    have hPpos : 0 < ∏ i, (n i)! := Finset.prod_pos (fun i _ => Nat.factorial_pos (n i))
    have hMP : Nat.multinomial Finset.univ n * (∏ i, (n i)!) = (∑ i, n i)! := by
      rw [mul_comm]; exact Nat.multinomial_spec Finset.univ n
    have hPascal : Nat.choose (k + 1) (∑ i, n i)
        = Nat.choose k (∑ i, n i) + Nat.choose k ((∑ i, n i) - 1) := by
      have h2 : ((∑ i, n i) - 1).succ = (∑ i, n i) := by
        rw [Nat.succ_eq_add_one, Nat.sub_add_cancel hN1]
      have h := Nat.choose_succ_succ k ((∑ i, n i) - 1)
      rw [h2] at h
      rw [h]
      exact add_comm _ _
    have hfacN : ((∑ i, n i) - 1)! * (∑ i, n i) = (∑ i, n i)! := by
      rw [mul_comm]
      conv_rhs => rw [← Nat.sub_add_cancel hN1]
      rw [Nat.factorial_succ, Nat.sub_add_cancel hN1]
    have key : ∀ q : Fin 12,
        (if 1 ≤ n q then Nat.choose k ((∑ i, n i) - 1)
            * Nat.multinomial Finset.univ (n - (Pi.single q (1:ℕ) : Fin 12 → ℕ))
          else 0) * (∏ i, (n i)!)
        = Nat.choose k ((∑ i, n i) - 1) * (n q * ((∑ i, n i) - 1)!) := by
      intro q
      by_cases hq : 1 ≤ n q
      · rw [if_pos hq, mul_assoc, multinomial_sub_single_mul n q hq]
      · have hq0 : n q = 0 := by omega
        rw [if_neg hq, zero_mul, hq0, zero_mul, mul_zero]
    have hsum1 : ∑ q : Fin 12, Nat.choose k ((∑ i, n i) - 1) * (n q * ((∑ i, n i) - 1)!)
        = Nat.choose k ((∑ i, n i) - 1) * ((∑ i, n i) - 1)! * ∑ q, n q := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    have hC : (∑ q : Fin 12, if 1 ≤ n q then Nat.choose k ((∑ i, n i) - 1)
            * Nat.multinomial Finset.univ (n - (Pi.single q (1:ℕ) : Fin 12 → ℕ))
          else 0) * (∏ i, (n i)!)
        = Nat.choose k ((∑ i, n i) - 1) * (∑ i, n i)! := by
      rw [Finset.sum_mul, Finset.sum_congr rfl (fun q _ => key q), hsum1,
        mul_assoc, hfacN]
    apply Nat.mul_right_cancel hPpos
    rw [mul_assoc, hMP, add_mul, mul_assoc, hMP, hC, ← add_mul, ← hPascal]

end Commons.Data.Nat
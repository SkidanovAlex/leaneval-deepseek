/-
  Companion paper, §9: the assembly of the remainder hypothesis (9.7)

      `R(t,D) = ∑♭_{d ≤ D} |r̃_d(t)| ⩽ Ã(x)(log x)^{−2^22}`,

  from the three inputs of the paper: `E₁` (9.11), `E₂` (9.12) and the `g̃`-tail.  This is
  `S9c.Rtilde_sum_le` (the exact assembly) combined with `S9b.E1_le` (the reduction of `E₁` to
  the `(R′₃)`-sum over cubefree moduli) and `S9d.Etwo_le` (the reduction of `E₂`).
-/
import Mathlib
import Submission.ASP.S9b
import Submission.ASP.S9c
import Submission.ASP.S9d

namespace Submission.ASP

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- **Companion §9, (9.7)**, reduced to its four explicit inputs: `(R′₃)`-type bound on the
cubefree τ-weighted sum (`hE1`), the τ³-weighted square-divisor count (`hX`), the two
Cauchy–Schwarz factors of `E₂` (`hS1`, `hS2`), the `g`-part of `E₂` (`hG`) and the `g̃`-tail. -/
theorem Rtilde_sum_le_of_inputs (a g : ℕ → ℝ) (r : ℕ → ℕ → ℝ) (gtil : ℕ → ℝ) (t D L Y : ℕ)
    (hLt : L ≤ t) (hLY : L < Y) (hYt : Y ≤ t)
    (ha : ∀ n, 0 ≤ a n) (hg : ∀ n, 0 ≤ g n) (happ : Approx a g r (t : ℝ))
    {X1 X S1 S2 Gsum : ℝ}
    (hE1 : (∑ k ∈ (Finset.Icc 1 (D * L ^ 2)).filter CubefreeN,
        (k.divisors.card : ℝ) * |r k t|) ≤ X1)
    (hX : (∑ n ∈ Finset.Icc 1 t, (n.divisors.card : ℝ) ^ 3
        * (sqdvCount n (Y + 1) t : ℝ)) ≤ X)
    (hS1 : (∑ ν ∈ ((Finset.Icc (L + 1) Y).filter Squarefree), Ad a (ν ^ 2) t) ≤ S1)
    (hS2 : (∑ n ∈ Finset.Icc 1 t, a n * (n.divisors.card : ℝ) ^ 3) ≤ S2)
    (hG : EtwoG a g t D (L + 1) t ≤ Gsum) :
    (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |rtilde r gtil d t|)
      ≤ X1 + (Real.sqrt S1 * Real.sqrt S2
          + Real.sqrt (∑ n ∈ Finset.Icc 1 t, a n ^ 2) * Real.sqrt X + Gsum)
        + (∑ d ∈ (Finset.Icc 1 D).filter Squarefree, |gtil d|)
            * (∑ ν ∈ Finset.Icc 1 t, |r (ν ^ 2) t|) := by
  have hE1' : Eone r t D L ≤ X1 := E1_le r t D L hE1
  have hE2 : Etwo a g t D L ≤ Real.sqrt S1 * Real.sqrt S2
      + Real.sqrt (∑ n ∈ Finset.Icc 1 t, a n ^ 2) * Real.sqrt X + Gsum :=
    Etwo_le a g ha t D L Y (by omega) hLY hYt hX hS1 hS2 hG
  have hmain := Rtilde_sum_le a g r gtil t D L hLt ha hg happ
  linarith [hmain, hE1', hE2]

/-! ### The transfer of a Theorem-1 type estimate from `ã` to `a` -/

/-- `ã_p = a_p` at primes: `ã` is squarefree-supported, so the *prime* sums of `a` and `ã`
coincide. -/
lemma atil_prime (a : ℕ → ℝ) {p : ℕ} (hp : p.Prime) : atil a p = a p := by
  rw [atil, ArithmeticFunction.moebius_apply_prime hp]
  norm_num

/-- The prime sum is unchanged by the passage `a ↦ ã` — this is why Theorem 1 applied to `ã`
proves Theorem 2 for `a`. -/
lemma sum_primes_atil_eq (a : ℕ → ℝ) (x : ℕ) :
    (∑ p ∈ Nat.primesBelow (x + 1), Real.log (p : ℝ) * atil a p)
      = ∑ p ∈ Nat.primesBelow (x + 1), Real.log (p : ℝ) * a p := by
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Nat.mem_primesBelow] at hp
  rw [atil_prime a hp.2]

/-- **Companion §9, (9.12)+(9.13)+(9.14)** (abstract form): if `Q` approximates `H̃·Ã(x)` and
(9.12) `Ã(x) = G·A(x)(1 + O(δ))` and (9.13) `H̃·G = H` hold, then `Q` approximates
`H·A(x)` with error increased by `|H̃|·G·A(x)·δ`. -/
theorem transfer_abs {Q H Htil G E δ A Aa : ℝ}
    (hT1 : |Q - Htil * Aa| ≤ E)
    (hH : Htil * G = H)
    (h912 : |Aa - G * A| ≤ G * A * δ) :
    |Q - H * A| ≤ E + |Htil| * G * A * δ := by
  have hkey : Q - H * A = (Q - Htil * Aa) + Htil * (Aa - G * A) + (Htil * G - H) * A := by
    ring
  have h1 : |Htil * (Aa - G * A)| ≤ |Htil| * (G * A) * δ := by
    calc |Htil * (Aa - G * A)| = |Htil| * |Aa - G * A| := by rw [abs_mul]
      _ ≤ |Htil| * (G * A * δ) := mul_le_mul_of_nonneg_left h912 (abs_nonneg _)
      _ = |Htil| * (G * A) * δ := by ring
  have htri : |(Q - Htil * Aa) + Htil * (Aa - G * A) + (Htil * G - H) * A|
      ≤ |Q - Htil * Aa| + |Htil * (Aa - G * A)| + |(Htil * G - H) * A| := by
    refine le_trans (abs_add_le _ _) ?_
    linarith [abs_add_le (Q - Htil * Aa) (Htil * (Aa - G * A))]
  calc |Q - H * A|
      = |(Q - Htil * Aa) + Htil * (Aa - G * A) + (Htil * G - H) * A| := by rw [hkey]
    _ ≤ |Q - Htil * Aa| + |Htil * (Aa - G * A)| + |(Htil * G - H) * A| := htri
    _ ≤ E + |Htil| * (G * A) * δ + 0 := by
        refine add_le_add (add_le_add hT1 h1) ?_
        rw [hH]; simp
    _ = E + |Htil| * G * A * δ := by ring

/-- **Companion §9, (9.12)+(9.13)+(9.14)**, for the sieve sum of `ã`. -/
theorem transfer_H (a lam : ℕ → ℝ) (N : ℕ) {H Htil G E δ z : ℝ}
    (hT1 : |(∑ n ∈ Finset.Icc 1 N, atil a n * rhoOf lam n *
        (if z < (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0))
        - Htil * Acount (atil a) (N : ℝ)| ≤ E)
    (hH : Htil * G = H)
    (h912 : |Acount (atil a) (N : ℝ) - G * Acount a (N : ℝ)|
        ≤ G * Acount a (N : ℝ) * δ) :
    |(∑ n ∈ Finset.Icc 1 N, atil a n * rhoOf lam n *
        (if z < (n : ℝ) then ArithmeticFunction.vonMangoldt n else 0)) - H * Acount a (N : ℝ)|
      ≤ E + |Htil| * G * Acount a (N : ℝ) * δ :=
  transfer_abs hT1 hH h912

/-- **Companion §9, Theorem 2** (the last step): Theorem 1's prime-sum asymptotic for the
squarefree-supported sequence `ã`, together with (9.12) and (9.13), gives the prime-sum
asymptotic for the original sequence `a`. -/
theorem primeSum_transfer (a : ℕ → ℝ) (x : ℕ) {H Htil G E δ : ℝ}
    (hT1 : |(∑ p ∈ Nat.primesBelow (x + 1), Real.log (p : ℝ) * atil a p)
        - Htil * Acount (atil a) (x : ℝ)| ≤ E)
    (hH : Htil * G = H)
    (h912 : |Acount (atil a) (x : ℝ) - G * Acount a (x : ℝ)|
        ≤ G * Acount a (x : ℝ) * δ) :
    |(∑ p ∈ Nat.primesBelow (x + 1), Real.log (p : ℝ) * a p) - H * Acount a (x : ℝ)|
      ≤ E + |Htil| * G * Acount a (x : ℝ) * δ := by
  rw [← sum_primes_atil_eq a x]
  exact transfer_abs hT1 hH h912

end

end Submission.ASP

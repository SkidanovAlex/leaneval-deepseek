import Mathlib
import Submission.Work.FIArea2.R6.ndCountDefs

/-!
# `FIArea2/R6/gcdBox_eq_sum_totient`

The identity

  `gcdBox c X Y = Σ_{d ∣ c} φ(d) · #{h₁ ∈ zPz X : d ∣ h₁²} · #{h₂ ∈ zPz Y : d ∣ h₂²}`,

obtained by writing `gcd(c, h₁², h₂²) = Σ_{d ∣ gcd(c,h₁²,h₂²)} φ(d)` (`Nat.sum_totient`)
and interchanging the order of summation.
-/

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- `Nat.gcd (Nat.gcd c A) B` written as a sum of totients over the divisors of `c`
that divide both `A` and `B`. -/
lemma gcd_gcd_eq_sum_totient (c A B : ℕ) (hc : 1 ≤ c) :
    Nat.gcd (Nat.gcd c A) B
      = ∑ d ∈ c.divisors, (if (d ∣ A ∧ d ∣ B) then Nat.totient d else 0) := by
  have hc0 : c ≠ 0 := Nat.one_le_iff_ne_zero.mp hc
  have hG0 : Nat.gcd (Nat.gcd c A) B ≠ 0 := by
    have hdvd : Nat.gcd (Nat.gcd c A) B ∣ c :=
      dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
    exact (Nat.pos_of_dvd_of_pos hdvd (by omega)).ne'
  have hmem : (Nat.gcd (Nat.gcd c A) B).divisors
      = c.divisors.filter (fun d => d ∣ A ∧ d ∣ B) := by
    ext d
    rw [Nat.mem_divisors, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · intro h
      obtain ⟨hdvd, _⟩ := h
      obtain ⟨h1, h2⟩ := Nat.dvd_gcd_iff.mp hdvd
      obtain ⟨h3, h4⟩ := Nat.dvd_gcd_iff.mp h1
      exact ⟨⟨h3, hc0⟩, ⟨h4, h2⟩⟩
    · intro h
      obtain ⟨⟨hdc, _⟩, ⟨hdA, hdB⟩⟩ := h
      exact ⟨Nat.dvd_gcd (Nat.dvd_gcd hdc hdA) hdB, hG0⟩
  calc Nat.gcd (Nat.gcd c A) B
      = ∑ d ∈ (Nat.gcd (Nat.gcd c A) B).divisors, Nat.totient d :=
        (Nat.sum_totient _).symm
    _ = ∑ d ∈ c.divisors, (if (d ∣ A ∧ d ∣ B) then Nat.totient d else 0) := by
        rw [hmem, Finset.sum_filter]

/-- The double sum of the indicator of `d ∣ h₁² ∧ d ∣ h₂²` weighted by `φ(d)` factors
as `φ(d)` times the two filtered cardinalities. -/
lemma sum2_factor_dvd (X Y d : ℕ) :
    (∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
        (if (d ∣ (h1 ^ 2).natAbs ∧ d ∣ (h2 ^ 2).natAbs) then Nat.totient d else 0))
      = Nat.totient d * ((zPz X).filter (fun h => d ∣ (h ^ 2).natAbs)).card
          * ((zPz Y).filter (fun h => d ∣ (h ^ 2).natAbs)).card := by
  have h1 : ∀ x : ℤ, (∑ y ∈ zPz Y,
        (if (d ∣ (x ^ 2).natAbs ∧ d ∣ (y ^ 2).natAbs) then Nat.totient d else 0))
      = if d ∣ (x ^ 2).natAbs
          then (((zPz Y).filter (fun h => d ∣ (h ^ 2).natAbs)).card * Nat.totient d)
          else 0 := by
    intro x
    by_cases hx : d ∣ (x ^ 2).natAbs
    · simp only [hx, true_and]
      rw [← Finset.sum_filter]
      exact Finset.sum_const_nat (fun y _ => rfl)
    · rw [if_neg hx]
      apply Finset.sum_eq_zero
      intro y _
      exact if_neg (fun hc => hx hc.1)
  calc ∑ x ∈ zPz X, ∑ y ∈ zPz Y,
          (if (d ∣ (x ^ 2).natAbs ∧ d ∣ (y ^ 2).natAbs) then Nat.totient d else 0)
      = ∑ x ∈ zPz X, (if d ∣ (x ^ 2).natAbs
          then (((zPz Y).filter (fun h => d ∣ (h ^ 2).natAbs)).card * Nat.totient d)
          else 0) :=
        Finset.sum_congr rfl (fun x _ => h1 x)
    _ = ∑ x ∈ (zPz X).filter (fun h => d ∣ (h ^ 2).natAbs),
          (((zPz Y).filter (fun h => d ∣ (h ^ 2).natAbs)).card * Nat.totient d) := by
        rw [← Finset.sum_filter]
    _ = ((zPz X).filter (fun h => d ∣ (h ^ 2).natAbs)).card
          * (((zPz Y).filter (fun h => d ∣ (h ^ 2).natAbs)).card * Nat.totient d) :=
        Finset.sum_const_nat (fun x _ => rfl)
    _ = Nat.totient d * ((zPz X).filter (fun h => d ∣ (h ^ 2).natAbs)).card
          * ((zPz Y).filter (fun h => d ∣ (h ^ 2).natAbs)).card := by ring

theorem gcdBox_eq_sum_totient (c X Y : ℕ) (hc : 1 ≤ c) :
    Work.FIArea2.R6.gcdBox c X Y
      = c.divisors.sum (fun d => Nat.totient d
          * ((Work.FIArea2.R6.zPz X).filter (fun h => d ∣ (h ^ 2).natAbs)).card
          * ((Work.FIArea2.R6.zPz Y).filter (fun h => d ∣ (h ^ 2).natAbs)).card) := by
  unfold gcdBox
  calc ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, Nat.gcd (Nat.gcd c (h1 ^ 2).natAbs) (h2 ^ 2).natAbs
      = ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, ∑ d ∈ c.divisors,
          (if (d ∣ (h1 ^ 2).natAbs ∧ d ∣ (h2 ^ 2).natAbs) then Nat.totient d else 0) := by
        apply Finset.sum_congr rfl; intro h1 _
        apply Finset.sum_congr rfl; intro h2 _
        exact gcd_gcd_eq_sum_totient c (h1 ^ 2).natAbs (h2 ^ 2).natAbs hc
    _ = ∑ d ∈ c.divisors, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
          (if (d ∣ (h1 ^ 2).natAbs ∧ d ∣ (h2 ^ 2).natAbs) then Nat.totient d else 0) := by
        calc ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y, ∑ d ∈ c.divisors,
                (if (d ∣ (h1 ^ 2).natAbs ∧ d ∣ (h2 ^ 2).natAbs) then Nat.totient d else 0)
            = ∑ h2 ∈ zPz Y, ∑ h1 ∈ zPz X, ∑ d ∈ c.divisors,
                (if (d ∣ (h1 ^ 2).natAbs ∧ d ∣ (h2 ^ 2).natAbs) then Nat.totient d else 0) :=
              Finset.sum_comm
          _ = ∑ h2 ∈ zPz Y, ∑ d ∈ c.divisors, ∑ h1 ∈ zPz X,
                (if (d ∣ (h1 ^ 2).natAbs ∧ d ∣ (h2 ^ 2).natAbs) then Nat.totient d else 0) := by
              apply Finset.sum_congr rfl; intro h2 _
              exact Finset.sum_comm
          _ = ∑ d ∈ c.divisors, ∑ h2 ∈ zPz Y, ∑ h1 ∈ zPz X,
                (if (d ∣ (h1 ^ 2).natAbs ∧ d ∣ (h2 ^ 2).natAbs) then Nat.totient d else 0) :=
              Finset.sum_comm
          _ = ∑ d ∈ c.divisors, ∑ h1 ∈ zPz X, ∑ h2 ∈ zPz Y,
                (if (d ∣ (h1 ^ 2).natAbs ∧ d ∣ (h2 ^ 2).natAbs) then Nat.totient d else 0) := by
              apply Finset.sum_congr rfl; intro d _
              exact Finset.sum_comm
    _ = ∑ d ∈ c.divisors, Nat.totient d
          * ((zPz X).filter (fun h => d ∣ (h ^ 2).natAbs)).card
          * ((zPz Y).filter (fun h => d ∣ (h ^ 2).natAbs)).card := by
        apply Finset.sum_congr rfl; intro d _
        exact sum2_factor_dvd X Y d

end Work.FIArea2.R6

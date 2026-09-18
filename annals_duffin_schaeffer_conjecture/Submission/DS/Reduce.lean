import Mathlib
open scoped Nat

/-!
# Reduction of fractions to lowest terms

If `(a,q)` is a pair with `q : ℕ+`, we reduce to `(a/g, q/g)` where `g = gcd a q`.
This file collects the basic algebraic facts about this reduction.
-/

namespace Submission.DS

/-- `gcd a q` (with `q` viewed as a natural number). -/
def g (a : ℕ) (q : ℕ+) : ℕ := Nat.gcd a (q : ℕ)

lemma g_pos (a : ℕ) (q : ℕ+) : 0 < g a q := by
  exact Nat.gcd_pos_of_pos_right a q.property

lemma g_le_q (a : ℕ) (q : ℕ+) : g a q ≤ (q : ℕ) := by
  exact Nat.le_of_dvd q.property (Nat.gcd_dvd_right a (q : ℕ))

lemma g_le_a_of_pos (a : ℕ) (q : ℕ+) (ha : 0 < a) : g a q ≤ a := by
  exact Nat.le_of_dvd ha (Nat.gcd_dvd_left a (q : ℕ))

lemma g_dvd_a (a : ℕ) (q : ℕ+) : g a q ∣ a := by
  exact Nat.gcd_dvd_left a (q : ℕ)

lemma g_dvd_q (a : ℕ) (q : ℕ+) : g a q ∣ (q : ℕ) := by
  exact Nat.gcd_dvd_right a (q : ℕ)

/-- Reduced denominator `q / gcd a q`, as a positive natural. -/
def denRed (a : ℕ) (q : ℕ+) : ℕ+ :=
  ⟨(q : ℕ) / g a q, Nat.div_pos (g_le_q a q) (g_pos a q)⟩

/-- Reduced numerator `a / gcd a q`. -/
def numRed (a : ℕ) (q : ℕ+) : ℕ := a / g a q

lemma numRed_coprime_denRed (a : ℕ) (q : ℕ+) :
    Nat.Coprime (numRed a q) (denRed a q : ℕ) := by
  change Nat.Coprime (a / g a q) ((q : ℕ) / g a q)
  exact Nat.coprime_div_gcd_div_gcd (Nat.gcd_pos_of_pos_right a q.property)

lemma numRed_le_denRed (a : ℕ) (q : ℕ+) (haq : a ≤ (q : ℕ)) :
    numRed a q ≤ (denRed a q : ℕ) := by
  change a / g a q ≤ (q : ℕ) / g a q
  exact Nat.div_le_div_right haq

lemma numRed_mul_g (a : ℕ) (q : ℕ+) : numRed a q * g a q = a := by
  change a / g a q * g a q = a
  exact Nat.div_mul_cancel (g_dvd_a a q)

lemma denRed_mul_g (a : ℕ) (q : ℕ+) : (denRed a q : ℕ) * g a q = (q : ℕ) := by
  change (q : ℕ) / g a q * g a q = (q : ℕ)
  exact Nat.div_mul_cancel (g_dvd_q a q)

lemma denRed_dvd_q (a : ℕ) (q : ℕ+) : (denRed a q : ℕ) ∣ (q : ℕ) := by
  use g a q
  exact (denRed_mul_g a q).symm

lemma denRed_le_q (a : ℕ) (q : ℕ+) : (denRed a q : ℕ) ≤ (q : ℕ) := by
  exact Nat.le_of_dvd q.property (denRed_dvd_q a q)

lemma numRed_zero_iff_zero (a : ℕ) (q : ℕ+) : numRed a q = 0 ↔ a = 0 := by
  constructor
  · intro h
    calc
      a = numRed a q * g a q := (numRed_mul_g a q).symm
      _ = 0 := by simp [h]
  · intro ha
    rw [ha]
    simp [numRed]

lemma numRed_pos_of_pos (a : ℕ) (q : ℕ+) (ha : 0 < a) : 0 < numRed a q := by
  by_contra h
  have hz : numRed a q = 0 := Nat.eq_zero_of_not_pos h
  have ha0 : a = 0 := (numRed_zero_iff_zero a q).mp hz
  omega

/-- The reduced fraction has the same real value as the original. -/
lemma reduced_value_eq (a : ℕ) (q : ℕ+) :
    ((numRed a q : ℝ) / (denRed a q : ℝ)) = (a : ℝ) / (q : ℝ) := by
  have hden : (denRed a q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (denRed a q).2)
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt q.2)
  rw [div_eq_div_iff hden hq]
  have hnat : numRed a q * (q : ℕ) = a * (denRed a q : ℕ) := by
    have hq' : (q : ℕ) = g a q * (denRed a q : ℕ) := by
      rw [← denRed_mul_g a q, mul_comm]
    calc
      numRed a q * (q : ℕ) = numRed a q * (g a q * (denRed a q : ℕ)) := by rw [hq']
      _ = (numRed a q * g a q) * (denRed a q : ℕ) := by rw [Nat.mul_assoc]
      _ = a * (denRed a q : ℕ) := by rw [numRed_mul_g a q]
  exact_mod_cast hnat

lemma denRed_dvd_pnat (a : ℕ) (q : ℕ+) : denRed a q ∣ q := by
  refine ⟨⟨g a q, g_pos a q⟩, ?_⟩
  apply PNat.coe_inj.mp
  change (q : ℕ) = (denRed a q : ℕ) * g a q
  exact (denRed_mul_g a q).symm

end Submission.DS

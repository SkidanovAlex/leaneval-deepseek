import Mathlib
import Submission.Work.ZeroFreeTables.tf72Phi_defs

open scoped Real
open MeasureTheory

namespace Work.ZeroFreeTables

lemma tf72PhiUB_eq_integral (x : ℝ) :
    tf72PhiUB x = (1 / 30) * ∫ s in (0 : ℝ)..2,
      ((∑ m ∈ Finset.range 9, (x * s) ^ m / (m.factorial : ℝ))
        + 2 * (x * s) ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s := by
  have hcont : ∀ m : ℕ, Continuous
      (fun s : ℝ => ((x * s) ^ m / ((m.factorial : ℕ) : ℝ)) * tf72Body s) := by
    intro m
    rw [show (fun s : ℝ => ((x * s) ^ m / ((m.factorial : ℕ) : ℝ)) * tf72Body s)
          = fun s : ℝ => (x * s) ^ m * (((m.factorial : ℕ) : ℝ))⁻¹ * tf72Body s by
        funext s; rw [div_eq_mul_inv]]
    unfold tf72Body
    fun_prop
  have hCterm : ∀ m : ℕ, IntervalIntegrable
      (fun s : ℝ => ((x * s) ^ m / ((m.factorial : ℕ) : ℝ)) * tf72Body s) volume (0 : ℝ) 2 :=
    fun m => (hcont m).intervalIntegrable 0 2
  have hBcont : Continuous
      (fun s : ℝ => (2 * (x * s) ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s) := by
    rw [show (fun s : ℝ => (2 * (x * s) ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s)
          = fun s : ℝ => 2 * (x * s) ^ 9 * (((Nat.factorial 9 : ℕ) : ℝ))⁻¹ * tf72Body s by
        funext s; rw [div_eq_mul_inv]]
    unfold tf72Body
    fun_prop
  have hA : IntervalIntegrable
      (fun s : ℝ => ∑ m ∈ Finset.range 9, ((x * s) ^ m / ((m.factorial : ℕ) : ℝ)) * tf72Body s)
      volume (0 : ℝ) 2 :=
    (continuous_finsetSum (Finset.range 9) (fun m _ => hcont m)).intervalIntegrable 0 2
  have hB : IntervalIntegrable
      (fun s : ℝ => (2 * (x * s) ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s) volume (0 : ℝ) 2 :=
    hBcont.intervalIntegrable 0 2
  have hval : ∀ m : ℕ,
      (∫ s in (0 : ℝ)..2, ((x * s) ^ m / ((m.factorial : ℕ) : ℝ)) * tf72Body s)
        = x ^ m * tf72M m / ((m.factorial : ℕ) : ℝ) := by
    intro m
    rw [show (fun s : ℝ => ((x * s) ^ m / ((m.factorial : ℕ) : ℝ)) * tf72Body s)
          = (fun s : ℝ => (x ^ m / ((m.factorial : ℕ) : ℝ)) * (s ^ m * tf72Body s)) by
        funext s; rw [mul_pow]; ring]
    rw [intervalIntegral.integral_const_mul, tf72M_eq_integral]
    ring
  have hrem : (∫ s in (0 : ℝ)..2,
        (2 * (x * s) ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s)
      = 2 * x ^ 9 * tf72M 9 / ((Nat.factorial 9 : ℕ) : ℝ) := by
    rw [show (fun s : ℝ => (2 * (x * s) ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s)
          = (fun s : ℝ => (2 * x ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ)) * (s ^ 9 * tf72Body s)) by
        funext s; rw [mul_pow]; ring]
    rw [intervalIntegral.integral_const_mul, tf72M_eq_integral]
    ring
  rw [tf72PhiUB]
  congr 1
  rw [show (fun s : ℝ => ((∑ m ∈ Finset.range 9, (x * s) ^ m / (m.factorial : ℝ))
        + 2 * (x * s) ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s)
      = (fun s : ℝ => (∑ m ∈ Finset.range 9, ((x * s) ^ m / (m.factorial : ℝ)) * tf72Body s)
        + (2 * (x * s) ^ 9 / ((Nat.factorial 9 : ℕ) : ℝ)) * tf72Body s) by
    funext s; rw [add_mul, Finset.sum_mul]]
  rw [intervalIntegral.integral_add hA hB]
  rw [intervalIntegral.integral_finsetSum (s := Finset.range 9) (fun m _ => hCterm m)]
  have hsum_eq : (∑ m ∈ Finset.range 9,
        ∫ s in (0 : ℝ)..2, ((x * s) ^ m / ((m.factorial : ℕ) : ℝ)) * tf72Body s)
      = ∑ m ∈ Finset.range 9, x ^ m * tf72M m / ((m.factorial : ℕ) : ℝ) :=
    Finset.sum_congr rfl (fun m _ => hval m)
  rw [hsum_eq, hrem]

end Work.ZeroFreeTables

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib
import Mathlib.Data.Real.Basic

namespace Commons.NumberTheory.Sieve

open Finset

/-- Real-parameter version of `sum_mu_divisors_mul_truncated`: the double Möbius sum
collapses to the truncated function at `n` itself. -/
theorem sum_mu_divisors_mul_truncated_real {f : ℕ → ℝ} {n : ℕ} (hn : 0 < n) (z : ℝ) :
    (∑ b ∈ n.divisors, ∑ c ∈ (n / b).divisors,
        (ArithmeticFunction.moebius b : ℝ) * (if z < (c : ℝ) then f c else 0))
      = if z < (n : ℝ) then f n else 0 := by
  have hMob := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
      (f := fun c => if z < (c : ℝ) then f c else 0)
      (g := fun m => ∑ c ∈ m.divisors, (if z < (c : ℝ) then f c else 0))).mp
      (fun m _ => rfl)
  rw [← hMob n hn]
  trans ∑ b ∈ n.divisors,
      (ArithmeticFunction.moebius b : ℝ) *
        ∑ c ∈ (n / b).divisors, (if z < (c : ℝ) then f c else 0)
  · apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
  · rw [← Nat.sum_divisorsAntidiagonal (f := fun i j =>
        (ArithmeticFunction.moebius i : ℝ) *
          ∑ c ∈ j.divisors, (if z < (c : ℝ) then f c else 0))]

/-- The five-term real coefficient identity attached to a pair `(β, γ)`. -/
private lemma pointwise_coeff (x : ℝ) {β γ σ y z : ℝ} (hβ : 1 ≤ β) (hγ : 1 ≤ γ)
    (hσ : 1 ≤ σ) :
    (if β ≤ y then x else 0)
      - (if β ≤ y then (if γ ≤ z then x else 0) else 0)
      + (if σ * y < β then (if σ * z < γ then x else 0) else 0)
      + (if y < β ∧ β ≤ σ * y then (if z < γ then x else 0) else 0)
      + (if σ * y < β then (if z < γ ∧ γ ≤ σ * z then x else 0) else 0)
      = if z < γ then x else 0 := by
  by_cases hb : β ≤ y
  · have hy0 : 0 < y := lt_of_lt_of_le (by linarith : (0 : ℝ) < β) hb
    have hsy_ge : β ≤ σ * y := by
      have h : 0 ≤ (σ - 1) * y := mul_nonneg (by linarith) (le_of_lt hy0)
      nlinarith [h]
    have hsy : ¬ σ * y < β := by linarith
    have hn3 : ¬ (y < β ∧ β ≤ σ * y) := by rintro ⟨h1, _⟩; linarith
    simp only [if_pos hb, if_neg hsy, if_neg hn3]
    by_cases hc : γ ≤ z
    · simp only [if_pos hc, if_neg (show ¬ z < γ by linarith)]
      ring
    · have hzc : z < γ := lt_of_not_ge hc
      simp only [if_neg hc, if_pos hzc]
      ring
  · have hyb : y < β := lt_of_not_ge hb
    by_cases hbsy : β ≤ σ * y
    · have hsy : ¬ σ * y < β := by linarith
      simp only [if_neg hb, if_neg hsy, if_pos (show y < β ∧ β ≤ σ * y from ⟨hyb, hbsy⟩)]
      ring
    · have hsy : σ * y < β := lt_of_not_ge hbsy
      have hn3 : ¬ (y < β ∧ β ≤ σ * y) := by rintro ⟨_, h⟩; exact hbsy h
      simp only [if_neg hb, if_pos hsy, if_neg hn3]
      by_cases hzc : z < γ
      · by_cases hsz : σ * z < γ
        · have hc : ¬ (z < γ ∧ γ ≤ σ * z) := by rintro ⟨_, h⟩; linarith
          simp only [if_pos hsz, if_neg hc, if_pos hzc]
          ring
        · have hcz : γ ≤ σ * z := le_of_not_gt hsz
          simp only [if_neg hsz, if_pos (show z < γ ∧ γ ≤ σ * z from ⟨hzc, hcz⟩), if_pos hzc]
          ring
      · have hzγ : γ ≤ z := le_of_not_gt hzc
        have hz0 : 0 ≤ z := by linarith
        have hle : z ≤ σ * z := by
          have h : 0 ≤ (σ - 1) * z := mul_nonneg (by linarith) hz0
          nlinarith [h]
        have hsz : ¬ σ * z < γ := by linarith
        have hn : ¬ (z < γ ∧ γ ≤ σ * z) := by rintro ⟨h, _⟩; exact hzc h
        simp only [if_neg hsz, if_neg hn, if_neg hzc]
        ring

/-- The inner (over `c`) combination of the five truncated sums attached to a fixed
`b` equals the single truncated sum `∑_{c | D} [z < c] · F c`. -/
private lemma sum_combine (F : ℕ → ℝ) (D : Finset ℕ) {b s : ℕ} (y z : ℝ) (hs : 1 ≤ s)
    (hb : 1 ≤ b) (hD : ∀ c ∈ D, 1 ≤ c) :
    (if (b : ℝ) ≤ y then (∑ c ∈ D, F c) else 0)
      - (if (b : ℝ) ≤ y then (∑ c ∈ D, if (c : ℝ) ≤ z then F c else 0) else 0)
      + (if (s : ℝ) * y < (b : ℝ) then
          (∑ c ∈ D, if (s : ℝ) * z < (c : ℝ) then F c else 0) else 0)
      + (if y < (b : ℝ) ∧ (b : ℝ) ≤ (s : ℝ) * y then
          (∑ c ∈ D, if z < (c : ℝ) then F c else 0) else 0)
      + (if (s : ℝ) * y < (b : ℝ) then
          (∑ c ∈ D, if z < (c : ℝ) ∧ (c : ℝ) ≤ (s : ℝ) * z then F c else 0) else 0)
      = ∑ c ∈ D, (if z < (c : ℝ) then F c else 0) := by
  have h1 : (if (b : ℝ) ≤ y then (∑ c ∈ D, F c) else 0)
      = ∑ c ∈ D, (if (b : ℝ) ≤ y then F c else 0) := by
    by_cases h : (b : ℝ) ≤ y <;> simp [h]
  have h2 : (if (b : ℝ) ≤ y then (∑ c ∈ D, if (c : ℝ) ≤ z then F c else 0) else 0)
      = ∑ c ∈ D, (if (b : ℝ) ≤ y then (if (c : ℝ) ≤ z then F c else 0) else 0) := by
    by_cases h : (b : ℝ) ≤ y <;> simp [h]
  have h3 : (if (s : ℝ) * y < (b : ℝ) then
        (∑ c ∈ D, if (s : ℝ) * z < (c : ℝ) then F c else 0) else 0)
      = ∑ c ∈ D, (if (s : ℝ) * y < (b : ℝ) then
        (if (s : ℝ) * z < (c : ℝ) then F c else 0) else 0) := by
    by_cases h : (s : ℝ) * y < (b : ℝ) <;> simp [h]
  have h4 : (if y < (b : ℝ) ∧ (b : ℝ) ≤ (s : ℝ) * y then
        (∑ c ∈ D, if z < (c : ℝ) then F c else 0) else 0)
      = ∑ c ∈ D, (if y < (b : ℝ) ∧ (b : ℝ) ≤ (s : ℝ) * y then
        (if z < (c : ℝ) then F c else 0) else 0) := by
    by_cases h : y < (b : ℝ) ∧ (b : ℝ) ≤ (s : ℝ) * y <;> simp [h]
  have h5 : (if (s : ℝ) * y < (b : ℝ) then
        (∑ c ∈ D, if z < (c : ℝ) ∧ (c : ℝ) ≤ (s : ℝ) * z then F c else 0) else 0)
      = ∑ c ∈ D, (if (s : ℝ) * y < (b : ℝ) then
        (if z < (c : ℝ) ∧ (c : ℝ) ≤ (s : ℝ) * z then F c else 0) else 0) := by
    by_cases h : (s : ℝ) * y < (b : ℝ) <;> simp [h]
  rw [h1, h2, h3, h4, h5, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  exact pointwise_coeff (F c) (by exact_mod_cast hb) (by exact_mod_cast hD c hc)
    (by exact_mod_cast hs)

/-- The five-term combination attached to a single `b`, with its Möbius factor pulled
out, equals `μ b · ∑_{c | n/b} [z < c] · f c`. -/
private lemma per_b {f : ℕ → ℝ} {n : ℕ} (y z : ℝ) {s b : ℕ} (hs : 1 ≤ s) (hb : 1 ≤ b) :
    (if (b : ℝ) ≤ y then (ArithmeticFunction.moebius b : ℝ) *
        (∑ d ∈ (n / b).divisors, f d) else 0)
      - (if (b : ℝ) ≤ y then (ArithmeticFunction.moebius b : ℝ) *
          (∑ c ∈ (n / b).divisors, if (c : ℝ) ≤ z then f c else 0) else 0)
      + (if (s : ℝ) * y < (b : ℝ) then (ArithmeticFunction.moebius b : ℝ) *
          (∑ c ∈ (n / b).divisors, if (s : ℝ) * z < (c : ℝ) then f c else 0) else 0)
      + (if y < (b : ℝ) ∧ (b : ℝ) ≤ (s : ℝ) * y then (ArithmeticFunction.moebius b : ℝ) *
          (∑ c ∈ (n / b).divisors, if z < (c : ℝ) then f c else 0) else 0)
      + (if (s : ℝ) * y < (b : ℝ) then (ArithmeticFunction.moebius b : ℝ) *
          (∑ c ∈ (n / b).divisors, if z < (c : ℝ) ∧ (c : ℝ) ≤ (s : ℝ) * z then f c else 0)
          else 0)
      = (ArithmeticFunction.moebius b : ℝ) *
          (∑ c ∈ (n / b).divisors, if z < (c : ℝ) then f c else 0) := by
  have hA : (if (b : ℝ) ≤ y then (ArithmeticFunction.moebius b : ℝ) *
      (∑ d ∈ (n / b).divisors, f d) else 0)
      = (ArithmeticFunction.moebius b : ℝ) *
      (if (b : ℝ) ≤ y then (∑ d ∈ (n / b).divisors, f d) else 0) := by
    by_cases h : (b : ℝ) ≤ y <;> simp [h]
  have hB : (if (b : ℝ) ≤ y then (ArithmeticFunction.moebius b : ℝ) *
      (∑ c ∈ (n / b).divisors, if (c : ℝ) ≤ z then f c else 0) else 0)
      = (ArithmeticFunction.moebius b : ℝ) *
      (if (b : ℝ) ≤ y then (∑ c ∈ (n / b).divisors, if (c : ℝ) ≤ z then f c else 0)
        else 0) := by
    by_cases h : (b : ℝ) ≤ y <;> simp [h]
  have hC : (if (s : ℝ) * y < (b : ℝ) then (ArithmeticFunction.moebius b : ℝ) *
      (∑ c ∈ (n / b).divisors, if (s : ℝ) * z < (c : ℝ) then f c else 0) else 0)
      = (ArithmeticFunction.moebius b : ℝ) *
      (if (s : ℝ) * y < (b : ℝ) then
        (∑ c ∈ (n / b).divisors, if (s : ℝ) * z < (c : ℝ) then f c else 0) else 0) := by
    by_cases h : (s : ℝ) * y < (b : ℝ) <;> simp [h]
  have hD : (if y < (b : ℝ) ∧ (b : ℝ) ≤ (s : ℝ) * y then
      (ArithmeticFunction.moebius b : ℝ) *
      (∑ c ∈ (n / b).divisors, if z < (c : ℝ) then f c else 0) else 0)
      = (ArithmeticFunction.moebius b : ℝ) *
      (if y < (b : ℝ) ∧ (b : ℝ) ≤ (s : ℝ) * y then
        (∑ c ∈ (n / b).divisors, if z < (c : ℝ) then f c else 0) else 0) := by
    by_cases h : y < (b : ℝ) ∧ (b : ℝ) ≤ (s : ℝ) * y <;> simp [h]
  have hE : (if (s : ℝ) * y < (b : ℝ) then (ArithmeticFunction.moebius b : ℝ) *
      (∑ c ∈ (n / b).divisors, if z < (c : ℝ) ∧ (c : ℝ) ≤ (s : ℝ) * z then f c else 0)
      else 0)
      = (ArithmeticFunction.moebius b : ℝ) *
      (if (s : ℝ) * y < (b : ℝ) then
        (∑ c ∈ (n / b).divisors,
          if z < (c : ℝ) ∧ (c : ℝ) ≤ (s : ℝ) * z then f c else 0) else 0) := by
    by_cases h : (s : ℝ) * y < (b : ℝ) <;> simp [h]
  rw [hA, hB, hC, hD, hE, ← mul_sub, ← mul_add, ← mul_add, ← mul_add]
  congr 1
  exact sum_combine f (n / b).divisors y z hs hb
    (fun c hc => by have := Nat.pos_of_mem_divisors hc; omega)

theorem vaughan_decomposition_real (f : ℕ → ℝ) {n s : ℕ} (hn : 0 < n) (hs : 1 ≤ s)
    (y z : ℝ) :
    (if z < (n : ℝ) then f n else 0)
      = (∑ b ∈ n.divisors,
            if (b : ℝ) ≤ y then (ArithmeticFunction.moebius b : ℝ)
              * (∑ d ∈ (n / b).divisors, f d) else 0)
        - (∑ b ∈ n.divisors,
            if (b : ℝ) ≤ y then (ArithmeticFunction.moebius b : ℝ)
              * (∑ c ∈ (n / b).divisors, if (c : ℝ) ≤ z then f c else 0) else 0)
        + (∑ b ∈ n.divisors,
            if (s : ℝ) * y < (b : ℝ) then (ArithmeticFunction.moebius b : ℝ)
              * (∑ c ∈ (n / b).divisors, if (s : ℝ) * z < (c : ℝ) then f c else 0) else 0)
        + (∑ b ∈ n.divisors,
            if y < (b : ℝ) ∧ (b : ℝ) ≤ (s : ℝ) * y then (ArithmeticFunction.moebius b : ℝ)
              * (∑ c ∈ (n / b).divisors, if z < (c : ℝ) then f c else 0) else 0)
        + (∑ b ∈ n.divisors,
            if (s : ℝ) * y < (b : ℝ) then (ArithmeticFunction.moebius b : ℝ)
              * (∑ c ∈ (n / b).divisors, if z < (c : ℝ) ∧ (c : ℝ) ≤ (s : ℝ) * z then f c else 0)
            else 0) := by
  have hsum :
      (∑ b ∈ n.divisors,
            if (b : ℝ) ≤ y then (ArithmeticFunction.moebius b : ℝ)
              * (∑ d ∈ (n / b).divisors, f d) else 0)
        - (∑ b ∈ n.divisors,
            if (b : ℝ) ≤ y then (ArithmeticFunction.moebius b : ℝ)
              * (∑ c ∈ (n / b).divisors, if (c : ℝ) ≤ z then f c else 0) else 0)
        + (∑ b ∈ n.divisors,
            if (s : ℝ) * y < (b : ℝ) then (ArithmeticFunction.moebius b : ℝ)
              * (∑ c ∈ (n / b).divisors, if (s : ℝ) * z < (c : ℝ) then f c else 0) else 0)
        + (∑ b ∈ n.divisors,
            if y < (b : ℝ) ∧ (b : ℝ) ≤ (s : ℝ) * y then (ArithmeticFunction.moebius b : ℝ)
              * (∑ c ∈ (n / b).divisors, if z < (c : ℝ) then f c else 0) else 0)
        + (∑ b ∈ n.divisors,
            if (s : ℝ) * y < (b : ℝ) then (ArithmeticFunction.moebius b : ℝ)
              * (∑ c ∈ (n / b).divisors, if z < (c : ℝ) ∧ (c : ℝ) ≤ (s : ℝ) * z then f c else 0)
            else 0)
      = ∑ b ∈ n.divisors, (ArithmeticFunction.moebius b : ℝ) *
          (∑ c ∈ (n / b).divisors, (if z < (c : ℝ) then f c else 0)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    have hb1 : 1 ≤ b := by have := Nat.pos_of_mem_divisors hb; omega
    exact per_b y z hs hb1
  rw [hsum]
  have h2 : (∑ b ∈ n.divisors, (ArithmeticFunction.moebius b : ℝ) *
        (∑ c ∈ (n / b).divisors, (if z < (c : ℝ) then f c else 0)))
      = ∑ b ∈ n.divisors, ∑ c ∈ (n / b).divisors,
          (ArithmeticFunction.moebius b : ℝ) * (if z < (c : ℝ) then f c else 0) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
  rw [h2]
  exact (sum_mu_divisors_mul_truncated_real (f := f) hn z).symm

end Commons.NumberTheory.Sieve
import Mathlib
import Submission.Work.FIArea7.Classical172Defs
import Submission.Commons.NumberTheory.ArithmeticFunction.vonMangoldt_gt_vaughan_decomp
import Submission.Work.FIArea7.sum_Icc_divisors_swap_left
import Submission.Work.FIArea7.sum_Icc_divisors_double_le
import Submission.Work.FIArea7.sum_Icc_divisors_double_gt
import Submission.Work.FIArea7.sum_Icc_divisors_double_gt_range
import Submission.Work.FIArea7.sum_Icc_filter_Icc_le

namespace Work.FIArea7

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- The Vaughan decomposition of `Λ`, with the divisor-form filters, in `ℂ`. -/
theorem vaughan_decomp_complex (n Y : ℕ) (hn : 1 ≤ n) :
    ((if Y < n then (ArithmeticFunction.vonMangoldt n : ℝ) else 0 : ℝ) : ℂ)
      = (∑ b ∈ n.divisors.filter (fun b => b ≤ Y),
            (ArithmeticFunction.moebius b : ℂ) * ((Real.log ((n / b : ℕ) : ℝ)) : ℂ))
        - (∑ b ∈ n.divisors.filter (fun b => b ≤ Y),
            (ArithmeticFunction.moebius b : ℂ) *
              ∑ c ∈ (n / b).divisors.filter (fun c => c ≤ Y),
                ((ArithmeticFunction.vonMangoldt c : ℝ) : ℂ))
        + (∑ b ∈ n.divisors.filter (fun b => Y < b),
            (ArithmeticFunction.moebius b : ℂ) *
              ∑ c ∈ (n / b).divisors.filter (fun c => Y < c),
                ((ArithmeticFunction.vonMangoldt c : ℝ) : ℂ)) := by
  have h := Commons.NumberTheory.ArithmeticFunction.vonMangoldt_gt_vaughan_decomp n hn
      (y := (Y : ℝ)) (z := (Y : ℝ)) (sy := (Y : ℝ)) (sz := (Y : ℝ)) le_rfl le_rfl
  simp only [Nat.cast_lt, Nat.cast_le] at h
  have hC : (∑ b ∈ n.divisors.filter (fun b => Y < b ∧ b ≤ Y),
       (ArithmeticFunction.moebius b : ℝ) *
         ∑ c ∈ (n / b).divisors.filter (fun c => Y < c), ArithmeticFunction.vonMangoldt c) = 0 := by
    have hf : n.divisors.filter (fun b => Y < b ∧ b ≤ Y) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro b _ hb
      exact absurd hb.2 (not_le.mpr hb.1)
    rw [hf, Finset.sum_empty]
  have hD : (∑ b ∈ n.divisors.filter (fun b => Y < b),
       (ArithmeticFunction.moebius b : ℝ) *
         ∑ c ∈ (n / b).divisors.filter (fun c => Y < c ∧ c ≤ Y),
           ArithmeticFunction.vonMangoldt c) = 0 := by
    apply Finset.sum_eq_zero
    intro b _
    have hf : (n / b).divisors.filter (fun c => Y < c ∧ c ≤ Y) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro c _ hc
      exact absurd hc.2 (not_le.mpr hc.1)
    rw [hf, Finset.sum_empty, mul_zero]
  have key : (if Y < n then (ArithmeticFunction.vonMangoldt n : ℝ) else 0)
      = (∑ b ∈ n.divisors.filter (fun b => b ≤ Y),
            (ArithmeticFunction.moebius b : ℝ) * Real.log ((n / b : ℕ) : ℝ))
          - (∑ b ∈ n.divisors.filter (fun b => b ≤ Y),
              (ArithmeticFunction.moebius b : ℝ) *
                ∑ c ∈ (n / b).divisors.filter (fun c => c ≤ Y),
                  ArithmeticFunction.vonMangoldt c)
          + (∑ b ∈ n.divisors.filter (fun b => Y < b),
              (ArithmeticFunction.moebius b : ℝ) *
                ∑ c ∈ (n / b).divisors.filter (fun c => Y < c),
                  ArithmeticFunction.vonMangoldt c) := by
    rw [h, hC, hD]; ring
  rw [key]
  have e1 : ((∑ b ∈ n.divisors.filter (fun b => b ≤ Y),
        (ArithmeticFunction.moebius b : ℝ) * Real.log ((n / b : ℕ) : ℝ) : ℝ) : ℂ)
      = (∑ b ∈ n.divisors.filter (fun b => b ≤ Y),
          (ArithmeticFunction.moebius b : ℂ) * ((Real.log ((n / b : ℕ) : ℝ)) : ℂ)) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Complex.ofReal_mul]
    push_cast
    ring
  have e2 : ((∑ b ∈ n.divisors.filter (fun b => b ≤ Y),
        (ArithmeticFunction.moebius b : ℝ) *
          ∑ c ∈ (n / b).divisors.filter (fun c => c ≤ Y),
            ArithmeticFunction.vonMangoldt c : ℝ) : ℂ)
      = (∑ b ∈ n.divisors.filter (fun b => b ≤ Y),
          (ArithmeticFunction.moebius b : ℂ) *
            ∑ c ∈ (n / b).divisors.filter (fun c => c ≤ Y),
              ((ArithmeticFunction.vonMangoldt c : ℝ) : ℂ)) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Complex.ofReal_mul, Complex.ofReal_sum]
    push_cast
    ring
  have e3 : ((∑ b ∈ n.divisors.filter (fun b => Y < b),
        (ArithmeticFunction.moebius b : ℝ) *
          ∑ c ∈ (n / b).divisors.filter (fun c => Y < c),
            ArithmeticFunction.vonMangoldt c : ℝ) : ℂ)
      = (∑ b ∈ n.divisors.filter (fun b => Y < b),
          (ArithmeticFunction.moebius b : ℂ) *
            ∑ c ∈ (n / b).divisors.filter (fun c => Y < c),
              ((ArithmeticFunction.vonMangoldt c : ℝ) : ℂ)) := by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Complex.ofReal_mul, Complex.ofReal_sum]
    push_cast
    ring
  rw [Complex.ofReal_add, Complex.ofReal_sub, e1, e2, e3]

private lemma S0_eq (N Y c : ℕ) (psi : GaussianInt → ℂ) (hYN : Y ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
        ((if n ≤ Y then (ArithmeticFunction.vonMangoldt n : ℝ) else 0 : ℝ) : ℂ) *
          quadEigen psi (c * n))
      = ∑ n ∈ Finset.Icc 1 Y,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * quadEigen psi (c * n) := by
  have h1 : (∑ n ∈ (Finset.Icc 1 N).filter (fun n => n ≤ Y),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * quadEigen psi (c * n))
      = ∑ n ∈ Finset.Icc 1 N,
          ((if n ≤ Y then (ArithmeticFunction.vonMangoldt n : ℝ) else 0 : ℝ) : ℂ) *
            quadEigen psi (c * n) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : n ≤ Y <;> simp [h]
  rw [← h1]
  exact sum_Icc_filter_Icc_le N Y hYN _

private lemma S1_eq (N Y c : ℕ) (psi : GaussianInt → ℂ) :
    (∑ n ∈ Finset.Icc 1 N,
        (∑ a ∈ n.divisors.filter (fun a => a ≤ Y),
            (ArithmeticFunction.moebius a : ℂ) *
              ((Real.log ((n / a : ℕ) : ℝ)) : ℂ)) * quadEigen psi (c * n))
      = ∑ a ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius a : ℂ) *
          ∑ m ∈ Finset.Icc 1 (N / a),
            ((Real.log m : ℝ) : ℂ) * quadEigen psi (c * (a * m)) := by
  let G : ℕ → ℕ → ℂ := fun a n => (ArithmeticFunction.moebius a : ℂ) *
      ((Real.log ((n / a : ℕ) : ℝ)) : ℂ) * quadEigen psi (c * n)
  have h1 : (∑ n ∈ Finset.Icc 1 N,
        (∑ a ∈ n.divisors.filter (fun a => a ≤ Y),
            (ArithmeticFunction.moebius a : ℂ) *
              ((Real.log ((n / a : ℕ) : ℝ)) : ℂ)) * quadEigen psi (c * n))
      = ∑ n ∈ Finset.Icc 1 N, ∑ a ∈ n.divisors.filter (fun a => a ≤ Y), G a n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.sum_mul]
  have h2 := sum_Icc_divisors_swap_left N Y G
  have h3 : (∑ a ∈ Finset.Icc 1 Y, ∑ m ∈ Finset.Icc 1 (N / a), G a (a * m))
      = ∑ a ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius a : ℂ) *
          ∑ m ∈ Finset.Icc 1 (N / a),
            ((Real.log m : ℝ) : ℂ) * quadEigen psi (c * (a * m)) := by
    apply Finset.sum_congr rfl
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    simp only [G]
    rw [Nat.mul_div_right m (by omega : 0 < a)]
    ring
  exact h1.trans (h2.trans h3)

private lemma S2_eq (N Y c : ℕ) (psi : GaussianInt → ℂ) :
    (∑ n ∈ Finset.Icc 1 N,
        (∑ a ∈ n.divisors.filter (fun a => a ≤ Y),
            (ArithmeticFunction.moebius a : ℂ) *
              ∑ b ∈ (n / a).divisors.filter (fun b => b ≤ Y),
                ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ)) * quadEigen psi (c * n))
      = ∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y,
          (ArithmeticFunction.moebius a : ℂ) * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) *
            ∑ m ∈ Finset.Icc 1 (N / (a * b)), quadEigen psi (c * (a * b * m)) := by
  let G : ℕ → ℕ → ℕ → ℂ := fun a b n => (ArithmeticFunction.moebius a : ℂ) *
      ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) * quadEigen psi (c * n)
  have h1 : (∑ n ∈ Finset.Icc 1 N,
        (∑ a ∈ n.divisors.filter (fun a => a ≤ Y),
            (ArithmeticFunction.moebius a : ℂ) *
              ∑ b ∈ (n / a).divisors.filter (fun b => b ≤ Y),
                ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ)) * quadEigen psi (c * n))
      = ∑ n ∈ Finset.Icc 1 N, ∑ a ∈ n.divisors.filter (fun a => a ≤ Y),
          ∑ b ∈ (n / a).divisors.filter (fun b => b ≤ Y), G a b n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum, Finset.sum_mul]
  have h2 := sum_Icc_divisors_double_le N Y G
  have h3 : (∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y,
        ∑ m ∈ Finset.Icc 1 (N / (a * b)), G a b (a * b * m))
      = ∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y,
          (ArithmeticFunction.moebius a : ℂ) * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) *
            ∑ m ∈ Finset.Icc 1 (N / (a * b)), quadEigen psi (c * (a * b * m)) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [G]
    rw [Finset.mul_sum]
  exact h1.trans (h2.trans h3)

private lemma S3_eq (N Y c : ℕ) (psi : GaussianInt → ℂ) (hY1 : 1 ≤ Y) :
    (∑ n ∈ Finset.Icc 1 N,
        (∑ a ∈ n.divisors.filter (fun a => Y < a),
            (ArithmeticFunction.moebius a : ℂ) *
              ∑ b ∈ (n / a).divisors.filter (fun b => Y < b),
                ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ)) * quadEigen psi (c * n))
      = ∑ a ∈ Finset.Icc (Y + 1) (N / Y), (ArithmeticFunction.moebius a : ℂ) *
          ∑ n ∈ Finset.Icc 1 (N / a),
            (∑ b ∈ n.divisors.filter (fun b => Y < b),
                ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ)) *
              quadEigen psi (c * (a * n)) := by
  let G : ℕ → ℕ → ℕ → ℂ := fun a b n => (ArithmeticFunction.moebius a : ℂ) *
      ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) * quadEigen psi (c * n)
  have h1 : (∑ n ∈ Finset.Icc 1 N,
        (∑ a ∈ n.divisors.filter (fun a => Y < a),
            (ArithmeticFunction.moebius a : ℂ) *
              ∑ b ∈ (n / a).divisors.filter (fun b => Y < b),
                ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ)) * quadEigen psi (c * n))
      = ∑ n ∈ Finset.Icc 1 N, ∑ a ∈ n.divisors.filter (fun a => Y < a),
          ∑ b ∈ (n / a).divisors.filter (fun b => Y < b), G a b n := by
    apply Finset.sum_congr rfl
    intro n _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum, Finset.sum_mul]
  have h2 := sum_Icc_divisors_double_gt N Y G
  have h3 := sum_Icc_divisors_double_gt_range N Y hY1 G
  have h4 : (∑ a ∈ Finset.Icc (Y + 1) (N / Y), ∑ m ∈ Finset.Icc 1 (N / a),
        ∑ b ∈ m.divisors.filter (fun b => Y < b), G a b (a * m))
      = ∑ a ∈ Finset.Icc (Y + 1) (N / Y), (ArithmeticFunction.moebius a : ℂ) *
          ∑ n ∈ Finset.Icc 1 (N / a),
            (∑ b ∈ n.divisors.filter (fun b => Y < b),
                ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ)) *
              quadEigen psi (c * (a * n)) := by
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    simp only [G]
    ring
  exact h1.trans (h2.trans (h3.trans h4))

-- `Submission.Work.FIArea7.vaughan_identity` gives, for `Y < n`,
-- `Λ n = ∑_{a ∣ n, a ≤ Y} μ a · log(n/a) − ∑_{a,b ≤ Y, ab ∣ n} μ a · Λ b + ∑_{a,b > Y, ab ∣ n} μ a · Λ b`
-- and its right hand side vanishes for `n ≤ Y`.  Subtracting, `Λ n = Λ n·[n ≤ Y] + RHS_n` for every
-- `n ≤ N` (use `Y ≤ N` for the `S₀` range, and `1 ≤ Y` so that the `S₃` range `Icc (Y+1) (N/Y)` is
-- the correct one).  Then sum over `n ≤ N` and perform the three divisor swaps
-- (`∑_{n≤N} ∑_{a|n, a≤Y} = ∑_{a≤Y} ∑_{m≤N/a}`, and `n = a·b·m` in the last two terms).
/-- **The Vaughan splitting of `∑_{n ≤ N} Λ(n) λ(cn)` into `S₀ + S₁ - S₂ + S₃`** for `1 ≤ Y ≤ N`,
with `S₀ = ∑_{n≤Y}`, `S₁ = ∑_{a≤Y} μ(a) ∑_{m≤N/a} log m λ(cam)`,
`S₂ = ∑_{a,b≤Y} μ(a)Λ(b) ∑_{m≤N/(ab)} λ(c(ab)m)` and
`S₃ = ∑_{Y<a≤N/Y} μ(a) ∑_{n≤N/a} (∑_{b|n, b>Y} Λ b) λ(can)`. -/
theorem t2psi_vaughan_split (N Y c : ℕ) (psi : GaussianInt → ℂ) (hY1 : 1 ≤ Y) (hYN : Y ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * Work.FIArea7.quadEigen psi (c * n))
      = (∑ n ∈ Finset.Icc 1 Y,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * Work.FIArea7.quadEigen psi (c * n))
        + (∑ a ∈ Finset.Icc 1 Y, (ArithmeticFunction.moebius a : ℂ) *
            ∑ m ∈ Finset.Icc 1 (N / a),
              ((Real.log m : ℝ) : ℂ) * Work.FIArea7.quadEigen psi (c * (a * m)))
        - (∑ a ∈ Finset.Icc 1 Y, ∑ b ∈ Finset.Icc 1 Y,
            (ArithmeticFunction.moebius a : ℂ) * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ) *
              ∑ m ∈ Finset.Icc 1 (N / (a * b)),
                Work.FIArea7.quadEigen psi (c * ((a * b) * m)))
        + (∑ a ∈ Finset.Icc (Y + 1) (N / Y), (ArithmeticFunction.moebius a : ℂ) *
            ∑ n ∈ Finset.Icc 1 (N / a),
              (∑ b ∈ n.divisors.filter (fun b => Y < b),
                  ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ)) *
                Work.FIArea7.quadEigen psi (c * (a * n))) := by
  have hpt : ∀ n ∈ Finset.Icc 1 N,
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * quadEigen psi (c * n)
      = ((if n ≤ Y then (ArithmeticFunction.vonMangoldt n : ℝ) else 0 : ℝ) : ℂ) *
            quadEigen psi (c * n)
        + (((∑ a ∈ n.divisors.filter (fun a => a ≤ Y),
                (ArithmeticFunction.moebius a : ℂ) *
                  ((Real.log ((n / a : ℕ) : ℝ)) : ℂ)) * quadEigen psi (c * n)
              - (∑ a ∈ n.divisors.filter (fun a => a ≤ Y),
                  (ArithmeticFunction.moebius a : ℂ) *
                    ∑ b ∈ (n / a).divisors.filter (fun b => b ≤ Y),
                      ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ)) * quadEigen psi (c * n)
              + (∑ a ∈ n.divisors.filter (fun a => Y < a),
                  (ArithmeticFunction.moebius a : ℂ) *
                    ∑ b ∈ (n / a).divisors.filter (fun b => Y < b),
                      ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ)) * quadEigen psi (c * n))) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hd := vaughan_decomp_complex n Y hn1
    have hsplit : ((if n ≤ Y then (ArithmeticFunction.vonMangoldt n : ℝ) else 0 : ℝ) : ℂ)
        + ((if Y < n then (ArithmeticFunction.vonMangoldt n : ℝ) else 0 : ℝ) : ℂ)
        = ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) := by
      by_cases h : Y < n
      · rw [if_neg (not_le.mpr h), if_pos h]; simp
      · rw [if_pos (not_lt.mp h), if_neg h]; simp
    rw [← hsplit, hd]
    ring
  have hsum := Finset.sum_congr rfl hpt
  rw [hsum, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [S0_eq N Y c psi hYN, S1_eq N Y c psi, S2_eq N Y c psi, S3_eq N Y c psi hY1]
  ring

end Work.FIArea7

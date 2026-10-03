import Mathlib
import Submission.Commons.Analysis.Summation.sum_Icc_one_eq_range

/-!
# The tail integrand for the Fourier series of `-log(2 |sin(α/2)|)`

We set up the elementary identity

`∑_{n=1}^K cos(nα)/n = -log(2|sin(α/2)|) - ∫_0^1 P α K x dx`

where `P α n x = x^n (cos((n+1)α) - x cos(nα)) / (1 - 2x cos α + x²)`.
This file contains the algebraic (non-analytic) part of that identity.
-/

namespace Work.FIArea7

open scoped BigOperators

/-- `Q α x = 1 - 2 x cos α + x² = |1 - x e^{iα}|²`. -/
noncomputable def Q (α x : ℝ) : ℝ := 1 - 2 * x * Real.cos α + x ^ 2

/-- The `n`-th tail integrand `x^n (cos((n+1)α) - x cos(nα)) / Q α x`. -/
noncomputable def P (α : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n * (Real.cos (((n : ℝ) + 1) * α) - x * Real.cos ((n : ℝ) * α)) / Q α x

lemma cos_add_cos_sub (θ α : ℝ) :
    Real.cos (θ + α) + Real.cos (θ - α) = 2 * Real.cos θ * Real.cos α := by
  rw [Real.cos_add, Real.cos_sub]; ring

lemma one_sub_cos (α : ℝ) : 1 - Real.cos α = 2 * Real.sin (α / 2) ^ 2 := by
  have h := Real.cos_two_mul (α / 2)
  rw [show 2 * (α / 2) = α by ring] at h
  have h2 := Real.cos_sq_add_sin_sq (α / 2)
  nlinarith [h, h2]

lemma Q_eq (α x : ℝ) : Q α x = (1 - x) ^ 2 + 4 * x * Real.sin (α / 2) ^ 2 := by
  unfold Q
  linear_combination (2 * x) * (one_sub_cos α)

lemma Q_zero (α : ℝ) : Q α 0 = 1 := by unfold Q; ring

lemma Q_one (α : ℝ) : Q α 1 = 4 * Real.sin (α / 2) ^ 2 := by
  unfold Q; linear_combination 2 * (one_sub_cos α)

lemma Q_pos (α x : ℝ) (hs : Real.sin (α / 2) ≠ 0) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    0 < Q α x := by
  rw [Q_eq]
  rcases eq_or_lt_of_le h0 with hx | hx
  · subst hx; norm_num
  · have h2 : 0 < Real.sin (α / 2) ^ 2 := sq_pos_of_ne_zero hs
    nlinarith [h2, hx, sq_nonneg (1 - x)]

lemma Q_ne_zero (α x : ℝ) (hs : Real.sin (α / 2) ≠ 0) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Q α x ≠ 0 := (Q_pos α x hs h0 h1).ne'

lemma P_zero (α x : ℝ) :
    P α 0 x = (Real.cos α - x) / Q α x := by
  unfold P
  simp

lemma P_succ_sub (α x : ℝ) (n : ℕ) (hQ : Q α x ≠ 0) :
    P α (n + 1) x - P α n x = -x ^ n * Real.cos (((n : ℝ) + 1) * α) := by
  have htrig : Real.cos (↑n * α + α + α) + Real.cos (↑n * α)
      = 2 * Real.cos (↑n * α + α) * Real.cos α := by
    have h := cos_add_cos_sub (↑n * α + α) α
    rw [show (↑n * α + α) + α = ↑n * α + α + α by ring,
      show (↑n * α + α) - α = ↑n * α by ring] at h
    exact h
  have hbase : x * (Real.cos (↑n * α + α + α) - x * Real.cos (↑n * α + α))
      - (Real.cos (↑n * α + α) - x * Real.cos (↑n * α))
      = -Real.cos (↑n * α + α) * (1 - 2 * x * Real.cos α + x ^ 2) := by
    have h' : Real.cos (↑n * α + α + α)
        = 2 * Real.cos (↑n * α + α) * Real.cos α - Real.cos (↑n * α) := by linarith
    rw [h']; ring
  have hnum : x ^ (n + 1) * (Real.cos (↑n * α + α + α) - x * Real.cos (↑n * α + α))
      - x ^ n * (Real.cos (↑n * α + α) - x * Real.cos (↑n * α))
      = -x ^ n * Real.cos (↑n * α + α) * (1 - 2 * x * Real.cos α + x ^ 2) := by
    rw [pow_succ]
    calc x ^ n * x * (Real.cos (↑n * α + α + α) - x * Real.cos (↑n * α + α))
          - x ^ n * (Real.cos (↑n * α + α) - x * Real.cos (↑n * α))
        = x ^ n * (x * (Real.cos (↑n * α + α + α) - x * Real.cos (↑n * α + α))
            - (Real.cos (↑n * α + α) - x * Real.cos (↑n * α))) := by ring
      _ = x ^ n * (-Real.cos (↑n * α + α) * (1 - 2 * x * Real.cos α + x ^ 2)) := by
            rw [hbase]
      _ = -x ^ n * Real.cos (↑n * α + α) * (1 - 2 * x * Real.cos α + x ^ 2) := by ring
  unfold P
  simp only [Nat.cast_add, Nat.cast_one]
  rw [show (↑n + 1 + 1) * α = ↑n * α + α + α by ring]
  rw [show (↑n + 1) * α = ↑n * α + α by ring]
  rw [div_sub_div_same, div_eq_iff hQ]
  rw [hnum]
  unfold Q
  ring

/-- Telescoping: the partial sum of the Fourier series is `P α 0 - P α K`. -/
lemma P_tele (α : ℝ) (K : ℕ) (x : ℝ) (hQ : Q α x ≠ 0) :
    (∑ n ∈ Finset.Icc 1 K, x ^ (n - 1) * Real.cos ((n : ℝ) * α)) = P α 0 x - P α K x := by
  rw [Commons.Analysis.Summation.sum_Icc_one_eq_range]
  have hshift : ∀ k : ℕ, x ^ (k + 1 - 1) * Real.cos (((k + 1 : ℕ) : ℝ) * α)
      = x ^ k * Real.cos (((k : ℝ) + 1) * α) := by
    intro k
    rw [Nat.add_sub_cancel]
    congr 1
    push_cast
    ring
  simp only [hshift]
  have hstep : ∀ k : ℕ, P α (k + 1) x - P α k x = -(x ^ k * Real.cos (((k : ℝ) + 1) * α)) := by
    intro k
    rw [P_succ_sub α x k hQ]
    ring
  calc (∑ k ∈ Finset.range K, x ^ k * Real.cos (((k : ℝ) + 1) * α))
      = ∑ k ∈ Finset.range K, -(P α (k + 1) x - P α k x) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hstep k]; ring
    _ = -(∑ k ∈ Finset.range K, (P α (k + 1) x - P α k x)) := by
        rw [Finset.sum_neg_distrib]
    _ = -(P α K x - P α 0 x) := by rw [Finset.sum_range_sub (fun n => P α n x) K]
    _ = P α 0 x - P α K x := by ring

end Work.FIArea7

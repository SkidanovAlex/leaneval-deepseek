import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base
import Submission.Work.OffAxis.G72MomentClosed
import Submission.Work.ZeroFreeTables.tf72_exp_taylor_upper

open scoped Interval BigOperators
open MeasureTheory

namespace Work.OffAxis.Tf72One

/-! ## Auxiliary integral evaluations

We evaluate `∫₀² y² · P(y) · g72 y dy` for polynomials `P` given as a finite sum of
monomials, in terms of the moments `∫₀² y^n g72 y` of `g72` (supplied by
`Work.OffAxis.G72MomentClosed`). -/

/-- `∫₀² y² · (∑_{m<N} c_m y^m) · g72 y dy = ∑_{m<N} c_m ∫₀² y^{m+2} g72 y dy`. -/
lemma integral_y2_sum_g72 (c : ℕ → ℝ) (N : ℕ) :
    ∫ y in (0:ℝ)..2, y^2 * (∑ m ∈ Finset.range N, c m * y^m) * Work.ZeroFreeTables.g72 y
      = ∑ m ∈ Finset.range N, c m * (∫ y in (0:ℝ)..2, y^(m+2) * Work.ZeroFreeTables.g72 y) := by
  have hpt : ∀ y : ℝ, y^2 * (∑ m ∈ Finset.range N, c m * y^m) * Work.ZeroFreeTables.g72 y
      = ∑ m ∈ Finset.range N, c m * (y^(m+2) * Work.ZeroFreeTables.g72 y) := by
    intro y
    rw [show y^2 * (∑ m ∈ Finset.range N, c m * y^m) * Work.ZeroFreeTables.g72 y
        = (∑ m ∈ Finset.range N, c m * y^m) * (y^2 * Work.ZeroFreeTables.g72 y) by ring,
      Finset.sum_mul]
    refine Finset.sum_congr rfl ?_
    intro m _
    have hm : y^m * y^2 = y^(m+2) := by rw [← pow_add]
    calc c m * y^m * (y^2 * Work.ZeroFreeTables.g72 y)
        = c m * (y^m * y^2) * Work.ZeroFreeTables.g72 y := by ring
      _ = c m * (y^(m+2) * Work.ZeroFreeTables.g72 y) := by rw [hm]; ring
  rw [intervalIntegral.integral_congr (fun y _ => hpt y)]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl ?_
    intro m _
    rw [intervalIntegral.integral_const_mul]
  · intro i _
    exact Continuous.intervalIntegrable (by simp only [Work.ZeroFreeTables.g72]; fun_prop) 0 2

/-- The shifted moments of `g72`: `∫₀² y^{m+2} g72 y dy` in closed form. -/
lemma moment_shift (m : ℕ) :
    (∫ y in (0:ℝ)..2, y^(m+2) * Work.ZeroFreeTables.g72 y)
      = (16 * (2:ℝ)^(m+3) / 15) * (1/((m:ℝ)+3) - 5/((m:ℝ)+5) + 5/((m:ℝ)+6) - 1/((m:ℝ)+8)) := by
  rw [Work.OffAxis.G72MomentClosed (m+2)]
  push_cast
  norm_num
  ring

/-- `∫₀² y² · ((∑_{m<N} c_m y^m) + d y^N) · g72 y dy` evaluated through the moments. -/
lemma integral_y2_P_g72 (c : ℕ → ℝ) (d : ℝ) (N : ℕ) :
    ∫ y in (0:ℝ)..2, y^2 * ((∑ m ∈ Finset.range N, c m * y^m) + d * y^N) * Work.ZeroFreeTables.g72 y
      = (∑ m ∈ Finset.range N, c m * (∫ y in (0:ℝ)..2, y^(m+2) * Work.ZeroFreeTables.g72 y))
        + d * (∫ y in (0:ℝ)..2, y^(N+2) * Work.ZeroFreeTables.g72 y) := by
  have hpt : ∀ y : ℝ, y^2 * ((∑ m ∈ Finset.range N, c m * y^m) + d * y^N) * Work.ZeroFreeTables.g72 y
      = (∑ m ∈ Finset.range N, c m * (y^(m+2) * Work.ZeroFreeTables.g72 y))
        + d * (y^(N+2) * Work.ZeroFreeTables.g72 y) := by
    intro y
    have hsum : y^2 * (∑ m ∈ Finset.range N, c m * y^m) * Work.ZeroFreeTables.g72 y
        = ∑ m ∈ Finset.range N, c m * (y^(m+2) * Work.ZeroFreeTables.g72 y) := by
      rw [show y^2 * (∑ m ∈ Finset.range N, c m * y^m) * Work.ZeroFreeTables.g72 y
          = (∑ m ∈ Finset.range N, c m * y^m) * (y^2 * Work.ZeroFreeTables.g72 y) by ring,
        Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro m _
      have hm : y^m * y^2 = y^(m+2) := by rw [← pow_add]
      calc c m * y^m * (y^2 * Work.ZeroFreeTables.g72 y)
          = c m * (y^m * y^2) * Work.ZeroFreeTables.g72 y := by ring
        _ = c m * (y^(m+2) * Work.ZeroFreeTables.g72 y) := by rw [hm]; ring
    have hd : y^2 * (d * y^N) * Work.ZeroFreeTables.g72 y
        = d * (y^(N+2) * Work.ZeroFreeTables.g72 y) := by
      have hN : y^N * y^2 = y^(N+2) := by rw [← pow_add]
      calc y^2 * (d * y^N) * Work.ZeroFreeTables.g72 y
          = d * (y^N * y^2) * Work.ZeroFreeTables.g72 y := by ring
        _ = d * (y^(N+2) * Work.ZeroFreeTables.g72 y) := by rw [hN]; ring
    rw [show y^2 * ((∑ m ∈ Finset.range N, c m * y^m) + d * y^N) * Work.ZeroFreeTables.g72 y
        = y^2 * (∑ m ∈ Finset.range N, c m * y^m) * Work.ZeroFreeTables.g72 y
          + y^2 * (d * y^N) * Work.ZeroFreeTables.g72 y by ring, hsum, hd]
  rw [intervalIntegral.integral_congr (fun y _ => hpt y)]
  have hint1 : IntervalIntegrable
      (fun y : ℝ => ∑ m ∈ Finset.range N, c m * (y^(m+2) * Work.ZeroFreeTables.g72 y))
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]; fun_prop
  have hint2 : IntervalIntegrable (fun y : ℝ => d * (y^(N+2) * Work.ZeroFreeTables.g72 y))
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]; fun_prop
  rw [intervalIntegral.integral_add hint1 hint2]
  rw [intervalIntegral.integral_finsetSum (E := ℝ) (μ := volume) (a := 0) (b := 2) (s := Finset.range N)
      (f := fun m (y : ℝ) => c m * (y^(m+2) * Work.ZeroFreeTables.g72 y))
      (fun i _ => by apply Continuous.intervalIntegrable; simp only [Work.ZeroFreeTables.g72]; fun_prop)]
  simp only [intervalIntegral.integral_const_mul]

/-- `∫₀² y² e^{sy} g72 y dy ≤ 13/10` for `0 ≤ s ≤ 17/16` (the `s`-second-derivative bound for the
Lemma 7.2 Laplace transform at `λ = 1`, `g72 y = (1/30)(2-y)³(4+6y+y²)`). -/
theorem Mss_bound (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 17/16) :
    ∫ y in (0:ℝ)..2, y ^ 2 * Real.exp (s * y) * Work.ZeroFreeTables.g72 y ≤ 13/10 := by
  -- the integrand is increasing in `s` on `[0,2]`, so it suffices to consider `s = 17/16`
  have hcontG : Continuous (fun y : ℝ => Work.ZeroFreeTables.g72 y) := by
    simp only [Work.ZeroFreeTables.g72]; fun_prop
  have hintS : IntervalIntegrable
      (fun y : ℝ => y^2 * Real.exp (s*y) * Work.ZeroFreeTables.g72 y) volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]; fun_prop
  have hintU : IntervalIntegrable
      (fun y : ℝ => y^2 * Real.exp ((17/16)*y) * Work.ZeroFreeTables.g72 y) volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]; fun_prop
  have hmono1 : ∫ y in (0:ℝ)..2, y ^ 2 * Real.exp (s * y) * Work.ZeroFreeTables.g72 y
      ≤ ∫ y in (0:ℝ)..2, y ^ 2 * Real.exp ((17/16) * y) * Work.ZeroFreeTables.g72 y := by
    refine intervalIntegral.integral_mono_on (by norm_num) hintS hintU ?_
    intro y hy
    have hy0 : 0 ≤ y := hy.1
    have hgy : 0 ≤ Work.ZeroFreeTables.g72 y := Work.ZeroFreeTables.OffAxis.g72_nonneg hy.1 hy.2
    have hexp : Real.exp (s * y) ≤ Real.exp ((17/16) * y) :=
      Real.exp_le_exp.mpr (by nlinarith)
    calc y ^ 2 * Real.exp (s * y) * Work.ZeroFreeTables.g72 y
        = (y^2 * Work.ZeroFreeTables.g72 y) * Real.exp (s * y) := by ring
      _ ≤ (y^2 * Work.ZeroFreeTables.g72 y) * Real.exp ((17/16) * y) :=
            mul_le_mul_of_nonneg_left hexp (mul_nonneg (sq_nonneg y) hgy)
      _ = y ^ 2 * Real.exp ((17/16) * y) * Work.ZeroFreeTables.g72 y := by ring
  -- the degree-9 Taylor upper bound for `exp` on `[0,17/8]`
  set Poly : ℝ → ℝ := fun y => (∑ m ∈ Finset.range 9,
        ((17/16:ℝ)^m / ((m.factorial : ℕ) : ℝ)) * y^m)
      + (2 * (17/16:ℝ)^9 / ((Nat.factorial 9 : ℕ) : ℝ)) * y^9 with hPoly
  have hPe : ∀ y ∈ Set.Icc (0:ℝ) 2, Real.exp ((17/16) * y) ≤ Poly y := by
    intro y hy
    have h := Work.ZeroFreeTables.tf72_exp_taylor_upper ((17/16) * y)
      (mul_nonneg (by norm_num) hy.1) (by nlinarith [hy.2])
    rw [hPoly]
    refine le_trans h ?_
    have hsum : (∑ m ∈ Finset.range 9, ((17/16) * y)^m / ((m.factorial : ℕ) : ℝ))
        = ∑ m ∈ Finset.range 9, ((17/16:ℝ)^m / ((m.factorial : ℕ) : ℝ)) * y^m := by
      refine Finset.sum_congr rfl ?_
      intro m _
      rw [mul_pow]; ring
    have h9 : 2 * ((17/16) * y)^9 / ((Nat.factorial 9 : ℕ) : ℝ)
        = (2 * (17/16:ℝ)^9 / ((Nat.factorial 9 : ℕ) : ℝ)) * y^9 := by
      rw [mul_pow]; ring
    rw [hsum, h9]
  have hcontPoly : Continuous Poly := by
    rw [hPoly]; fun_prop
  have hintP : IntervalIntegrable
      (fun y : ℝ => y^2 * Poly y * Work.ZeroFreeTables.g72 y) volume (0:ℝ) 2 :=
    Continuous.intervalIntegrable (((continuous_id.pow 2).mul hcontPoly).mul hcontG) 0 2
  have hmono2 : ∫ y in (0:ℝ)..2, y ^ 2 * Real.exp ((17/16) * y) * Work.ZeroFreeTables.g72 y
      ≤ ∫ y in (0:ℝ)..2, y^2 * Poly y * Work.ZeroFreeTables.g72 y := by
    refine intervalIntegral.integral_mono_on (by norm_num) hintU hintP ?_
    intro y hy
    have hgy : 0 ≤ Work.ZeroFreeTables.g72 y := Work.ZeroFreeTables.OffAxis.g72_nonneg hy.1 hy.2
    have h1 : Real.exp ((17/16) * y) ≤ Poly y := hPe y hy
    calc y ^ 2 * Real.exp ((17/16) * y) * Work.ZeroFreeTables.g72 y
        = (y^2 * Work.ZeroFreeTables.g72 y) * Real.exp ((17/16) * y) := by ring
      _ ≤ (y^2 * Work.ZeroFreeTables.g72 y) * Poly y :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg (sq_nonneg y) hgy)
      _ = y^2 * Poly y * Work.ZeroFreeTables.g72 y := by ring
  have hval : ∫ y in (0:ℝ)..2, y^2 * Poly y * Work.ZeroFreeTables.g72 y
      = (∑ m ∈ Finset.range 9, ((17/16:ℝ)^m / ((m.factorial : ℕ) : ℝ)) *
          (∫ y in (0:ℝ)..2, y^(m+2) * Work.ZeroFreeTables.g72 y))
        + (2 * (17/16:ℝ)^9 / ((Nat.factorial 9 : ℕ) : ℝ)) *
          (∫ y in (0:ℝ)..2, y^(9+2) * Work.ZeroFreeTables.g72 y) := by
    rw [hPoly]
    exact integral_y2_P_g72 (fun m => (17/16:ℝ)^m / ((m.factorial : ℕ) : ℝ))
      (2 * (17/16:ℝ)^9 / ((Nat.factorial 9 : ℕ) : ℝ)) 9
  have hfinal : (∑ m ∈ Finset.range 9, ((17/16:ℝ)^m / ((m.factorial : ℕ) : ℝ)) *
          (∫ y in (0:ℝ)..2, y^(m+2) * Work.ZeroFreeTables.g72 y))
        + (2 * (17/16:ℝ)^9 / ((Nat.factorial 9 : ℕ) : ℝ)) *
          (∫ y in (0:ℝ)..2, y^(9+2) * Work.ZeroFreeTables.g72 y) ≤ 13/10 := by
    have hsum : (∑ m ∈ Finset.range 9, ((17/16:ℝ)^m / ((m.factorial : ℕ) : ℝ)) *
          (∫ y in (0:ℝ)..2, y^(m+2) * Work.ZeroFreeTables.g72 y))
        = ∑ m ∈ Finset.range 9, ((17/16:ℝ)^m / ((m.factorial : ℕ) : ℝ)) *
          ((16 * (2:ℝ)^(m+3) / 15) *
            (1/((m:ℝ)+3) - 5/((m:ℝ)+5) + 5/((m:ℝ)+6) - 1/((m:ℝ)+8))) := by
      refine Finset.sum_congr rfl ?_
      intro m _
      rw [moment_shift m]
    rw [hsum, Work.OffAxis.G72MomentClosed (9+2)]
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero]
  calc ∫ y in (0:ℝ)..2, y ^ 2 * Real.exp (s * y) * Work.ZeroFreeTables.g72 y
      ≤ ∫ y in (0:ℝ)..2, y ^ 2 * Real.exp ((17/16) * y) * Work.ZeroFreeTables.g72 y := hmono1
    _ ≤ ∫ y in (0:ℝ)..2, y^2 * Poly y * Work.ZeroFreeTables.g72 y := hmono2
    _ = (∑ m ∈ Finset.range 9, ((17/16:ℝ)^m / ((m.factorial : ℕ) : ℝ)) *
          (∫ y in (0:ℝ)..2, y^(m+2) * Work.ZeroFreeTables.g72 y))
        + (2 * (17/16:ℝ)^9 / ((Nat.factorial 9 : ℕ) : ℝ)) *
          (∫ y in (0:ℝ)..2, y^(9+2) * Work.ZeroFreeTables.g72 y) := hval
    _ ≤ 13/10 := hfinal

end Work.OffAxis.Tf72One

import Mathlib
import Submission.Work.WilkiesH.Interp.V2Params

namespace Work.WilkiesH.Interp.V2dV

open Work.WilkiesH.Interp

/-- The `(μ+1)`-st root of `RR μ g b` splits as the product of the `(μ+1)`-st root of the
part not involving `b` and the power `(b+1)^(μ/(μ+1))`. -/
lemma rpow_RR (μ g b : ℕ) :
    ((RR μ g b : ℕ) : ℝ) ^ (1 / ((μ : ℝ) + 1)) =
      ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) ^ (1 / ((μ : ℝ) + 1)) *
        ((b : ℝ) + 1) ^ ((μ : ℝ) / ((μ : ℝ) + 1)) := by
  have hR : ((RR μ g b : ℕ) : ℝ) =
      ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) * ((b : ℝ) + 1) ^ (μ : ℕ) := by
    simp only [RR]; push_cast; ring
  have hb1 : (0 : ℝ) ≤ (b : ℝ) + 1 := by positivity
  rw [hR, Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hb1]
  congr 1
  field_simp

-- `dV μ g b` is `⌈(((μ+1)! (8g+9) (b+1)^μ))^(1/(μ+1))⌉ + 1`; the goal is the
-- corresponding upper bound.
theorem dV_upper (μ g b : ℕ) :
    ((Work.WilkiesH.Interp.dV μ g b : ℕ) : ℝ) ≤
      8 * ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) ^ (1 / ((μ : ℝ) + 1)) *
        ((b : ℝ) + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1)) := by
  have hfact1 : (1 : ℝ) ≤ (((μ + 1).factorial : ℕ) : ℝ) := by
    exact_mod_cast (Nat.factorial_pos (μ + 1))
  have hg : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg g
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  have hA1 : 1 ≤ ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) := by
    nlinarith [hfact1, hg]
  have hmu : (0 : ℝ) ≤ (μ : ℝ) / ((μ : ℝ) + 1) := by positivity
  have hb2 : (1 : ℝ) ≤ (b : ℝ) + 2 := by linarith
  have hP1 : 1 ≤ ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) ^ (1 / ((μ : ℝ) + 1)) *
        ((b : ℝ) + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1)) := by
    have h1 : (1 : ℝ) ≤ ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) ^
        (1 / ((μ : ℝ) + 1)) := Real.one_le_rpow hA1 (by positivity)
    have h2 : (1 : ℝ) ≤ ((b : ℝ) + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1)) :=
      Real.one_le_rpow hb2 hmu
    nlinarith [h1, h2]
  have hmono : ((b : ℝ) + 1) ^ ((μ : ℝ) / ((μ : ℝ) + 1)) ≤
      ((b : ℝ) + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1)) :=
    Real.rpow_le_rpow (by positivity) (by linarith) hmu
  rw [dV]
  have hx0 : 0 ≤ ((RR μ g b : ℕ) : ℝ) ^ (1 / ((μ : ℝ) + 1)) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hceil : ((Nat.ceil (((RR μ g b : ℕ) : ℝ) ^ (1 / ((μ : ℝ) + 1))) : ℝ) + 1)
      ≤ ((RR μ g b : ℕ) : ℝ) ^ (1 / ((μ : ℝ) + 1)) + 2 := by
    have h := Nat.ceil_lt_add_one hx0
    linarith
  push_cast
  have hmain : ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) ^ (1 / ((μ : ℝ) + 1)) *
        ((b : ℝ) + 1) ^ ((μ : ℝ) / ((μ : ℝ) + 1)) + 2
      ≤ 8 * ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) ^ (1 / ((μ : ℝ) + 1)) *
          ((b : ℝ) + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1)) := by
    have h1 : ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) ^ (1 / ((μ : ℝ) + 1)) *
          ((b : ℝ) + 1) ^ ((μ : ℝ) / ((μ : ℝ) + 1))
        ≤ ((((μ + 1).factorial : ℕ) : ℝ) * (8 * (g : ℝ) + 9)) ^ (1 / ((μ : ℝ) + 1)) *
          ((b : ℝ) + 2) ^ ((μ : ℝ) / ((μ : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg (by positivity) _)
    nlinarith [h1, hP1]
  linarith [rpow_RR μ g b, hceil, hmain]

end Work.WilkiesH.Interp.V2dV

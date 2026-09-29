import Mathlib
import Submission.Work.TMContract.Defs

/-!
# Fundamentals for the "exponential lower bound" reduction (`RedProj`)

Owned by the proof of `Work.TMComp.RedProj.exp_lower_of_diophBelow`.
(Kept under this file name because `Submission/Work/TMComp/RedProj/Basic.lean` belongs to
another worker in the shared directory.)

Two key items:

* `norm_exp_two_pi_eq`: `‖exp (2 π i y) - 1‖ = 2 |sin (π y)|`;
* `four_mul_fracDist_le_norm`: `4 * fracDist (k α) ≤ ‖exp (2 π i k α) - 1‖` for every `k : ℤ`.
-/

open Complex

noncomputable section

namespace Work.TMComp.RedProj

/-! ## 1. The distance to the nearest integer -/

theorem fracDist_nonneg (x : ℝ) : 0 ≤ Work.TMContract.fracDist x := abs_nonneg _

theorem fracDist_le_half (x : ℝ) : Work.TMContract.fracDist x ≤ 1 / 2 := abs_sub_round x

theorem fracDist_eq_zero_iff (x : ℝ) :
    Work.TMContract.fracDist x = 0 ↔ ∃ z : ℤ, x = (z : ℝ) := by
  rw [Work.TMContract.fracDist, abs_eq_zero, sub_eq_zero]
  constructor
  · intro h; exact ⟨round x, h⟩
  · rintro ⟨z, rfl⟩; simp [round_intCast]

/-- `fracDist` is an even function of its argument. -/
theorem fracDist_neg (x : ℝ) : Work.TMContract.fracDist (-x) = Work.TMContract.fracDist x := by
  have h1 : Work.TMContract.fracDist (-x) ≤ Work.TMContract.fracDist x := by
    have h := round_le (-x) (-(round x))
    rw [show ((-x : ℝ) - (((-(round x) : ℤ)) : ℝ)) = -(x - (round x : ℝ)) by push_cast; ring,
      abs_neg] at h
    simpa [Work.TMContract.fracDist] using h
  have h2 : Work.TMContract.fracDist x ≤ Work.TMContract.fracDist (-x) := by
    have h := round_le x (-(round (-x)))
    rw [show ((x : ℝ) - (((-(round (-x)) : ℤ)) : ℝ))
          = -((-x : ℝ) - (round (-x) : ℝ)) by push_cast; ring, abs_neg] at h
    simpa [Work.TMContract.fracDist] using h
  exact le_antisymm h1 h2

/-- `fracDist` only depends on `|y|`. -/
theorem fracDist_abs (α y : ℝ) :
    Work.TMContract.fracDist (y * α) = Work.TMContract.fracDist (|y| * α) := by
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]
  · rw [abs_of_neg hy]
    rw [show -y * α = -(y * α) by ring, fracDist_neg]

/-- `fracDist (k α)` only depends on `k.natAbs`. -/
theorem fracDist_natAbs (α : ℝ) (k : ℤ) :
    Work.TMContract.fracDist ((k : ℝ) * α)
      = Work.TMContract.fracDist (((k.natAbs : ℕ) : ℝ) * α) := by
  rw [fracDist_abs α (k : ℝ), show |(k : ℝ)| = ((k.natAbs : ℕ) : ℝ) by simp]

/-! ## 2. The modulus of `exp (2 π i y) - 1` -/

theorem norm_exp_two_pi_eq (y : ℝ) :
    ‖Complex.exp (2 * Real.pi * y * Complex.I) - 1‖
      = 2 * |Real.sin (Real.pi * y)| := by
  have h : (2 * Real.pi * y * Complex.I : ℂ) = Complex.I * ((2 * Real.pi * y : ℝ) : ℂ) := by
    push_cast; ring
  rw [h, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * y) / 2 = Real.pi * y by ring]
  simp

/-- The modulus of `exp (2 π i y) - 1` only depends on `|y|`. -/
theorem norm_exp_two_pi_abs (α y : ℝ) :
    ‖Complex.exp (2 * Real.pi * y * α * Complex.I) - 1‖
      = ‖Complex.exp (2 * Real.pi * |y| * α * Complex.I) - 1‖ := by
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]
  · rw [abs_of_neg hy, Complex.ofReal_neg]
    have hneg : (2 * Real.pi * (-y) * α * Complex.I : ℂ)
        = -(2 * Real.pi * y * α * Complex.I) := by
      ring
    rw [hneg, Complex.exp_neg]
    set z : ℂ := Complex.exp (2 * Real.pi * y * α * Complex.I) with hz
    have hnorm1 : ‖z‖ = 1 := by
      rw [hz, Complex.norm_exp]
      simp
    have hz0 : z ≠ 0 := by simp [hz]
    have h1 : z⁻¹ - 1 = z⁻¹ * (1 - z) := by
      rw [mul_sub, mul_one, inv_mul_cancel₀ hz0]
    rw [h1, norm_mul, norm_inv, hnorm1, inv_one, one_mul, norm_sub_rev]

/-- The modulus of `exp (2 π i k α) - 1` only depends on `k.natAbs`. -/
theorem norm_exp_two_pi_natAbs (α : ℝ) (k : ℤ) :
    ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖
      = ‖Complex.exp (2 * Real.pi * (((k.natAbs : ℕ) : ℝ)) * α * Complex.I) - 1‖ := by
  rw [norm_exp_two_pi_abs α (k : ℝ), show |(k : ℝ)| = ((k.natAbs : ℕ) : ℝ) by simp]

/-! ## 3. The two comparison inequalities -/

/-- **Distance to the integers controls the chord length.** -/
theorem four_mul_fracDist_le_norm (α : ℝ) (k : ℤ) :
    4 * Work.TMContract.fracDist ((k : ℝ) * α) ≤
      ‖Complex.exp (2 * Real.pi * (k : ℝ) * α * Complex.I) - 1‖ := by
  have harg : (2 * Real.pi * (k:ℝ) * α * Complex.I : ℂ)
      = (2 * Real.pi * (((k:ℝ) * α : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [harg, norm_exp_two_pi_eq ((k:ℝ) * α)]
  set y : ℝ := (k:ℝ) * α with hy
  set m : ℤ := round y with hm
  have ht_le : |y - (m:ℝ)| ≤ 1/2 := by rw [hm]; exact abs_sub_round y
  set t : ℝ := y - (m:ℝ) with ht
  have hy_eq : y = t + (m:ℝ) := by rw [ht]; ring
  have hfy : Work.TMContract.fracDist y = |t| := by
    rw [Work.TMContract.fracDist, ← hm, ← ht]
  rw [hfy]
  have hsin : Real.sin (Real.pi * y) = (-1 : ℝ)^(m:ℤ) * Real.sin (Real.pi * t) := by
    rw [hy_eq, show Real.pi * (t + (m:ℝ)) = Real.pi * t + (m:ℝ) * Real.pi by ring,
      Real.sin_add_int_mul_pi]
  rw [hsin, abs_mul, abs_neg_one_zpow, one_mul]
  have hpi2 : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    have h1 : Real.pi * |t| ≤ Real.pi * (1/2) := mul_le_mul_of_nonneg_left ht_le Real.pi_pos.le
    linarith
  have hb := Real.mul_abs_le_abs_sin hpi2
  have hb2 : 2 * |t| ≤ |Real.sin (Real.pi * t)| := by
    have h2 : (2:ℝ) / Real.pi * |Real.pi * t| = 2 * |t| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      field_simp
    rw [← h2]; exact hb
  linarith

/-- For irrational `α` and nonzero `k`, `‖exp (2 π i k α) - 1‖ > 0`. -/
theorem norm_exp_two_pi_pos_of_irrational {α : ℝ} (hα : Irrational α) {k : ℤ} (hk : k ≠ 0) :
    0 < ‖Complex.exp (2 * Real.pi * (k:ℝ) * α * Complex.I) - 1‖ := by
  by_contra h
  push Not at h
  have h0 : ‖Complex.exp (2 * Real.pi * (k:ℝ) * α * Complex.I) - 1‖ = 0 :=
    le_antisymm h (norm_nonneg _)
  have h4 := four_mul_fracDist_le_norm α k
  rw [h0] at h4
  have hfd : Work.TMContract.fracDist ((k:ℝ)*α) = 0 := by
    have hnn : 0 ≤ Work.TMContract.fracDist ((k:ℝ)*α) := abs_nonneg _
    nlinarith
  obtain ⟨z, hz⟩ := (fracDist_eq_zero_iff ((k:ℝ)*α)).mp hfd
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast hk
  have hdiv : α = (z:ℝ)/(k:ℝ) := by
    field_simp
    linarith
  apply hα
  refine ⟨(z:ℚ)/(k:ℚ), ?_⟩
  rw [hdiv]
  push_cast
  ring

end Work.TMComp.RedProj

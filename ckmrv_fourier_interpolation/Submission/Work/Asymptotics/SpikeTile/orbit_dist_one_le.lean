/-
# Points of the `SL(2,ℤ)`-orbit of a high point of `ℍ` are at Euclidean distance `≥ 1`

Let `σ ∈ ℍ` with `Im σ ≥ 2` and `η ∈ SL(2,ℤ)` with `η • σ ≠ σ`.  Then the Euclidean distance
between `η • σ` and `σ`, viewed as complex numbers, is at least `1`.

The proof splits on the lower-left entry `c = η 1 0` of `η`.

* If `c = 0` the determinant relation `ad - bc = 1` forces `a = d = ±1`, so `η` acts as the
  translation `σ ↦ σ + b/d` with `b = η 0 1 ≠ 0` (as `η` does not fix `σ`); hence the distance
  equals `|b| ≥ 1`.

* If `c ≠ 0` one writes `γ = [[a,b],[c,d]]` and uses the exact identity (valid for `c ≠ 0`,
  `ad - bc = 1` and `c z + d ≠ 0`)

    `(a z + b)/(c z + d) = a/c - 1/(c (c z + d))`.

  Hence `γ z - z = (a/c - z) - 1/(c (c z + d))`.  Since `a/c` is real, `‖a/c - z‖ ≥ Im z`,
  while `‖1/(c(c z + d))‖ ≤ 1/Im z` because the imaginary part of `c (c z + d)` equals
  `c² Im z`.  The reverse triangle inequality then gives

    `‖γ z - z‖ ≥ Im z - 1/Im z ≥ 2 - 1/2 ≥ 1`.

  (In fact the bound is `≥ 3/2`; the shift `z ↦ z + 1` at `z = 2i` shows the argument is sharp.)
-/
import Mathlib

namespace Work.Asymptotics.SpikeTile

open UpperHalfPlane Matrix
open scoped MatrixGroups

/-- The Möbius action of `g ∈ SL(2,ℤ)` written out in the entries of `g`. -/
lemma orbit_coe_smul_eq (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane) :
    ((g • z : UpperHalfPlane) : ℂ) =
      (((g 0 0 : ℤ) : ℂ) * (z : ℂ) + ((g 0 1 : ℤ) : ℂ)) /
      (((g 1 0 : ℤ) : ℂ) * (z : ℂ) + ((g 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [algebraMap_int_eq]
  simp

/-- For `c ≠ 0` and `a d - b c = 1` the linear fractional transformation has the
"parabolic shape" `(a z + b)/(c z + d) = a/c - 1/(c (c z + d))`. -/
lemma orbit_div_sl_eq (A B C D z : ℂ) (hC : C ≠ 0) (hden : C * z + D ≠ 0)
    (hdet : A * D - B * C = 1) :
    (A * z + B) / (C * z + D) = A / C - 1 / (C * (C * z + D)) := by
  have hden' : z * C + D ≠ 0 := by rw [mul_comm]; exact hden
  rw [one_div, mul_inv, mul_comm C z]
  field_simp
  linear_combination -hdet

/-- The case `c = η 1 0 ≠ 0` of `Work.Asymptotics.SpikeTile.orbit_dist_one_le`. -/
lemma orbit_dist_one_le_of_c_ne_zero (η : Matrix.SpecialLinearGroup (Fin 2) ℤ) (σ : UpperHalfPlane)
    (hσ : 2 ≤ σ.im) (hC : η 1 0 ≠ 0) :
    1 ≤ ‖((η • σ : UpperHalfPlane) : ℂ) - (σ : ℂ)‖ := by
  have hdetI : η 0 0 * η 1 1 - η 0 1 * η 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe η
    rwa [Matrix.det_fin_two] at h
  have hdet : (η 0 0 : ℂ) * (η 1 1 : ℂ) - (η 0 1 : ℂ) * (η 1 0 : ℂ) = 1 := by
    exact_mod_cast hdetI
  have hCne : ((η 1 0 : ℤ) : ℂ) ≠ 0 := by simpa using hC
  -- the denominator `c z + d` does not vanish: its imaginary part is `c · Im z ≠ 0`
  have hden : ((η 1 0 : ℤ) : ℂ) * (σ : ℂ) + ((η 1 1 : ℤ) : ℂ) ≠ 0 := by
    intro hzero
    have him := congrArg Complex.im hzero
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      Complex.zero_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_re, zero_mul, add_zero] at him
    have hcr : ((η 1 0 : ℤ) : ℝ) = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · exact h
      · exact absurd h (ne_of_gt σ.im_pos)
    exact hC (by exact_mod_cast hcr)
  -- the parabolic shape of the transformation
  have hsplit : ((η • σ : UpperHalfPlane) : ℂ) - (σ : ℂ)
      = ((η 0 0 : ℂ) / (η 1 0 : ℂ) - (σ : ℂ))
        - 1 / ((η 1 0 : ℂ) * ((η 1 0 : ℂ) * (σ : ℂ) + (η 1 1 : ℂ))) := by
    rw [orbit_coe_smul_eq, orbit_div_sl_eq (η 0 0 : ℂ) (η 0 1 : ℂ) (η 1 0 : ℂ) (η 1 1 : ℂ)
      (σ : ℂ) hCne hden hdet]
    ring
  -- `‖a/c - z‖ ≥ Im z` because `a/c` is real
  have hu : σ.im ≤ ‖((η 0 0 : ℂ) / (η 1 0 : ℂ) - (σ : ℂ))‖ := by
    have him : ((η 0 0 : ℂ) / (η 1 0 : ℂ) - (σ : ℂ)).im = -σ.im := by
      rw [Complex.sub_im]
      have h1 : ((η 0 0 : ℂ) / (η 1 0 : ℂ)).im = 0 := by rw [Complex.div_im]; simp
      rw [h1, UpperHalfPlane.coe_im]; ring
    calc σ.im = |((η 0 0 : ℂ) / (η 1 0 : ℂ) - (σ : ℂ)).im| := by
          rw [him, abs_neg, abs_of_pos σ.im_pos]
      _ ≤ ‖((η 0 0 : ℂ) / (η 1 0 : ℂ) - (σ : ℂ))‖ := Complex.abs_im_le_norm _
  -- `‖1/(c (c z + d))‖ ≤ 1/Im z`
  have hcR : (1 : ℝ) ≤ |((η 1 0 : ℤ) : ℝ)| := by
    have h := Int.one_le_abs hC
    have h2 : (1 : ℝ) ≤ ((|η 1 0| : ℤ) : ℝ) := by exact_mod_cast h
    rwa [Int.cast_abs] at h2
  have hv : ‖(1 : ℂ) / ((η 1 0 : ℂ) * ((η 1 0 : ℂ) * (σ : ℂ) + (η 1 1 : ℂ)))‖ ≤ 1 / σ.im := by
    have him2 : (((η 1 0 : ℂ) * ((η 1 0 : ℂ) * (σ : ℂ) + (η 1 1 : ℂ))).im)
        = ((η 1 0 : ℝ)) ^ 2 * σ.im := by
      simp only [Complex.mul_im, Complex.add_im, Complex.intCast_re, Complex.intCast_im,
        UpperHalfPlane.coe_im, UpperHalfPlane.coe_re, zero_mul, add_zero]
      ring
    have hx : σ.im ≤ ‖(η 1 0 : ℂ) * ((η 1 0 : ℂ) * (σ : ℂ) + (η 1 1 : ℂ))‖ := by
      have hs : (1 : ℝ) ≤ ((η 1 0 : ℝ)) ^ 2 := by
        nlinarith [sq_abs (((η 1 0 : ℤ) : ℝ)), abs_nonneg (((η 1 0 : ℤ) : ℝ)),
          sq_nonneg (((η 1 0 : ℤ) : ℝ)), hcR]
      calc σ.im ≤ ((η 1 0 : ℝ)) ^ 2 * σ.im := by nlinarith [hs, σ.im_pos]
        _ = |(((η 1 0 : ℂ) * ((η 1 0 : ℂ) * (σ : ℂ) + (η 1 1 : ℂ))).im)| := by
              rw [him2, abs_of_nonneg (by positivity)]
        _ ≤ ‖(η 1 0 : ℂ) * ((η 1 0 : ℂ) * (σ : ℂ) + (η 1 1 : ℂ))‖ := Complex.abs_im_le_norm _
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le σ.im_pos hx
  have hgap : (1 : ℝ) ≤ σ.im - 1 / σ.im := by
    have h2 : 1 / σ.im ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hσ
    linarith
  have h1 : σ.im - 1 / σ.im ≤
      ‖((η 0 0 : ℂ) / (η 1 0 : ℂ) - (σ : ℂ))
        - (1 : ℂ) / ((η 1 0 : ℂ) * ((η 1 0 : ℂ) * (σ : ℂ) + (η 1 1 : ℂ)))‖ := by
    calc σ.im - 1 / σ.im ≤ ‖((η 0 0 : ℂ) / (η 1 0 : ℂ) - (σ : ℂ))‖
          - ‖(1 : ℂ) / ((η 1 0 : ℂ) * ((η 1 0 : ℂ) * (σ : ℂ) + (η 1 1 : ℂ)))‖ := by
            linarith [hu, hv]
      _ ≤ |‖((η 0 0 : ℂ) / (η 1 0 : ℂ) - (σ : ℂ))‖
          - ‖(1 : ℂ) / ((η 1 0 : ℂ) * ((η 1 0 : ℂ) * (σ : ℂ) + (η 1 1 : ℂ)))‖| :=
            le_abs_self _
      _ ≤ ‖((η 0 0 : ℂ) / (η 1 0 : ℂ) - (σ : ℂ))
          - (1 : ℂ) / ((η 1 0 : ℂ) * ((η 1 0 : ℂ) * (σ : ℂ) + (η 1 1 : ℂ)))‖ :=
            abs_norm_sub_norm_le _ _
  rw [hsplit]
  linarith [h1, hgap]

/-- The case `c = η 1 0 = 0` of `Work.Asymptotics.SpikeTile.orbit_dist_one_le`: `η` acts as a
non-trivial translation `σ ↦ σ + b/d`. -/
lemma orbit_dist_one_le_of_c_eq_zero (η : Matrix.SpecialLinearGroup (Fin 2) ℤ) (σ : UpperHalfPlane)
    (h : η • σ ≠ σ) (hC : η 1 0 = 0) :
    1 ≤ ‖((η • σ : UpperHalfPlane) : ℂ) - (σ : ℂ)‖ := by
  have hdetI : η 0 0 * η 1 1 - η 0 1 * η 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe η
    rwa [Matrix.det_fin_two] at h
  have hprod : η 0 0 * η 1 1 = 1 := by
    rw [hC, mul_zero, sub_zero] at hdetI; exact hdetI
  have hA : η 0 0 = 1 ∨ η 0 0 = -1 := Int.eq_one_or_neg_one_of_mul_eq_one hprod
  have hD : η 1 1 = 1 ∨ η 1 1 = -1 :=
    Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact hprod)
  have hAD : η 0 0 = η 1 1 := by
    rcases hA with h1 | h1 <;> rw [h1] at hprod ⊢ <;> omega
  have hDne : ((η 1 1 : ℤ) : ℂ) ≠ 0 := by
    rcases hD with h1 | h1 <;> rw [h1] <;> norm_num
  have hne : ((η • σ : UpperHalfPlane) : ℂ) ≠ (σ : ℂ) :=
    fun hh => h (UpperHalfPlane.ext hh)
  have hdiff : ((η • σ : UpperHalfPlane) : ℂ) - (σ : ℂ) =
      (η 0 1 : ℂ) / (η 1 1 : ℂ) := by
    rw [orbit_coe_smul_eq, hC, hAD]
    simp only [Int.cast_zero, zero_mul, zero_add]
    field_simp
    ring
  have hB : η 0 1 ≠ 0 := by
    intro hB0
    refine hne ?_
    have h0 : ((η • σ : UpperHalfPlane) : ℂ) - (σ : ℂ) = 0 := by
      rw [hdiff, hB0]; simp
    rwa [sub_eq_zero] at h0
  rw [hdiff]
  have hD1 : ‖((η 1 1 : ℤ) : ℂ)‖ = 1 := by
    rcases hD with h1 | h1 <;> rw [h1] <;> norm_num
  have hB1 : (1 : ℝ) ≤ ‖((η 0 1 : ℤ) : ℂ)‖ := by
    rw [show ‖((η 0 1 : ℤ) : ℂ)‖ = ((|η 0 1| : ℤ) : ℝ) by
      rw [Complex.norm_intCast, Int.cast_abs]]
    exact_mod_cast Int.one_le_abs hB
  rw [norm_div, hD1, div_one]
  exact hB1

theorem orbit_dist_one_le {σ : UpperHalfPlane} (hσ : 2 ≤ σ.im)
    (η : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h : η • σ ≠ σ) :
    1 ≤ ‖(((η • σ : UpperHalfPlane)) : ℂ) - (σ : ℂ)‖ := by
  rcases eq_or_ne (η 1 0) 0 with hC | hC
  · exact orbit_dist_one_le_of_c_eq_zero η σ h hC
  · exact orbit_dist_one_le_of_c_ne_zero η σ hσ hC

end Work.Asymptotics.SpikeTile

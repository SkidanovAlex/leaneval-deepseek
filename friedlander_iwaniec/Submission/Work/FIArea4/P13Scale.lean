import Mathlib
import Submission.Work.FIArea4.A4varbounds

/-!
# The §13 scale `P = D^{-1/2}(R+S)^{-1/8}(RS)^{3/8}`

The scale at which FI §13 enlarges the moduli, together with the two elementary identities
`P ≤ (RS)^{3/8}` and `D·P² = (R+S)^{-1/4}(RS)^{3/4}`.
-/

namespace Work.FIArea4

noncomputable section

/-- The scale `P = D^{-1/2}(R+S)^{-1/8}(RS)^{3/8}` of FI §13. -/
def p13P (D R S : ℕ) : ℝ :=
  (D : ℝ) ^ (-(1:ℝ)/2) * ((R : ℝ) + (S : ℝ)) ^ (-(1:ℝ)/8) * ((R : ℝ) * (S : ℝ)) ^ ((3:ℝ)/8)

lemma p13P_pos (D R S : ℕ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) : 0 < p13P D R S := by
  unfold p13P
  have h1 : (0:ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have h2 : (0:ℝ) < (R : ℝ) + (S : ℝ) := by
    have hR0 : (0:ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
    linarith [Nat.cast_nonneg (α := ℝ) S]
  have h3 : (0:ℝ) < (R : ℝ) * (S : ℝ) := by
    have hR0 : (0:ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
    have hS0 : (0:ℝ) < (S : ℝ) := by exact_mod_cast (by omega : 0 < S)
    positivity
  exact mul_pos (mul_pos (Real.rpow_pos_of_pos h1 _) (Real.rpow_pos_of_pos h2 _))
    (Real.rpow_pos_of_pos h3 _)

lemma p13P_le (D R S : ℕ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    p13P D R S ≤ ((R : ℝ) * (S : ℝ)) ^ ((3:ℝ)/8) := by
  unfold p13P
  have h1 : (D : ℝ) ^ (-(1:ℝ)/2) ≤ 1 := by
    have hD1 : (1:ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    calc (D : ℝ) ^ (-(1:ℝ)/2) ≤ (D : ℝ) ^ (0:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num)
      _ = 1 := Real.rpow_zero _
  have h2 : ((R : ℝ) + (S : ℝ)) ^ (-(1:ℝ)/8) ≤ 1 := by
    have hR1 : (1:ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    have h1 : (1:ℝ) ≤ (R : ℝ) + (S : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) S
      linarith
    calc ((R : ℝ) + (S : ℝ)) ^ (-(1:ℝ)/8) ≤ ((R : ℝ) + (S : ℝ)) ^ (0:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = 1 := Real.rpow_zero _
  have h3 : (0:ℝ) ≤ ((R : ℝ) * (S : ℝ)) ^ ((3:ℝ)/8) := by
    apply Real.rpow_nonneg
    have hR0 : (0:ℝ) ≤ (R : ℝ) := Nat.cast_nonneg R
    have hS0 : (0:ℝ) ≤ (S : ℝ) := Nat.cast_nonneg S
    positivity
  have h4 : (0:ℝ) ≤ (D : ℝ) ^ (-(1:ℝ)/2) := Real.rpow_nonneg (Nat.cast_nonneg D) _
  have h5 : (0:ℝ) ≤ ((R : ℝ) + (S : ℝ)) ^ (-(1:ℝ)/8) :=
    Real.rpow_nonneg (by positivity) _
  calc (D : ℝ) ^ (-(1:ℝ)/2) * ((R : ℝ) + (S : ℝ)) ^ (-(1:ℝ)/8) * ((R : ℝ) * (S : ℝ)) ^ ((3:ℝ)/8)
      ≤ 1 * 1 * ((R : ℝ) * (S : ℝ)) ^ ((3:ℝ)/8) := by
        apply mul_le_mul (mul_le_mul h1 h2 h5 (by norm_num)) le_rfl h3 (by positivity)
    _ = ((R : ℝ) * (S : ℝ)) ^ ((3:ℝ)/8) := by ring

lemma p13P_mul_sq (D R S : ℕ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) :
    (D : ℝ) * (p13P D R S) ^ 2
      = ((R : ℝ) + (S : ℝ)) ^ (-(1:ℝ)/4) * ((R : ℝ) * (S : ℝ)) ^ ((3:ℝ)/4) := by
  unfold p13P
  have hD0 : (0:ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hRS0 : (0:ℝ) < (R : ℝ) + (S : ℝ) := by
    have hR1 : (1:ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    have := Nat.cast_nonneg (α := ℝ) S
    linarith
  have hRS1 : (0:ℝ) < (R : ℝ) * (S : ℝ) := by
    have hR0 : (0:ℝ) < (R : ℝ) := by exact_mod_cast (by omega : 0 < R)
    have hS0 : (0:ℝ) < (S : ℝ) := by exact_mod_cast (by omega : 0 < S)
    positivity
  have h1 : ((D : ℝ) ^ (-(1:ℝ)/2)) ^ 2 = ((D : ℝ))⁻¹ := by
    rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hD0)]
    norm_num
    exact Real.rpow_neg_one _
  have h2 : (((R : ℝ) + (S : ℝ)) ^ (-(1:ℝ)/8)) ^ 2 = (((R : ℝ) + (S : ℝ))) ^ (-(1:ℝ)/4) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hRS0)]
    norm_num
  have h3 : (((R : ℝ) * (S : ℝ)) ^ ((3:ℝ)/8)) ^ 2 = (((R : ℝ) * (S : ℝ))) ^ ((3:ℝ)/4) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hRS1)]
    norm_num
  rw [mul_pow, mul_pow, h1, h2, h3]
  field_simp

lemma p14T13_pos (D R S : ℕ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) (ε : ℝ) :
    0 < p14T13 D R S ε := by
  unfold p14T13
  have hD1 : (0:ℝ) < (D:ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hRS : (0:ℝ) < (R:ℝ)*(S:ℝ) := by
    have hR1 : (0:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 0 < R)
    have hS1 : (0:ℝ) < (S:ℝ) := by exact_mod_cast (by omega : 0 < S)
    positivity
  have h6 : (0:ℝ) < (D:ℝ) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/4) * ((R:ℝ)*(S:ℝ))^((1:ℝ)/4) := by positivity
  have h7 : (0:ℝ) ≤ (D:ℝ)^(-(1:ℝ)/2) * ((R:ℝ)+(S:ℝ))^((1:ℝ)/8) * ((R:ℝ)*(S:ℝ))^((9:ℝ)/8) := by positivity
  linarith

lemma p14T12_pos (D R S : ℕ) (hD : 1 ≤ D) (hR : 1 ≤ R) (hS : 1 ≤ S) (ε : ℝ) :
    0 < p14T12 D R S ε := by
  unfold p14T12
  have hD1 : (0:ℝ) < (D:ℝ) := by exact_mod_cast (by omega : 0 < D)
  have h2 : (0:ℝ) ≤ (D:ℝ)^((1:ℝ)/3) * ((R:ℝ)*(S:ℝ))^((2:ℝ)/3)
      * (Real.log (2 * (R:ℝ) * (S:ℝ)) + 1) ^ (4:ℕ) := by positivity
  have h3 : (0:ℝ) ≤ ((D:ℝ)⁻¹ * ((R:ℝ)*(S:ℝ))^((3:ℝ)/2)
      + (R:ℝ) * (S:ℝ)^((3:ℝ)/4) + (S:ℝ) * (R:ℝ)^((3:ℝ)/4))
      * (((R:ℝ)*(S:ℝ))^ε) := by positivity
  linarith

end

end Work.FIArea4

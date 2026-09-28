import Mathlib
import Submission.Work.HP.Q44Main.m17_le_Z_half
import Submission.Work.HP.Q44Main.m17_le_delta_half
import Submission.Work.HP.Q44Main.m17_le_mix

namespace Work.HP.Q44Main

/-- Comparison lemma used in the `min` reduction for the Q44 window sums.

Given `M, Z, Δ ≥ 1`, `M^53 ≤ Δ` and `M^106 Δ ≤ Z^3`, the sum of five monomials in
`M, Z, Δ` is bounded by `5` times `Z^(9/2) Δ^2 (Z^(3/2)+Δ^(3/2)) M^53`.

The mechanism: from the two constraints one gets
`M^17 ≤ Z^(1/2)`, `M^17 ≤ Δ^(1/2)` and `M^17 ≤ Z^(1/2) Δ^(-1/6)`; multiplying by the
remaining monomial part shows each of the five summands is at most one of the two
pieces `Z^6 Δ^2 M^53`, `Z^(9/2) Δ^(7/2) M^53` whose sum is the bracket on the right. -/
theorem min_compare_good3 (CL1 Z Δ M : ℝ) (hZ : 1 ≤ Z) (hΔ : 1 ≤ Δ) (hM : 1 ≤ M)
    (hCL1 : 0 < CL1) (hMle : M^(53:ℝ) ≤ Δ) (hZ3 : M^(106:ℝ) * Δ ≤ Z^(3:ℝ)) :
    CL1 * (M^(70:ℝ) * Z^(4:ℝ) * Δ^((7:ℝ)/2) + M^(70:ℝ) * Z^(6:ℝ) * Δ^((3:ℝ)/2)
      + M^(70:ℝ) * Z^(4:ℝ) * Δ^((11:ℝ)/3) + M^(40:ℝ) * Z^(4:ℝ) * Δ^(3:ℝ)
      + M^(40:ℝ) * Z^(6:ℝ) * Δ^(2:ℝ)) ≤
      (5 * CL1) * (Z^((9:ℝ)/2) * Δ^(2:ℝ) * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) * M^(53:ℝ)) := by
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hΔpos : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ
  have hfac1 : M^(17:ℝ) ≤ Z^((1:ℝ)/2) := m17_le_Z_half M Z Δ hM hZ hΔ hZ3
  have hfac2 : M^(17:ℝ) ≤ Δ^((1:ℝ)/2) := m17_le_delta_half M Δ hM hΔ hMle
  have hfac3 : M^(17:ℝ) ≤ Z^((1:ℝ)/2) * Δ^((-1:ℝ)/6) := m17_le_mix M Z Δ hM hZ hΔ hZ3
  -- Each of the five summands is bounded by one of the two bracket pieces.
  have hT1 : M^(70:ℝ) * Z^(4:ℝ) * Δ^((7:ℝ)/2) ≤ Z^((9:ℝ)/2) * Δ^((7:ℝ)/2) * M^(53:ℝ) := by
    have hkey : M^(17:ℝ) * Z^(4:ℝ) ≤ Z^((9:ℝ)/2) := by
      calc M^(17:ℝ) * Z^(4:ℝ) ≤ Z^((1:ℝ)/2) * Z^(4:ℝ) := mul_le_mul_of_nonneg_right hfac1 (by positivity)
        _ = Z^((9:ℝ)/2) := by rw [← Real.rpow_add hZpos]; norm_num
    have h70 : M^(70:ℝ) = M^(53:ℝ) * M^(17:ℝ) := by rw [← Real.rpow_add hMpos]; norm_num
    calc M^(70:ℝ) * Z^(4:ℝ) * Δ^((7:ℝ)/2)
        = M^(53:ℝ) * (M^(17:ℝ) * Z^(4:ℝ)) * Δ^((7:ℝ)/2) := by rw [h70]; ring
      _ ≤ M^(53:ℝ) * Z^((9:ℝ)/2) * Δ^((7:ℝ)/2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey (by positivity)) (by positivity)
      _ = Z^((9:ℝ)/2) * Δ^((7:ℝ)/2) * M^(53:ℝ) := by ring
  have hT2 : M^(70:ℝ) * Z^(6:ℝ) * Δ^((3:ℝ)/2) ≤ Z^(6:ℝ) * Δ^(2:ℝ) * M^(53:ℝ) := by
    have hkey : M^(17:ℝ) * Δ^((3:ℝ)/2) ≤ Δ^(2:ℝ) := by
      calc M^(17:ℝ) * Δ^((3:ℝ)/2) ≤ Δ^((1:ℝ)/2) * Δ^((3:ℝ)/2) := mul_le_mul_of_nonneg_right hfac2 (by positivity)
        _ = Δ^(2:ℝ) := by rw [← Real.rpow_add hΔpos]; norm_num
    have h70 : M^(70:ℝ) = M^(53:ℝ) * M^(17:ℝ) := by rw [← Real.rpow_add hMpos]; norm_num
    calc M^(70:ℝ) * Z^(6:ℝ) * Δ^((3:ℝ)/2)
        = M^(53:ℝ) * (M^(17:ℝ) * Δ^((3:ℝ)/2)) * Z^(6:ℝ) := by rw [h70]; ring
      _ ≤ M^(53:ℝ) * Δ^(2:ℝ) * Z^(6:ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey (by positivity)) (by positivity)
      _ = Z^(6:ℝ) * Δ^(2:ℝ) * M^(53:ℝ) := by ring
  have hT3 : M^(70:ℝ) * Z^(4:ℝ) * Δ^((11:ℝ)/3) ≤ Z^((9:ℝ)/2) * Δ^((7:ℝ)/2) * M^(53:ℝ) := by
    have hkey : M^(17:ℝ) * Z^(4:ℝ) * Δ^((11:ℝ)/3) ≤ Z^((9:ℝ)/2) * Δ^((7:ℝ)/2) := by
      calc M^(17:ℝ) * Z^(4:ℝ) * Δ^((11:ℝ)/3)
          ≤ (Z^((1:ℝ)/2) * Δ^((-1:ℝ)/6)) * Z^(4:ℝ) * Δ^((11:ℝ)/3) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfac3 (by positivity)) (by positivity)
        _ = (Z^((1:ℝ)/2) * Z^(4:ℝ)) * (Δ^((-1:ℝ)/6) * Δ^((11:ℝ)/3)) := by ring
        _ = Z^((9:ℝ)/2) * Δ^((7:ℝ)/2) := by rw [← Real.rpow_add hZpos, ← Real.rpow_add hΔpos]; norm_num
    have h70 : M^(70:ℝ) = M^(53:ℝ) * M^(17:ℝ) := by rw [← Real.rpow_add hMpos]; norm_num
    calc M^(70:ℝ) * Z^(4:ℝ) * Δ^((11:ℝ)/3)
        = M^(53:ℝ) * (M^(17:ℝ) * Z^(4:ℝ) * Δ^((11:ℝ)/3)) := by rw [h70]; ring
      _ ≤ M^(53:ℝ) * (Z^((9:ℝ)/2) * Δ^((7:ℝ)/2)) := mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = Z^((9:ℝ)/2) * Δ^((7:ℝ)/2) * M^(53:ℝ) := by ring
  have hT4 : M^(40:ℝ) * Z^(4:ℝ) * Δ^(3:ℝ) ≤ Z^((9:ℝ)/2) * Δ^((7:ℝ)/2) * M^(53:ℝ) := by
    have h1 : M^(40:ℝ) ≤ M^(53:ℝ) := Real.rpow_le_rpow_of_exponent_le hM (by norm_num)
    have h2 : Z^(4:ℝ) ≤ Z^((9:ℝ)/2) := Real.rpow_le_rpow_of_exponent_le hZ (by norm_num)
    have h3 : Δ^(3:ℝ) ≤ Δ^((7:ℝ)/2) := Real.rpow_le_rpow_of_exponent_le hΔ (by norm_num)
    calc M^(40:ℝ) * Z^(4:ℝ) * Δ^(3:ℝ) ≤ M^(53:ℝ) * Z^((9:ℝ)/2) * Δ^((7:ℝ)/2) := by
          apply mul_le_mul
          · exact mul_le_mul h1 h2 (by positivity) (by positivity)
          · exact h3
          · positivity
          · positivity
      _ = Z^((9:ℝ)/2) * Δ^((7:ℝ)/2) * M^(53:ℝ) := by ring
  have hT5 : M^(40:ℝ) * Z^(6:ℝ) * Δ^(2:ℝ) ≤ Z^(6:ℝ) * Δ^(2:ℝ) * M^(53:ℝ) := by
    have h1 : M^(40:ℝ) ≤ M^(53:ℝ) := Real.rpow_le_rpow_of_exponent_le hM (by norm_num)
    calc M^(40:ℝ) * Z^(6:ℝ) * Δ^(2:ℝ) ≤ M^(53:ℝ) * Z^(6:ℝ) * Δ^(2:ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity)) (by positivity)
      _ = Z^(6:ℝ) * Δ^(2:ℝ) * M^(53:ℝ) := by ring
  -- Split the bracket on the right-hand side into its two monomial pieces.
  have hId : Z^((9:ℝ)/2) * Δ^(2:ℝ) * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) * M^(53:ℝ)
      = Z^(6:ℝ) * Δ^(2:ℝ) * M^(53:ℝ) + Z^((9:ℝ)/2) * Δ^((7:ℝ)/2) * M^(53:ℝ) := by
    have e1 : Z^((9:ℝ)/2) * Z^((3:ℝ)/2) = Z^(6:ℝ) := by rw [← Real.rpow_add hZpos]; norm_num
    have e2 : Δ^(2:ℝ) * Δ^((3:ℝ)/2) = Δ^((7:ℝ)/2) := by rw [← Real.rpow_add hΔpos]; norm_num
    have hL : Z^((9:ℝ)/2) * Δ^(2:ℝ) * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) * M^(53:ℝ)
        = (Z^((9:ℝ)/2) * Z^((3:ℝ)/2)) * Δ^(2:ℝ) * M^(53:ℝ)
          + Z^((9:ℝ)/2) * (Δ^(2:ℝ) * Δ^((3:ℝ)/2)) * M^(53:ℝ) := by ring
    rw [hL, e1, e2]
  have hA : 0 ≤ Z^(6:ℝ) * Δ^(2:ℝ) * M^(53:ℝ) := by positivity
  have hB : 0 ≤ Z^((9:ℝ)/2) * Δ^((7:ℝ)/2) * M^(53:ℝ) := by positivity
  have hsum : M^(70:ℝ) * Z^(4:ℝ) * Δ^((7:ℝ)/2) + M^(70:ℝ) * Z^(6:ℝ) * Δ^((3:ℝ)/2)
      + M^(70:ℝ) * Z^(4:ℝ) * Δ^((11:ℝ)/3) + M^(40:ℝ) * Z^(4:ℝ) * Δ^(3:ℝ)
      + M^(40:ℝ) * Z^(6:ℝ) * Δ^(2:ℝ)
      ≤ 5 * (Z^((9:ℝ)/2) * Δ^(2:ℝ) * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) * M^(53:ℝ)) := by
    rw [hId]; linarith [hT1, hT2, hT3, hT4, hT5, hA, hB]
  calc CL1 * (M^(70:ℝ) * Z^(4:ℝ) * Δ^((7:ℝ)/2) + M^(70:ℝ) * Z^(6:ℝ) * Δ^((3:ℝ)/2)
        + M^(70:ℝ) * Z^(4:ℝ) * Δ^((11:ℝ)/3) + M^(40:ℝ) * Z^(4:ℝ) * Δ^(3:ℝ)
        + M^(40:ℝ) * Z^(6:ℝ) * Δ^(2:ℝ))
      ≤ CL1 * (5 * (Z^((9:ℝ)/2) * Δ^(2:ℝ) * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) * M^(53:ℝ))) :=
        mul_le_mul_of_nonneg_left hsum (le_of_lt hCL1)
    _ = (5 * CL1) * (Z^((9:ℝ)/2) * Δ^(2:ℝ) * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) * M^(53:ℝ)) := by ring

end Work.HP.Q44Main

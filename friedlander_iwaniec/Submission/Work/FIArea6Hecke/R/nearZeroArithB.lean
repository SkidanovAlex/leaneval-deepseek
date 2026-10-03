import Mathlib

namespace Work.FIArea6Hecke.R

theorem nearZeroArithB {C1 Csq Cnear cp L L₀ x β A B C : ℝ}
    (hC1 : 0 ≤ C1) (hCsq : 0 < Csq) (hCnear : 0 < Cnear)
    (hcppos : 0 < cp) (hcpK : cp * max 1 (3 * C1 + 2 * Csq + 4 * (Cnear + 7)) ≤ 1 / 4)
    (hL1 : 1 ≤ L) (hL2 : L ≤ 2 * L₀) (hL₀ : 0 < L₀) (hx : x = cp / L) (hβ : β ≤ 1)
    (hABC : 0 ≤ 3 * A + 4 * B + C) (hA : A ≤ 1 / x + C1) (hC : C ≤ 2 * Csq * L)
    (hB : B ≤ -(1 / (x + (1 - β))) + (Cnear + 7) * L) :
    cp / (16 * L₀) ≤ 1 - β := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hxpos : 0 < x := by rw [hx]; positivity
  have hs : 0 ≤ 1 - β := by linarith
  have hxs : 0 < x + (1 - β) := by linarith
  have h3C1_le : 3 * C1 ≤ max 1 (3 * C1 + 2 * Csq + 4 * (Cnear + 7)) := by
    apply le_trans _ (le_max_right _ _); nlinarith [hCsq, hCnear]
  have hM_le : 2 * Csq + 4 * (Cnear + 7) ≤ max 1 (3 * C1 + 2 * Csq + 4 * (Cnear + 7)) := by
    apply le_trans _ (le_max_right _ _); nlinarith [hC1]
  have h3C1cp : 3 * C1 * cp ≤ 1 / 4 := by
    have h1 : 3 * C1 * cp ≤ max 1 (3 * C1 + 2 * Csq + 4 * (Cnear + 7)) * cp :=
      mul_le_mul_of_nonneg_right h3C1_le (le_of_lt hcppos)
    nlinarith [h1, hcpK]
  have hMcp : (2 * Csq + 4 * (Cnear + 7)) * cp ≤ 1 / 4 := by
    have h1 : (2 * Csq + 4 * (Cnear + 7)) * cp ≤
        max 1 (3 * C1 + 2 * Csq + 4 * (Cnear + 7)) * cp :=
      mul_le_mul_of_nonneg_right hM_le (le_of_lt hcppos)
    nlinarith [h1, hcpK]
  have hxle : x ≤ cp := by
    rw [hx, div_le_iff₀ hLpos]; nlinarith
  have hP : 3 * C1 * x + (2 * Csq + 4 * (Cnear + 7)) * L * x ≤ 2⁻¹ := by
    have h1 : 3 * C1 * x ≤ 3 * C1 * cp := mul_le_mul_of_nonneg_left hxle (by linarith)
    have h2 : (2 * Csq + 4 * (Cnear + 7)) * L * x = (2 * Csq + 4 * (Cnear + 7)) * cp := by
      rw [hx]; field_simp
    linarith
  have hnonneg : 0 ≤ 3 / x + 3 * C1 - 4 / (x + (1 - β)) + (2 * Csq + 4 * (Cnear + 7)) * L := by
    have h3A : 3 * A ≤ 3 / x + 3 * C1 := by
      calc 3 * A ≤ 3 * (1 / x + C1) := mul_le_mul_of_nonneg_left hA (by norm_num)
        _ = 3 / x + 3 * C1 := by ring
    have h4B : 4 * B ≤ -(4 / (x + (1 - β))) + 4 * (Cnear + 7) * L := by
      calc 4 * B ≤ 4 * (-(1 / (x + (1 - β))) + (Cnear + 7) * L) :=
            mul_le_mul_of_nonneg_left hB (by norm_num)
        _ = -(4 / (x + (1 - β))) + 4 * (Cnear + 7) * L := by ring
    have hsum : 3 * A + 4 * B + C ≤
        3 / x + 3 * C1 - 4 / (x + (1 - β)) + (2 * Csq + 4 * (Cnear + 7)) * L := by
      nlinarith [h3A, h4B, hC]
    linarith
  have hdiv : 4 / (x + (1 - β)) ≤ 3 / x + 3 * C1 + (2 * Csq + 4 * (Cnear + 7)) * L := by
    linarith
  have hkey : 4 * x ≤ 3 * (x + (1 - β)) +
      (3 * C1 * x + (2 * Csq + 4 * (Cnear + 7)) * L * x) * (x + (1 - β)) := by
    rw [div_le_iff₀ hxs] at hdiv
    have h1 : 4 * x ≤ ((3 / x + (3 * C1 + (2 * Csq + 4 * (Cnear + 7)) * L)) *
        (x + (1 - β))) * x := by nlinarith [hdiv, hxpos]
    have h2 : ((3 / x + (3 * C1 + (2 * Csq + 4 * (Cnear + 7)) * L)) * (x + (1 - β))) * x
        = 3 * (x + (1 - β)) +
          (3 * C1 * x + (2 * Csq + 4 * (Cnear + 7)) * L * x) * (x + (1 - β)) := by
      field_simp
    linarith [h1, h2]
  have hx8 : x / 8 ≤ 1 - β := by nlinarith [hxpos, hs, hkey, hP]
  have hstep : cp / (16 * L₀) ≤ x / 8 := by
    have h16 : (0:ℝ) < 16 * L₀ := by positivity
    have h8 : (0:ℝ) < (8:ℝ) := by norm_num
    rw [div_le_div_iff₀ h16 h8, hx, div_mul_eq_mul_div]
    rw [le_div_iff₀ hLpos]
    nlinarith [hL2, hcppos]
  linarith [hstep, hx8]

end Work.FIArea6Hecke.R

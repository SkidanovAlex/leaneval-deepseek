import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem TL_bound {d h r : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 1 ≤ h) :
    (r:ℝ) * Real.log (r:ℝ) + 2*(r:ℝ)*((h:ℝ)+1) + 2*(r:ℝ)*Real.log (d:ℝ)
      + Real.log 2 + 50*Real.log (2*(r:ℝ)*(d:ℝ)) + Real.log (16*(r:ℝ)*(d:ℝ)*(h:ℝ))
      ≤ 124 * (r:ℝ)^3 * (h:ℝ) * (d:ℝ)^2 := by
  set R : ℝ := (r : ℝ) with hRdef
  set D : ℝ := (d : ℝ) with hDdef
  set H : ℝ := (h : ℝ) with hHdef
  have hR2 : (2:ℝ) ≤ R := by rw [hRdef]; exact_mod_cast hr
  have hD1 : (1:ℝ) ≤ D := by rw [hDdef]; exact_mod_cast hd
  have hH1 : (1:ℝ) ≤ H := by rw [hHdef]; exact_mod_cast hh
  have hRpos : 0 < R := by linarith
  have hDpos : 0 < D := by linarith
  have hHpos : 0 < H := by linarith
  have hR0 : (0:ℝ) ≤ R := le_of_lt hRpos
  have hR1 : (1:ℝ) ≤ R := by linarith
  have hR2sq : (4:ℝ) ≤ R^2 := by nlinarith
  have hD2sq : (1:ℝ) ≤ D^2 := by nlinarith
  have hRH' : (1:ℝ) ≤ R*H := by
    simpa using mul_le_mul hR1 hH1 (by norm_num) hR0
  have hRHD : (1:ℝ) ≤ R*H*D^2 := by
    simpa using mul_le_mul hRH' hD2sq (by norm_num) (by positivity : (0:ℝ) ≤ R*H)
  have hR2D2 : (4:ℝ) ≤ R^2*D^2 := by
    have h := mul_le_mul hR2sq hD2sq (by norm_num) (by positivity : (0:ℝ) ≤ R^2)
    simpa using h
  have hR2H : (4:ℝ) ≤ R^2*H := by
    have h := mul_le_mul hR2sq hH1 (by norm_num) (by positivity : (0:ℝ) ≤ R^2)
    simpa using h
  have hR2D : (4:ℝ) ≤ R^2*D := by
    have h := mul_le_mul hR2sq hD1 (by norm_num) (by positivity : (0:ℝ) ≤ R^2)
    simpa using h
  have hK : (4:ℝ) ≤ R^2*H*D := by
    have h := mul_le_mul hR2H hD1 (by norm_num) (by positivity : (0:ℝ) ≤ R^2*H)
    simpa using h
  have A1 : R^2 ≤ R^3*H*D^2 := by
    have h := mul_le_mul_of_nonneg_left hRHD (sq_nonneg R)
    nlinarith [h]
  have A2 : 4*R*H ≤ R^3*H*D^2 := by
    have h := mul_le_mul_of_nonneg_left hR2D2 (by positivity : (0:ℝ) ≤ R*H)
    nlinarith [h]
  have A3 : 2*R*D ≤ R^3*H*D^2 := by
    have h := mul_le_mul_of_nonneg_right (by linarith : (2:ℝ) ≤ R^2*H*D) (by positivity : (0:ℝ) ≤ R*D)
    nlinarith [h]
  have A4 : (1:ℝ) ≤ R^3*H*D^2 := by linarith [A1, hR2sq]
  have A5 : 100*R*D ≤ 25*(R^3*H*D^2) := by
    have h := mul_le_mul_of_nonneg_right hK (by positivity : (0:ℝ) ≤ R*D)
    nlinarith [h]
  have A6 : 16*R*D*H ≤ 4*(R^3*H*D^2) := by
    have h := mul_le_mul_of_nonneg_right hR2D (by positivity : (0:ℝ) ≤ R*D*H)
    nlinarith [h]
  have hSum : R^2 + 4*R*H + 102*R*D + 16*R*D*H + 1 ≤ 124 * R^3 * H * D^2 := by
    nlinarith [A1, A2, A3, A4, A5, A6]
  have hlogR : Real.log R ≤ R := Real.log_le_self hR0
  have L1 : R * Real.log R ≤ R^2 := by
    have h := mul_le_mul_of_nonneg_left hlogR hR0
    nlinarith [h]
  have L2 : 2*R*(H+1) ≤ 4*R*H := by
    have hHle : H + 1 ≤ 2*H := by linarith
    have h := mul_le_mul_of_nonneg_left hHle (by positivity : (0:ℝ) ≤ 2*R)
    nlinarith [h]
  have hlogD : Real.log D ≤ D := Real.log_le_self (le_of_lt hDpos)
  have L3 : 2*R*Real.log D ≤ 2*R*D := by
    have h := mul_le_mul_of_nonneg_left hlogD (by positivity : (0:ℝ) ≤ 2*R)
    nlinarith [h]
  have L4 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have L5 : 50*Real.log (2*R*D) ≤ 100*R*D := by
    have hx : (0:ℝ) < 2*R*D := by positivity
    have h := Real.log_le_self (le_of_lt hx)
    nlinarith [h]
  have L6 : Real.log (16*R*D*H) ≤ 16*R*D*H :=
    Real.log_le_self (by positivity : (0:ℝ) ≤ 16*R*D*H)
  linarith [L1, L2, L3, L4, L5, L6, hSum]

end Work.BW

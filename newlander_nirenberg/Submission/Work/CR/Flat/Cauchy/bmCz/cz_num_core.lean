import Mathlib

namespace Work.CR.Flat.Cauchy.bmCz

theorem cz_num_core {m : ℕ} (hm : 2 ≤ m) {X Y H : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (hH : 0 ≤ H) (hXY : |X - Y| ≤ H) (hYu : 2 * Y ≤ 3 * X) {A B : ℂ}
    (hB : ‖B‖ ≤ Y ^ 2) (hAB : ‖A - B‖ ≤ (5 / 2) * X * H) :
    ‖A * ((Y ^ m : ℝ) : ℂ) - B * ((X ^ m : ℝ) : ℂ)‖ / (X ^ m * Y ^ m)
      ≤ (5 / 2) * X * H / X ^ m + (m : ℝ) * (3 * X / 2) ^ (m - 1) * H * Y ^ 2 / (X ^ m * Y ^ m) := by
  have _hH' : 0 ≤ H := hH
  have hXm : (0:ℝ) < X ^ m := pow_pos hX m
  have hYm : (0:ℝ) < Y ^ m := pow_pos hY m
  have hden : (0:ℝ) < X ^ m * Y ^ m := mul_pos hXm hYm
  have hnY : ‖(((Y^m:ℝ)):ℂ)‖ = Y^m :=
    (RCLike.norm_ofReal (Y^m)).trans (abs_of_nonneg (le_of_lt hYm))
  have hnW : ‖(((Y^m - X^m:ℝ)):ℂ)‖ = |Y^m - X^m| := RCLike.norm_ofReal (Y^m - X^m)
  -- Key inequality: the mean-value bound on the difference of powers.
  have hkey : |Y ^ m - X ^ m| ≤ (m : ℝ) * (3 * X / 2) ^ (m - 1) * H := by
    have h1 : |Y ^ m - X ^ m| ≤ |Y - X| * (m:ℝ) * (max |Y| |X|) ^ (m - 1) :=
      abs_pow_sub_pow_le Y X m
    have h2 : |Y - X| = |X - Y| := abs_sub_comm Y X
    have h3 : max |Y| |X| = max Y X := by rw [abs_of_pos hY, abs_of_pos hX]
    have h4 : max Y X ≤ 3 * X / 2 := max_le (by linarith) (by linarith)
    have h5 : (0:ℝ) ≤ max Y X := le_max_of_le_left (le_of_lt hY)
    have h6 : (max Y X) ^ (m - 1) ≤ (3 * X / 2) ^ (m - 1) :=
      pow_le_pow_left₀ h5 h4 _
    have hcoef : (0:ℝ) ≤ (m:ℝ) * (3 * X / 2) ^ (m - 1) :=
      mul_nonneg (Nat.cast_nonneg m) (pow_nonneg (by positivity) _)
    calc |Y ^ m - X ^ m|
        ≤ |Y - X| * (m:ℝ) * (max |Y| |X|) ^ (m - 1) := h1
      _ = |X - Y| * (m:ℝ) * (max Y X) ^ (m - 1) := by rw [h2, h3]
      _ ≤ |X - Y| * (m:ℝ) * (3 * X / 2) ^ (m - 1) := by
            apply mul_le_mul_of_nonneg_left h6
            positivity
      _ = (m:ℝ) * (3 * X / 2) ^ (m - 1) * |X - Y| := by ring
      _ ≤ (m:ℝ) * (3 * X / 2) ^ (m - 1) * H := mul_le_mul_of_nonneg_left hXY hcoef
  -- Decompose $A Y^m - B X^m = (A-B)Y^m + B(Y^m - X^m)$ and bound its norm.
  have hnorm : ‖A * ((Y ^ m : ℝ) : ℂ) - B * ((X ^ m : ℝ) : ℂ)‖
      ≤ ‖A - B‖ * Y ^ m + ‖B‖ * |Y ^ m - X ^ m| := by
    have hdecomp : A * ((Y ^ m : ℝ) : ℂ) - B * ((X ^ m : ℝ) : ℂ)
        = (A - B) * ((Y ^ m : ℝ) : ℂ) + B * (((Y ^ m - X ^ m : ℝ)) : ℂ) := by
      rw [Complex.ofReal_sub]; ring
    rw [hdecomp]
    calc ‖(A - B) * ((Y ^ m : ℝ) : ℂ) + B * (((Y ^ m - X ^ m : ℝ)) : ℂ)‖
        ≤ ‖(A - B) * ((Y ^ m : ℝ) : ℂ)‖ + ‖B * (((Y ^ m - X ^ m : ℝ)) : ℂ)‖ :=
          norm_add_le _ _
      _ = ‖A - B‖ * Y ^ m + ‖B‖ * |Y ^ m - X ^ m| := by
          rw [norm_mul, norm_mul, hnY, hnW]
  have hT1 : ‖A - B‖ * Y ^ m ≤ (5/2 * X * H) * Y ^ m :=
    mul_le_mul_of_nonneg_right hAB (le_of_lt hYm)
  have hT2 : ‖B‖ * |Y ^ m - X ^ m| ≤ Y^2 * ((m:ℝ) * (3*X/2)^(m-1) * H) :=
    mul_le_mul hB hkey (abs_nonneg _) (by positivity)
  have htotal : ‖A * ((Y^m:ℝ):ℂ) - B * ((X^m:ℝ):ℂ)‖
      ≤ (5/2 * X * H) * Y^m + Y^2 * ((m:ℝ) * (3*X/2)^(m-1) * H) :=
    hnorm.trans (add_le_add hT1 hT2)
  have heq : ((5/2 * X * H) * Y^m + Y^2 * ((m:ℝ) * (3*X/2)^(m-1) * H)) / (X^m*Y^m)
      = (5/2) * X * H / X^m + (m:ℝ) * (3*X/2)^(m-1) * H * Y^2 / (X^m*Y^m) := by
    field_simp
  exact (div_le_div_of_nonneg_right htotal (le_of_lt hden)).trans (le_of_eq heq)

end Work.CR.Flat.Cauchy.bmCz

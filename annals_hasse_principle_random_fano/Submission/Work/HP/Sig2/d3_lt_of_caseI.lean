import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon

/-!
# Case I forces `𝔡₃(x,y) < 3n²‖x‖‖y‖/A`

In Case I (the complement of `𝔡₂³ ≤ 𝔡₃·‖x‖‖y‖`) the maximum inside
`muXY n x y = 3n² max (𝔡₂/𝔡₃) (‖x‖‖y‖/𝔡₂²)` is the first argument, so `muXY = 3n²𝔡₂/𝔡₃`.
Together with `A < muXY` and `𝔡₂ ≤ ‖x‖‖y‖` this gives `𝔡₃ < 3n²‖x‖‖y‖/A`.
-/

set_option autoImplicit false

noncomputable section

namespace Work.HP.Sig2

open Work.HP

/-- Case I implies `𝔡₃ < 3n²‖x‖‖y‖/A`. -/
theorem d3_lt_of_caseI (n : ℕ) (x y : Fin (n + 1) → ℤ) (A : ℝ)
    (hd2pos : 0 < dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
    (hd3pos : 0 < dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)))
    (hd2le : dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ≤ eNorm x * eNorm y)
    (hApos : 0 < A) (hA : A < muXY n x y)
    (hcase : ¬ (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) *
        dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2
        ≤ dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) * (eNorm x * eNorm y))) :
    dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))
      < 3 * (n : ℝ) ^ 2 * (eNorm x * eNorm y) / A := by
  set d2 := dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) with hd2def
  set d3 := dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) with hd3def
  set E := eNorm x * eNorm y with hEdef
  have hd2sqpos : 0 < d2 ^ 2 := by positivity
  -- Case I: the second argument of the `max` is strictly smaller
  have hlt : E / d2 ^ 2 < d2 / d3 := by
    rw [div_lt_div_iff₀ hd2sqpos hd3pos]
    have h := not_le.mp hcase
    nlinarith [h]
  have hmax : max (d2 / d3) (E / d2 ^ 2) = d2 / d3 := max_eq_left (le_of_lt hlt)
  have hmu : muXY n x y = 3 * (n : ℝ) ^ 2 * (d2 / d3) := by
    simp only [muXY, ← hd2def, ← hd3def, ← hEdef, hmax]
  rw [hmu] at hA
  have hc : (0:ℝ) ≤ 3 * (n : ℝ) ^ 2 := by positivity
  have h1 : A * d3 < 3 * (n : ℝ) ^ 2 * d2 := by
    have h := mul_lt_mul_of_pos_right hA hd3pos
    have h2 : 3 * (n : ℝ) ^ 2 * (d2 / d3) * d3 = 3 * (n : ℝ) ^ 2 * d2 := by
      field_simp
    linarith [h, h2]
  have h2 : d3 < 3 * (n : ℝ) ^ 2 * d2 / A := by
    rw [lt_div_iff₀ hApos]
    linarith [h1]
  calc d3 < 3 * (n : ℝ) ^ 2 * d2 / A := h2
    _ ≤ 3 * (n : ℝ) ^ 2 * E / A :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd2le hc) (le_of_lt hApos)

end Work.HP.Sig2

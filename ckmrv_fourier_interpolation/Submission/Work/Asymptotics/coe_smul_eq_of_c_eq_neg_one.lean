import Mathlib

namespace Work.Asymptotics

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane

/-- Casting `algebraMap ℤ ℝ` followed by the coercion to `ℂ` is the plain integer
coercion, used to normalise the formula for the Möbius action of `SL(2, ℤ)`. -/
private lemma algebraMap_int_cast_complex (n : ℤ) :
    (((algebraMap ℤ ℝ n : ℝ)) : ℂ) = (n : ℂ) := by
  simp

theorem coe_smul_eq_of_c_eq_neg_one {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ} (z : UpperHalfPlane)
    (hc : γ 1 0 = -1) :
    ((γ • z : UpperHalfPlane) : ℂ) = -((γ 0 0 : ℂ) + 1 / ((z : ℂ) - ((γ 1 1 : ℤ) : ℂ))) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  rw [algebraMap_int_cast_complex, algebraMap_int_cast_complex, algebraMap_int_cast_complex,
    algebraMap_int_cast_complex]
  rw [hc, show ((-1 : ℤ) : ℂ) = -1 from by norm_num]
  have hdet : ((γ 0 0 : ℤ) : ℂ) * ((γ 1 1 : ℤ) : ℂ) + ((γ 0 1 : ℤ) : ℂ) = 1 := by
    have h := γ.2
    rw [Matrix.det_fin_two] at h
    rw [hc] at h
    have h2 : (γ 0 0 : ℤ) * (γ 1 1 : ℤ) + (γ 0 1 : ℤ) = 1 := by linarith [h]
    exact_mod_cast h2
  have hb : ((γ 0 1 : ℤ) : ℂ) = 1 - ((γ 0 0 : ℤ) : ℂ) * ((γ 1 1 : ℤ) : ℂ) := by
    rw [← hdet]; ring
  rw [hb]
  have hz : (↑z : ℂ) - ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    exact z.im_ne_zero him
  rw [show (-1 : ℂ) * (↑z : ℂ) + ((γ 1 1 : ℤ) : ℂ)
        = -((↑z : ℂ) - ((γ 1 1 : ℤ) : ℂ)) by ring]
  rw [div_neg, neg_inj, div_eq_iff hz, add_mul, one_div, inv_mul_cancel₀ hz]
  ring

end Work.Asymptotics

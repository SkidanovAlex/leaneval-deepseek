/-
# The two tangency points `w = TST • i` and `-w̄ = ST • i`, and the Möbius formulas

The tangency arcs of the CKMRV domain `𝒟` (`Work.Asymptotics.arcT`) are the `SL(2,ℤ)`-orbits of
the elliptic point `i` under the four "grazing" elements
`T S T`, `(T S)⁻¹`, `S T`, `(T S T)⁻¹`.  Modulo sign these trace out exactly the two points

  `cR = T S T • i = (1 + i)/2`,    `cL = S T • i = (-1 + i)/2`,

and for a parameter `z = i t` on the imaginary axis the two coincidence points on the right arc are
`A • z` and `A • (S • z)` with `A = T S T`, and on the left arc the same with `A = S T`.
-/
import Mathlib
import Submission.Work.Asymptotics.Graze.Vanishing

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups

namespace Work.Asymptotics.Graze

/-- The right tangency point `T S T • i = (1+i)/2`. -/
def cR : ℍ := (ModularGroup.T * ModularGroup.S * ModularGroup.T) • UpperHalfPlane.I

/-- The left tangency point `S T • i = (-1+i)/2`. -/
def cL : ℍ := (ModularGroup.S * ModularGroup.T) • UpperHalfPlane.I

/-- The two `SL(2,ℤ)`-elements whose `i`-images are the tangency points. -/
def IsArc (A : SL(2, ℤ)) : Prop := A = ModularGroup.T * ModularGroup.S * ModularGroup.T
  ∨ A = ModularGroup.S * ModularGroup.T

lemma norm_one_add_I : ‖(1:ℂ) + Complex.I‖ = Real.sqrt 2 := by
  have h : ‖(1:ℂ) + Complex.I‖^2 = 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im]
    norm_num
  calc ‖(1:ℂ) + Complex.I‖ = Real.sqrt (‖(1:ℂ) + Complex.I‖^2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt 2 := by rw [h]

/-- The action of `T S T` on the upper half plane. -/
lemma coe_TST_smul (z : ℍ) :
    (((ModularGroup.T * ModularGroup.S * ModularGroup.T) • z : ℍ) : ℂ) = (z:ℂ) / ((z:ℂ) + 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T, ModularGroup.coe_S,
    Matrix.mul_apply, Fin.sum_univ_two]

/-- The action of `S T` on the upper half plane. -/
lemma coe_ST_smul (z : ℍ) :
    (((ModularGroup.S * ModularGroup.T) • z : ℍ) : ℂ) = -1 / ((z:ℂ) + 1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T, ModularGroup.coe_S,
    Matrix.mul_apply, Fin.sum_univ_two]

/-- The action of `(T S T)⁻¹` on the upper half plane. -/
lemma coe_TST_inv_smul (z : ℍ) :
    ((((ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹) • z : ℍ) : ℂ)
      = (z:ℂ) / (1 - (z:ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T, ModularGroup.coe_S,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf

/-- The action of `(S T)⁻¹` on the upper half plane. -/
lemma coe_ST_inv_smul (z : ℍ) :
    ((((ModularGroup.S * ModularGroup.T)⁻¹) • z : ℍ) : ℂ) = ((z:ℂ) + 1) / (-(z:ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T, ModularGroup.coe_S,
    Matrix.mul_apply, Fin.sum_univ_two]

/-- The action of `(T S)⁻¹` on the upper half plane. -/
lemma coe_TS_inv_smul (z : ℍ) :
    ((((ModularGroup.T * ModularGroup.S)⁻¹) • z : ℍ) : ℂ) = 1 / (1 - (z:ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T, ModularGroup.coe_S,
    Matrix.mul_apply, Fin.sum_univ_two]
  ring_nf

/-- `T S T • i = (1 + i)/2`. -/
lemma cST_I : (((ModularGroup.T * ModularGroup.S * ModularGroup.T) • UpperHalfPlane.I : ℍ) : ℂ)
    = (1 + Complex.I) / 2 := by
  rw [coe_TST_smul, UpperHalfPlane.coe_I]
  rw [div_eq_div_iff]
  · ring_nf; rw [Complex.I_sq]; ring
  · intro h; have := congrArg Complex.re h; simp at this
  · norm_num

/-- `S T • i = (-1 + i)/2`. -/
lemma cST_I' : (((ModularGroup.S * ModularGroup.T) • UpperHalfPlane.I : ℍ) : ℂ)
    = (-1 + Complex.I) / 2 := by
  rw [coe_ST_smul, UpperHalfPlane.coe_I]
  rw [div_eq_div_iff]
  · ring_nf; rw [Complex.I_sq]; ring
  · intro h; have := congrArg Complex.re h; simp at this
  · norm_num

lemma cR_coe : ((cR : ℍ) : ℂ) = (1 + Complex.I) / 2 := cST_I
lemma cL_coe : ((cL : ℍ) : ℂ) = (-1 + Complex.I) / 2 := cST_I'

lemma cR_im : cR.im = 1 / 2 := by
  rw [← UpperHalfPlane.coe_im, cR_coe]
  simp [Complex.add_im]

lemma cL_im : cL.im = 1 / 2 := by
  rw [← UpperHalfPlane.coe_im, cL_coe]
  simp [Complex.add_im]

lemma norm_one_sub_I : ‖(1:ℂ) - Complex.I‖ = Real.sqrt 2 := by
  have h : ‖(1:ℂ) - Complex.I‖^2 = 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im]
    norm_num
  calc ‖(1:ℂ) - Complex.I‖ = Real.sqrt (‖(1:ℂ) - Complex.I‖^2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt 2 := by rw [h]

lemma norm_sqrt2_div_two : Real.sqrt 2 / 2 = 1 / Real.sqrt 2 := by
  rw [div_eq_div_iff (by norm_num) (by positivity)]
  ring_nf
  rw [Real.sq_sqrt (by norm_num)]

lemma cR_norm : ‖((cR : ℍ) : ℂ)‖ = Real.sqrt 2 / 2 := by
  rw [cR_coe, norm_div, norm_one_add_I]
  rw [show ‖(2:ℂ)‖ = 2 from by norm_num]

lemma cL_norm : ‖((cL : ℍ) : ℂ)‖ = Real.sqrt 2 / 2 := by
  rw [cL_coe]
  have h1 : ((-1 : ℂ) + Complex.I) / 2 = -((1 - Complex.I) / 2) := by ring
  rw [h1, norm_neg]
  have h2 : ((1:ℂ) - Complex.I) / 2 = ((1:ℂ) + -Complex.I) / 2 := by ring
  rw [h2, show (1:ℂ) + -Complex.I = 1 - Complex.I from by ring, norm_div, norm_one_sub_I]
  rw [show ‖(2:ℂ)‖ = 2 from by norm_num]

end Work.Asymptotics.Graze

namespace Work.Asymptotics.Graze

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups

/-- Lower bounds on moduli from a squared lower bound. -/
lemma half_le_norm_of_normSq {w : ℂ} (h : (1:ℝ)/4 ≤ Complex.normSq w) : (1:ℝ)/2 ≤ ‖w‖ := by
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg w]

lemma IsArc_I_eq (A : SL(2,ℤ)) (hA : IsArc A) :
    A • UpperHalfPlane.I = cR ∨ A • UpperHalfPlane.I = cL := by
  rcases hA with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma IsArc_im_I (A : SL(2,ℤ)) (hA : IsArc A) : (A • UpperHalfPlane.I).im = 1 / 2 := by
  rcases IsArc_I_eq A hA with h | h <;> rw [h]
  · exact cR_im
  · exact cL_im

lemma sqrt2_half_sub_sixteenth : (1:ℝ)/2 ≤ Real.sqrt 2 / 2 - 1/16 := by
  have h5 : (9:ℝ)/8 ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  linarith

lemma sqrt2_half_pos : (0:ℝ) < Real.sqrt 2 / 2 := by
  have : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  linarith

/-- `‖A • i‖ = √2/2` for the two tangency elements. -/
lemma IsArc_I_norm (A : SL(2,ℤ)) (hA : IsArc A) :
    ‖((A • UpperHalfPlane.I : ℍ) : ℂ)‖ = Real.sqrt 2 / 2 := by
  rcases IsArc_I_eq A hA with h | h
  · rw [h]; exact cR_norm
  · rw [h]; exact cL_norm

/-- `√2/2 ≤ ‖1 - A • i‖` for the two tangency elements. -/
lemma IsArc_I_one_sub_norm (A : SL(2,ℤ)) (hA : IsArc A) :
    Real.sqrt 2 / 2 ≤ ‖1 - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ := by
  rcases IsArc_I_eq A hA with h | h
  · rw [h, cR_coe]
    have h1 : (1:ℂ) - (1 + Complex.I)/2 = (1 - Complex.I)/2 := by ring
    rw [h1, norm_div, norm_one_sub_I, show ‖(2:ℂ)‖ = 2 from by norm_num]
  · rw [h, cL_coe]
    have h1 : (1:ℂ) - (-1 + Complex.I)/2 = (3 - Complex.I)/2 := by ring
    rw [h1]
    have h2 : (Real.sqrt 2 / 2)^2 ≤ ‖((3:ℂ) - Complex.I)/2‖^2 := by
      have he : (Real.sqrt 2 / 2)^2 = (1:ℝ)/2 := by
        rw [div_pow, Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]; norm_num
      rw [he, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im]
      norm_num
    nlinarith [norm_nonneg (((3:ℂ) - Complex.I)/2)]

/-- The `•`-difference of `A`: `A z - A w = (z - w)/((z+1)(w+1))` for both tangency elements. -/
lemma IsArc_smul_sub (A : SL(2,ℤ)) (hA : IsArc A) (z w : ℍ) :
    (((A • z : ℍ) : ℂ)) - (((A • w : ℍ) : ℂ))
      = ((z : ℂ) - (w : ℂ)) / (((z : ℂ) + 1) * ((w : ℂ) + 1)) := by
  have hz : ((z:ℂ) + 1) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp [UpperHalfPlane.coe_im, z.im_pos.ne'] at this
  have hw : ((w:ℂ) + 1) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp [UpperHalfPlane.coe_im, w.im_pos.ne'] at this
  rcases hA with rfl | rfl
  · rw [coe_TST_smul, coe_TST_smul]; field_simp; ring
  · rw [coe_ST_smul, coe_ST_smul]
    field_simp
    ring_nf

/-- The `•`-difference of `(T S T)⁻¹`. -/
lemma TST_inv_smul_sub (u v : ℍ) :
    ((((ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹) • u : ℍ) : ℂ)
      - ((((ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹) • v : ℍ) : ℂ)
      = ((u:ℂ) - (v:ℂ)) / ((1 - (u:ℂ)) * (1 - (v:ℂ))) := by
  rw [coe_TST_inv_smul, coe_TST_inv_smul]
  have hu : (1 - (u:ℂ)) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp [UpperHalfPlane.coe_im, u.im_pos.ne'] at this
  have hv : (1 - (v:ℂ)) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp [UpperHalfPlane.coe_im, v.im_pos.ne'] at this
  field_simp
  ring

/-- The `•`-difference of `(S T)⁻¹`. -/
lemma ST_inv_smul_sub (u v : ℍ) :
    ((((ModularGroup.S * ModularGroup.T)⁻¹) • u : ℍ) : ℂ)
      - ((((ModularGroup.S * ModularGroup.T)⁻¹) • v : ℍ) : ℂ)
      = ((u:ℂ) - (v:ℂ)) / ((u:ℂ) * (v:ℂ)) := by
  rw [coe_ST_inv_smul, coe_ST_inv_smul]
  have hu : (u:ℂ) ≠ 0 := UpperHalfPlane.ne_zero u
  have hv : (v:ℂ) ≠ 0 := UpperHalfPlane.ne_zero v
  field_simp
  ring_nf

/-- On the disc of radius `1/16` around `i`: `1/2 ≤ ‖z‖`. -/
lemma half_le_norm_of_near_I {z : ℍ} (hz : ‖(z:ℂ) - Complex.I‖ < 1/16) :
    (1:ℝ)/2 ≤ ‖(z:ℂ)‖ := by
  have h : ‖(Complex.I:ℂ)‖ ≤ ‖(z:ℂ)‖ + ‖(z:ℂ) - Complex.I‖ := by
    have := norm_sub_le (z:ℂ) ((z:ℂ) - Complex.I)
    rw [show (z:ℂ) - ((z:ℂ) - Complex.I) = Complex.I by ring] at this
    exact this
  rw [Complex.norm_I] at h
  linarith

/-- On the disc of radius `1/16` around `i`: `1/2 ≤ ‖z + 1‖`. -/
lemma half_le_norm_add_one_of_near_I {z : ℍ} (hz : ‖(z:ℂ) - Complex.I‖ < 1/16) :
    (1:ℝ)/2 ≤ ‖(z:ℂ) + 1‖ := by
  have h : ‖(1:ℂ) + Complex.I‖ ≤ ‖(z:ℂ) + 1‖ + ‖(z:ℂ) - Complex.I‖ := by
    have := norm_sub_le ((z:ℂ) + 1) ((z:ℂ) - Complex.I)
    rw [show (z:ℂ) + 1 - ((z:ℂ) - Complex.I) = 1 + Complex.I by ring] at this
    exact this
  rw [norm_one_add_I] at h
  linarith [sqrt2_half_sub_sixteenth]

/-- On the disc of radius `1/16` around `i`: `1/2 ≤ ‖1 - z‖`. -/
lemma half_le_norm_one_sub_of_near_I {z : ℍ} (hz : ‖(z:ℂ) - Complex.I‖ < 1/16) :
    (1:ℝ)/2 ≤ ‖1 - (z:ℂ)‖ := by
  have h : ‖(1:ℂ) - Complex.I‖ ≤ ‖1 - (z:ℂ)‖ + ‖(z:ℂ) - Complex.I‖ := by
    have := norm_add_le (1 - (z:ℂ)) ((z:ℂ) - Complex.I)
    rw [show 1 - (z:ℂ) + ((z:ℂ) - Complex.I) = 1 - Complex.I by ring] at this
    exact this
  rw [norm_one_sub_I] at h
  linarith [sqrt2_half_sub_sixteenth]

/-- On the disc of radius `1/16` around `A • i`: `1/2 ≤ ‖u‖`. -/
lemma half_le_norm_of_near_cI {A : SL(2,ℤ)} (hA : IsArc A) {u : ℍ}
    (hu : ‖(u:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ < 1/16) :
    (1:ℝ)/2 ≤ ‖(u:ℂ)‖ := by
  have h : ‖((A • UpperHalfPlane.I : ℍ) : ℂ)‖
      ≤ ‖(u:ℂ)‖ + ‖(u:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ := by
    have := norm_sub_le (u:ℂ) ((u:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ))
    rw [show (u:ℂ) - ((u:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ))
        = ((A • UpperHalfPlane.I : ℍ) : ℂ) by ring] at this
    exact this
  rw [IsArc_I_norm A hA] at h
  linarith [sqrt2_half_sub_sixteenth]

/-- On the disc of radius `1/16` around `A • i`: `1/2 ≤ ‖1 - u‖`. -/
lemma half_le_norm_one_sub_of_near_cI {A : SL(2,ℤ)} (hA : IsArc A) {u : ℍ}
    (hu : ‖(u:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ < 1/16) :
    (1:ℝ)/2 ≤ ‖1 - (u:ℂ)‖ := by
  have h : ‖1 - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖
      ≤ ‖1 - (u:ℂ)‖ + ‖(u:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ := by
    have := norm_add_le (1 - (u:ℂ)) ((u:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ))
    rw [show 1 - (u:ℂ) + ((u:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ))
        = 1 - ((A • UpperHalfPlane.I : ℍ) : ℂ) by ring] at this
    exact this
  have h2 := IsArc_I_one_sub_norm A hA
  linarith [sqrt2_half_sub_sixteenth]

end Work.Asymptotics.Graze

namespace Work.Asymptotics.Graze

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups

lemma one_le_sqrt_two_sub_sixteenth : (1:ℝ) ≤ Real.sqrt 2 - 1/16 := by
  have h5 : (17:ℝ)/16 ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  linarith

/-- On the disc of radius `1/16` around `i`: `1/2 ≤ ‖S z + 1‖`. -/
lemma half_le_norm_one_add_S_of_near_I {z : ℍ} (hz : ‖(z:ℂ) - Complex.I‖ < 1/16) :
    (1:ℝ)/2 ≤ ‖((ModularGroup.S • z : ℍ) : ℂ) + 1‖ := by
  have hS : ((ModularGroup.S • z : ℍ) : ℂ) = (-(z:ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]
  have hz0 : (z:ℂ) ≠ 0 := UpperHalfPlane.ne_zero z
  have h1 : (-(z:ℂ))⁻¹ + 1 = ((z:ℂ) - 1)/(z:ℂ) := by
    field_simp
    ring
  rw [hS, h1, norm_div]
  have hnum : (1:ℝ) ≤ ‖(z:ℂ) - 1‖ := by
    have h3 : ‖(1:ℂ) - (z:ℂ)‖ = ‖(z:ℂ) - 1‖ := norm_sub_rev _ _
    have h4 := half_le_norm_one_sub_of_near_I hz
    rw [h3] at h4
    have h5 : ‖(1:ℂ) - Complex.I‖ ≤ ‖1 - (z:ℂ)‖ + ‖(z:ℂ) - Complex.I‖ := by
      have := norm_add_le (1 - (z:ℂ)) ((z:ℂ) - Complex.I)
      rw [show 1 - (z:ℂ) + ((z:ℂ) - Complex.I) = 1 - Complex.I by ring] at this
      exact this
    rw [norm_one_sub_I] at h5
    linarith [one_le_sqrt_two_sub_sixteenth]
  have hden : ‖(z:ℂ)‖ ≤ 2 := by
    have h : ‖(z:ℂ)‖ ≤ ‖(Complex.I:ℂ)‖ + ‖(z:ℂ) - Complex.I‖ := by
      have := norm_add_le Complex.I ((z:ℂ) - Complex.I)
      rw [show (Complex.I:ℂ) + ((z:ℂ) - Complex.I) = (z:ℂ) by ring] at this
      exact this
    rw [Complex.norm_I] at h
    linarith
  have hpos : (0:ℝ) < ‖(z:ℂ)‖ := by
    have := half_le_norm_of_near_I hz; linarith
  rw [le_div_iff₀ hpos]
  linarith

/-- Upper bound for the `A⁻¹`-difference near the tangency point. -/
lemma IsArc_inv_smul_sub_le (A : SL(2,ℤ)) (hA : IsArc A) {u v : ℍ}
    (hu : ‖(u:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ < 1/16)
    (hv : ‖(v:ℂ) - ((A • UpperHalfPlane.I : ℍ) : ℂ)‖ < 1/16) :
    ‖(((A⁻¹) • u : ℍ) : ℂ) - (((A⁻¹) • v : ℍ) : ℂ)‖ ≤ 4 * ‖(u:ℂ) - (v:ℂ)‖ := by
  rcases hA with hA | hA
  · subst hA
    rw [TST_inv_smul_sub, norm_div, norm_mul]
    have h1 := half_le_norm_one_sub_of_near_cI (A := ModularGroup.T * ModularGroup.S * ModularGroup.T)
      (Or.inl rfl) hu
    have h2 := half_le_norm_one_sub_of_near_cI (A := ModularGroup.T * ModularGroup.S * ModularGroup.T)
      (Or.inl rfl) hv
    have h5 : (1:ℝ) ≤ 4 * (‖1 - (u:ℂ)‖ * ‖1 - (v:ℂ)‖) := by
      nlinarith [h1, h2]
    rw [div_le_iff₀ (by positivity)]
    calc ‖(u:ℂ) - (v:ℂ)‖ = ‖(u:ℂ) - (v:ℂ)‖ * 1 := by ring
      _ ≤ ‖(u:ℂ) - (v:ℂ)‖ * (4 * (‖1 - (u:ℂ)‖ * ‖1 - (v:ℂ)‖)) :=
            mul_le_mul_of_nonneg_left h5 (norm_nonneg _)
      _ = 4 * ‖(u:ℂ) - (v:ℂ)‖ * (‖1 - (u:ℂ)‖ * ‖1 - (v:ℂ)‖) := by ring
  · subst hA
    rw [ST_inv_smul_sub, norm_div, norm_mul]
    have h1 := half_le_norm_of_near_cI (A := ModularGroup.S * ModularGroup.T) (Or.inr rfl) hu
    have h2 := half_le_norm_of_near_cI (A := ModularGroup.S * ModularGroup.T) (Or.inr rfl) hv
    have h5 : (1:ℝ) ≤ 4 * (‖(u:ℂ)‖ * ‖(v:ℂ)‖) := by nlinarith [h1, h2]
    rw [div_le_iff₀ (by positivity)]
    calc ‖(u:ℂ) - (v:ℂ)‖ = ‖(u:ℂ) - (v:ℂ)‖ * 1 := by ring
      _ ≤ ‖(u:ℂ) - (v:ℂ)‖ * (4 * (‖(u:ℂ)‖ * ‖(v:ℂ)‖)) :=
            mul_le_mul_of_nonneg_left h5 (norm_nonneg _)
      _ = 4 * ‖(u:ℂ) - (v:ℂ)‖ * (‖(u:ℂ)‖ * ‖(v:ℂ)‖) := by ring

end Work.Asymptotics.Graze

/-
# The two arc matrices of `U₀` and their Möbius actions

`Work.CKFinal.U0` is the strip `-1 < Re τ < 1` with the four closed discs of radius `1/4`
centred at `±1/4`, `±3/4` removed.  Its two "bottom" ideal triangles, `(0, 1/2, 1)` and
`(-1, -1/2, 0)`, are the points of `U₀` lying strictly inside the discs `|τ ∓ 1/2| < 1/2`.

The present file records the two elements of `SL(2,ℤ)`

* `Work.CKFinal.Gam1 = !![1, 0; -1, 1]`, whose Möbius action is `τ ↦ τ / (1 - τ)` and which maps
  the triangle `(0, 1/2, 1)` onto `(0, 1, ∞)`,
* `Work.CKFinal.Gam2 = !![1, 0; 1, 1]`, whose Möbius action is `τ ↦ τ / (1 + τ)` and which maps
  the triangle `(-1, -1/2, 0)` onto `(-1, 0, ∞)`,

together with the coordinate computation identifying the vanishing of the real part of the image
with the boundary arcs of `U₀`:

* `Re (Gam1 • τ) = 0 ↔ ‖τ - 1/2‖ = 1/2`,
* `Re (Gam2 • τ) = 0 ↔ ‖τ + 1/2‖ = 1/2`.

The two remaining facts -- that `Gam1` (resp. `Gam2`) sends the part of `U₀` inside
`‖τ - 1/2‖ < 1/2` (resp. `‖τ + 1/2‖ < 1/2`) into the CKMRV domain
`Work.Asymptotics.DomainD` -- are delegated to
`Work.CKFinal.gam1_smul_mem_DomainD` and `Work.CKFinal.gam2_smul_mem_DomainD`.
-/
import Mathlib

noncomputable section

open scoped MatrixGroups
open UpperHalfPlane

namespace Work.CKFinal

/-- The element `!![1, 0; -1, 1]` of `SL(2,ℤ)`, i.e. the element whose Möbius action is
`τ ↦ τ / (1 - τ)`.  (Its negative `!![-1, 0; 1, -1]` has the same action but also determinant `1`;
here we take this representative, of determinant `1`.) -/
def Gam1 : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨!![1, 0; -1, 1], by decide⟩

/-- The element `!![1, 0; 1, 1]` of `SL(2,ℤ)`, whose Möbius action is `τ ↦ τ / (1 + τ)`. -/
def Gam2 : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨!![1, 0; 1, 1], by decide⟩

@[simp] lemma Gam1_val : (Gam1 : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -1, 1] := rfl

@[simp] lemma Gam2_val : (Gam2 : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 1, 1] := rfl

/-- The Möbius action of `Gam1` is `τ ↦ τ / (1 - τ)`. -/
theorem coe_Gam1_smul (τ : ℍ) : ((Gam1 • τ : ℍ) : ℂ) = (τ : ℂ) / (1 - (τ : ℂ)) := by
  rw [coe_specialLinearGroup_apply]
  simp [Gam1]
  ring

/-- The Möbius action of `Gam2` is `τ ↦ τ / (1 + τ)`. -/
theorem coe_Gam2_smul (τ : ℍ) : ((Gam2 • τ : ℍ) : ℂ) = (τ : ℂ) / (1 + (τ : ℂ)) := by
  rw [coe_specialLinearGroup_apply]
  simp [Gam2]
  ring

/-- For a complex number of nonnegative norm, `‖z‖ = 1/2` is equivalent to `‖z‖ ^ 2 = 1/4`. -/
lemma norm_eq_half_iff (z : ℂ) : ‖z‖ = 1 / 2 ↔ ‖z‖ ^ 2 = 1 / 4 := by
  constructor
  · intro h; rw [h]; norm_num
  · intro h
    have h' : ‖z‖ ^ 2 = (1 / 2) ^ 2 := by norm_num at h ⊢; exact h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h' with h'' | h''
    · exact h''
    · linarith [norm_nonneg z]

/-- The squared distance from `τ` to `1/2`, in coordinates. -/
lemma norm_sq_sub_half (τ : ℍ) : ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 - τ.re + 1 / 4 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have h3 : ((τ : ℂ) - (1 / 2 : ℂ)).re = τ.re - 1 / 2 := by simp [Complex.sub_re]
  have h4 : ((τ : ℂ) - (1 / 2 : ℂ)).im = τ.im := by simp [Complex.sub_im]
  rw [h3, h4]; ring

/-- The squared distance from `τ` to `-1/2`, in coordinates. -/
lemma norm_sq_add_half (τ : ℍ) : ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 + τ.re + 1 / 4 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have h3 : ((τ : ℂ) + (1 / 2 : ℂ)).re = τ.re + 1 / 2 := by simp [Complex.add_re]
  have h4 : ((τ : ℂ) + (1 / 2 : ℂ)).im = τ.im := by simp [Complex.add_im]
  rw [h3, h4]; ring

/-- **The bottom-right arc is exactly the preimage of the imaginary axis under `Gam1`.** -/
theorem re_Gam1_smul_eq_zero_iff (τ : ℍ) :
    (((Gam1 • τ : ℍ) : ℂ).re = 0) ↔ ‖(τ : ℂ) - (1 / 2 : ℂ)‖ = 1 / 2 := by
  rw [coe_Gam1_smul]
  have h1 : (1 - (τ : ℂ)).re = 1 - τ.re := by simp
  have h2 : (1 - (τ : ℂ)).im = -τ.im := by simp
  have hre : (τ : ℂ).re = τ.re := by simp
  have him : (τ : ℂ).im = τ.im := by simp
  have hD : Complex.normSq (1 - (τ : ℂ)) = (1 - τ.re) ^ 2 + τ.im ^ 2 := by
    rw [Complex.normSq_apply, h1, h2]; ring
  rw [Complex.div_re, hre, him, h1, h2, hD]
  have hDpos : 0 < (1 - τ.re) ^ 2 + τ.im ^ 2 := by nlinarith [τ.im_pos, sq_nonneg (1 - τ.re)]
  have hDne : (1 - τ.re) ^ 2 + τ.im ^ 2 ≠ 0 := ne_of_gt hDpos
  rw [← add_div, div_eq_zero_iff, or_iff_left hDne]
  constructor
  · intro h
    have h2' : ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = 1 / 4 := by rw [norm_sq_sub_half]; nlinarith
    exact (norm_eq_half_iff _).mpr h2'
  · intro h
    have h2' : ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = 1 / 4 := (norm_eq_half_iff _).mp h
    rw [norm_sq_sub_half] at h2'
    nlinarith

/-- **The bottom-left arc is exactly the preimage of the imaginary axis under `Gam2`.** -/
theorem re_Gam2_smul_eq_zero_iff (τ : ℍ) :
    (((Gam2 • τ : ℍ) : ℂ).re = 0) ↔ ‖(τ : ℂ) + (1 / 2 : ℂ)‖ = 1 / 2 := by
  rw [coe_Gam2_smul]
  have h1 : (1 + (τ : ℂ)).re = 1 + τ.re := by simp
  have h2 : (1 + (τ : ℂ)).im = τ.im := by simp
  have hre : (τ : ℂ).re = τ.re := by simp
  have him : (τ : ℂ).im = τ.im := by simp
  have hD : Complex.normSq (1 + (τ : ℂ)) = (1 + τ.re) ^ 2 + τ.im ^ 2 := by
    rw [Complex.normSq_apply, h1, h2]; ring
  rw [Complex.div_re, hre, him, h1, h2, hD]
  have hDpos : 0 < (1 + τ.re) ^ 2 + τ.im ^ 2 := by nlinarith [τ.im_pos, sq_nonneg (1 + τ.re)]
  have hDne : (1 + τ.re) ^ 2 + τ.im ^ 2 ≠ 0 := ne_of_gt hDpos
  rw [← add_div, div_eq_zero_iff, or_iff_left hDne]
  constructor
  · intro h
    have h2' : ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = 1 / 4 := by rw [norm_sq_add_half]; nlinarith
    exact (norm_eq_half_iff _).mpr h2'
  · intro h
    have h2' : ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = 1 / 4 := (norm_eq_half_iff _).mp h
    rw [norm_sq_add_half] at h2'
    nlinarith

end Work.CKFinal

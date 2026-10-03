/-
# `Work.FIArea3.JointCount.angSector_geom_defs`

Two elementary planar helpers used by the convex-hull estimates for angular sectors:
`cs φ` is the unit vector at angle `φ`, and `crs u v = u.re * v.im - u.im * v.re` is the
signed area (2-dimensional cross product) of `u` and `v`.
-/
import Mathlib

namespace Work.FIArea3.JointCount

noncomputable section

/-- The unit vector at angle `φ`, as a complex number. -/
def cs (φ : ℝ) : ℂ := ⟨Real.cos φ, Real.sin φ⟩

/-- The signed area / cross product `u.re * v.im - u.im * v.re` of two complex numbers. -/
def crs (u v : ℂ) : ℝ := u.re * v.im - u.im * v.re

@[simp] lemma cs_re (φ : ℝ) : (cs φ).re = Real.cos φ := rfl
@[simp] lemma cs_im (φ : ℝ) : (cs φ).im = Real.sin φ := rfl

lemma normSq_cs (φ : ℝ) : Complex.normSq (cs φ) = 1 := by
  rw [Complex.normSq_apply, cs_re, cs_im]
  nlinarith [Real.cos_sq_add_sin_sq φ]

lemma norm_cs (φ : ℝ) : ‖cs φ‖ = 1 := by
  have h : ‖cs φ‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq, normSq_cs]
  nlinarith [norm_nonneg (cs φ)]

@[simp] lemma crs_apply (u v : ℂ) : crs u v = u.re * v.im - u.im * v.re := rfl

end

end Work.FIArea3.JointCount

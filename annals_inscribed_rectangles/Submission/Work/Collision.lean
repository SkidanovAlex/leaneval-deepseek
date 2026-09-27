import Mathlib
import ChallengeDeps
import Submission.Work.Geometry

open InscribedRectangles
open Manifold Real MeasureTheory
open scoped ContDiff ENNReal

set_option autoImplicit false
noncomputable section

namespace Submission.Collision

/-- The doubled (undirected) direction of a vector of `ℝ × ℝ`, as an element of `ℝ/ℤ`: the class of
`arg / π`, where `(x,y)` is identified with the complex number `x + y i`. -/
def dirC (p : ℝ × ℝ) : UnitAddCircle := ((Complex.arg ⟨p.1, p.2⟩ / Real.pi : ℝ) : UnitAddCircle)

lemma normC_eq_eucNorm (p : ℝ × ℝ) : ‖(⟨p.1, p.2⟩ : ℂ)‖ = Geometry.eucNorm p := by
  rw [Complex.norm_def, Complex.normSq_apply, Geometry.eucNorm, Geometry.eucDot]

/-- Given two vectors of `ℝ × ℝ` of equal Euclidean norm whose doubled directions `arg / π ∈ ℝ/ℤ`
differ by `θ/(2π)`, there is an angle `φ` with `w = ‖v‖ • (cos φ, sin φ)` and
`v = ± ‖v‖ • (cos (φ - θ/2), sin (φ - θ/2))`. -/
theorem exists_angle_of_dir_eq {v w : ℝ × ℝ} {θ : ℝ}
    (hn : ‖(⟨v.1, v.2⟩ : ℂ)‖ = ‖(⟨w.1, w.2⟩ : ℂ)‖)
    (hdir : dirC w = dirC v + ((θ / (2 * Real.pi) : ℝ) : UnitAddCircle)) :
    ∃ φ : ℝ, w = (‖(⟨v.1, v.2⟩ : ℂ)‖) • (Real.cos φ, Real.sin φ) ∧
      (v = (‖(⟨v.1, v.2⟩ : ℂ)‖) • (Real.cos (φ - θ / 2), Real.sin (φ - θ / 2)) ∨
       -v = (‖(⟨v.1, v.2⟩ : ℂ)‖) • (Real.cos (φ - θ / 2), Real.sin (φ - θ / 2))) := by
  set z : ℂ := ⟨v.1, v.2⟩ with hz
  set ζ : ℂ := ⟨w.1, w.2⟩ with hζ
  have hdir' : ((ζ.arg / Real.pi : ℝ) : UnitAddCircle)
      = ((z.arg / Real.pi + θ / (2 * Real.pi) : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_add]
    exact hdir
  have hzero : (↑(ζ.arg / Real.pi - (z.arg / Real.pi + θ / (2 * Real.pi)) : ℝ) :
      UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, hdir', sub_self]
  obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  rw [zsmul_one] at hk
  have harg : z.arg = ζ.arg - θ / 2 - k * Real.pi := by
    have h := hk
    field_simp at h
    linarith
  refine ⟨ζ.arg, ?_, ?_⟩
  · have h2 : ζ.re = w.1 := by rw [hζ]
    have h3 : ζ.im = w.2 := by rw [hζ]
    have hre : w.1 = ‖z‖ * Real.cos ζ.arg := by
      rw [← h2, ← Complex.norm_mul_cos_arg ζ, hn]
    have him : w.2 = ‖z‖ * Real.sin ζ.arg := by
      rw [← h3, ← Complex.norm_mul_sin_arg ζ, hn]
    ext <;> simp [hre, him]
  · have h4 : z.re = v.1 := by rw [hz]
    have h5 : z.im = v.2 := by rw [hz]
    have hzre : v.1 = ‖z‖ * Real.cos z.arg := by
      rw [← h4, ← Complex.norm_mul_cos_arg z]
    have hzim : v.2 = ‖z‖ * Real.sin z.arg := by
      rw [← h5, ← Complex.norm_mul_sin_arg z]
    have hcos : Real.cos z.arg = (-1) ^ k * Real.cos (ζ.arg - θ / 2) := by
      rw [harg, Real.cos_sub_int_mul_pi]
    have hsin : Real.sin z.arg = (-1) ^ k * Real.sin (ζ.arg - θ / 2) := by
      rw [harg, Real.sin_sub_int_mul_pi]
    rcases Int.even_or_odd k with hk | hk
    · left
      rw [hcos, hk.neg_one_zpow, one_mul] at hzre
      rw [hsin, hk.neg_one_zpow, one_mul] at hzim
      ext <;> simp [hzre, hzim]
    · right
      rw [hcos, hk.neg_one_zpow] at hzre
      rw [hsin, hk.neg_one_zpow] at hzim
      ext <;> simp [hzre, hzim]

/-- **Final geometric step of the reduction of Theorem 1.** Two chords of the plane with a common
midpoint `m`, equal half-length `c`, and doubled directions differing by `θ ∈ (0, π]` produce an
inscribed rectangle in `γ` of aspect ratio `tan (θ/4)`; hence `θ/π ∈ X γ`. -/
theorem member_of_X_of_collision {γ : Circle → ℝ × ℝ} {m v w : ℝ × ℝ} {c θ : ℝ}
    (hc : 0 < c) (hθpos : 0 < θ) (hθπ : θ ≤ π)
    (hv : Geometry.eucNorm v = c) (hw : Geometry.eucNorm w = c)
    (hdir : dirC w = dirC v + ((θ / (2 * Real.pi) : ℝ) : UnitAddCircle))
    (hmv : m + v ∈ Set.range γ) (hmv' : m - v ∈ Set.range γ)
    (hmw : m + w ∈ Set.range γ) (hmw' : m - w ∈ Set.range γ) :
    θ / π ∈ X γ := by
  have hn : ‖(⟨v.1, v.2⟩ : ℂ)‖ = ‖(⟨w.1, w.2⟩ : ℂ)‖ := by
    rw [normC_eq_eucNorm, normC_eq_eucNorm, hv, hw]
  obtain ⟨φ, hwφ, hvφ⟩ := exists_angle_of_dir_eq (v := v) (w := w) hn hdir
  have hwφ' : w = c • Geometry.uv φ := by
    rw [hwφ, show ‖(⟨v.1, v.2⟩ : ℂ)‖ = c from by rw [normC_eq_eucNorm, hv],
      Geometry.uv_mk]
  rcases hvφ with hvφ | hvφ
  · have hvφ' : v = c • Geometry.uv (φ - θ / 2) := by
      rw [hvφ, show ‖(⟨v.1, v.2⟩ : ℂ)‖ = c from by rw [normC_eq_eucNorm, hv],
        Geometry.uv_mk]
    exact Geometry.member_of_X_of_angle_chords hc hθpos hθπ
      (by rw [← hwφ']; exact hmw) (by rw [← hwφ']; exact hmw')
      (by rw [← hvφ']; exact hmv) (by rw [← hvφ']; exact hmv')
  · have hvφ' : -v = c • Geometry.uv (φ - θ / 2) := by
      rw [hvφ, show ‖(⟨v.1, v.2⟩ : ℂ)‖ = c from by rw [normC_eq_eucNorm, hv],
        Geometry.uv_mk]
    exact Geometry.member_of_X_of_angle_chords hc hθpos hθπ
      (by rw [← hwφ']; exact hmw) (by rw [← hwφ']; exact hmw')
      (by rw [← hvφ']; simpa [sub_eq_add_neg] using hmv')
      (by rw [← hvφ']; simpa [sub_neg_eq_add] using hmv)

end Submission.Collision

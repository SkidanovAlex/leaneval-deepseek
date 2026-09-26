import Mathlib
import Submission.Work.Smooth.SphereJordan.PCopy.halfAnnulusSetup

/-!
# `pcbdVec` lands on the boundary of the rectangle of radial coordinates

`pcbdVec z` is defined in `Submission/Work/SphereJordan/halfAnnulusSetup.lean` by a case distinction on
the signs of `Re z` and `Im z`, one branch for each side of the rectangle
`pcupRect = [1/2,1] × [0,π]` of radial coordinates of the upper half pcannulus.  Here we check that
each branch really does produce a point of the closed rectangle `pcupRect`, lying on its boundary
`pcupRectBd`.

The only analytic input is the standard range of `Real.arcsin`: `arcsin t ≤ π/2` for all `t`, and
`0 ≤ arcsin t` for `t ≥ 0`.  (In the second and fourth branches the argument is
`-Im z / ‖z‖ ≥ 0`, which holds because `Im z < 0` there.)
-/

open Set

namespace Work.SphereJordan

/-- A point of the plane with the four rectangular bounds lies in `pcupRect`. -/
lemma pcmem_upRect_of_bounds {p : ℝ × ℝ} (h₁ : 1 / 2 ≤ p.1) (h₂ : p.1 ≤ 1) (h₃ : 0 ≤ p.2)
    (h₄ : p.2 ≤ Real.pi) : p ∈ pcupRect := ⟨h₁, h₂, h₃, h₄⟩

/-- A point of the plane with the four rectangular bounds, one coordinate at an endpoint, lies in
the boundary `pcupRectBd` of `pcupRect`. -/
lemma pcmem_upRectBd_of_bounds {p : ℝ × ℝ} (h₁ : 1 / 2 ≤ p.1) (h₂ : p.1 ≤ 1) (h₃ : 0 ≤ p.2)
    (h₄ : p.2 ≤ Real.pi) (hb : p.1 = 1 / 2 ∨ p.1 = 1 ∨ p.2 = 0 ∨ p.2 = Real.pi) :
    p ∈ pcupRectBd := ⟨pcmem_upRect_of_bounds h₁ h₂ h₃ h₄, hb⟩

/-- For `Im z ≥ 0` the quotient `Im z / ‖z‖` is nonnegative, hence so is its arcsine. -/
lemma pcarcsin_div_norm_nonneg (z : ℂ) (h : 0 ≤ z.im) : 0 ≤ Real.arcsin (z.im / ‖z‖) :=
  Real.arcsin_nonneg.mpr (div_nonneg h (norm_nonneg z))

/-- The arcsine of `Im z / ‖z‖` is at most `π/2`. -/
lemma pcarcsin_div_norm_le (z : ℂ) : Real.arcsin (z.im / ‖z‖) ≤ Real.pi / 2 :=
  Real.arcsin_le_pi_div_two _

/-- For `Im z ≤ 0` the quotient `-Im z / ‖z‖` is nonnegative, hence so is its arcsine. -/
lemma pcarcsin_neg_div_norm_nonneg (z : ℂ) (h : z.im ≤ 0) : 0 ≤ Real.arcsin (-z.im / ‖z‖) :=
  Real.arcsin_nonneg.mpr (div_nonneg (by linarith) (norm_nonneg z))

theorem pcbdVec_mem_upRectBd (z : ℂ) : Work.SphereJordan.pcbdVec z ∈ Work.SphereJordan.pcupRectBd := by
  rw [pcbdVec]
  split_ifs with h1 h2
  · -- `Im z ≥ 0`, `Re z ≥ 0`: the point `(1, 2 arcsin (Im z / ‖z‖))` on the right side
    have h₃ : 0 ≤ Real.arcsin (z.im / ‖z‖) := pcarcsin_div_norm_nonneg z h1
    have h₄ : Real.arcsin (z.im / ‖z‖) ≤ Real.pi / 2 := pcarcsin_div_norm_le z
    exact pcmem_upRectBd_of_bounds (by norm_num) (by norm_num) (by linarith) (by linarith)
      (Or.inr (Or.inl rfl))
  · -- `Im z ≥ 0`, `Re z < 0`: the point `(1/2 + arcsin (Im z / ‖z‖)/π, π)` on the top side
    have h₃ : 0 ≤ Real.arcsin (z.im / ‖z‖) / Real.pi :=
      div_nonneg (pcarcsin_div_norm_nonneg z h1) Real.pi_pos.le
    have h₄ : Real.arcsin (z.im / ‖z‖) / Real.pi ≤ 1 / 2 := by
      rw [div_le_iff₀ Real.pi_pos]
      linarith [pcarcsin_div_norm_le z]
    exact pcmem_upRectBd_of_bounds (by linarith) (by linarith) Real.pi_pos.le le_rfl
      (Or.inr (Or.inr (Or.inr rfl)))
  · -- `Im z < 0`, `Re z ≥ 0`: the point `(1 - arcsin (-Im z / ‖z‖)/π, 0)` on the bottom side
    have h₁ : Real.arcsin (-z.im / ‖z‖) / Real.pi ≤ 1 / 2 := by
      rw [div_le_iff₀ Real.pi_pos]
      linarith [Real.arcsin_le_pi_div_two (-z.im / ‖z‖)]
    have h₂ : 0 ≤ Real.arcsin (-z.im / ‖z‖) / Real.pi :=
      div_nonneg (pcarcsin_neg_div_norm_nonneg z (by linarith)) Real.pi_pos.le
    exact pcmem_upRectBd_of_bounds (by linarith) (by linarith) le_rfl Real.pi_pos.le
      (Or.inr (Or.inr (Or.inl rfl)))
  · -- `Im z < 0`, `Re z < 0`: the point `(1/2, π - 2 arcsin (-Im z / ‖z‖))` on the left side
    have h₃ : 0 ≤ Real.pi - 2 * Real.arcsin (-z.im / ‖z‖) := by
      linarith [Real.arcsin_le_pi_div_two (-z.im / ‖z‖)]
    have h₄ : Real.pi - 2 * Real.arcsin (-z.im / ‖z‖) ≤ Real.pi := by
      linarith [pcarcsin_neg_div_norm_nonneg z (by linarith)]
    exact pcmem_upRectBd_of_bounds (by norm_num) (by norm_num) h₃ h₄ (Or.inl rfl)

end Work.SphereJordan

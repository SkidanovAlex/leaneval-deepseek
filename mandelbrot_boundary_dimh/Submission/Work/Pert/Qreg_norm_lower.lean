import Mathlib
import Submission.Work.Interfaces.Fatou

/-!
# Geometry of Shishikura's region `Qreg`: a norm bound on the two "ends"

`MandelDim.Qreg b₁ b₂` is Shishikura's region `𝒬(b₁,b₂)` (see
`Submission/Work/Interfaces/Fatou.lean`):

* `b₁ = some a` imposes `-|(z - a).im| < (z - a).re`, i.e. `z` lies strictly to the right of the
  "wedge" centred at `a`;
* `b₂ = some b` imposes `(z - b).re < |(z - b).im|`, i.e. `z` lies strictly to the left of the
  "wedge" centred at `b`.

This file records the elementary consequences used by the perturbation layer (`Work.Pert`):

* for a real vertex `ξ > 0`, the region with a lower vertex `ξ` (and no upper vertex) is contained
  in the complement of the closed ball of radius `ξ/2`;
* symmetrically, the region with only an upper vertex `-ξ` is contained in the complement of the
  closed ball of radius `ξ/2`;
* consequently every vertical line contained in either region satisfies the corresponding
  one-sided bound on its real part (`Re ≥ ξ` resp. `Re ≤ -ξ`).
-/

namespace Work.Pert

open Complex

theorem Qreg_norm_lower {ξ : ℝ} (hξ : 0 < ξ) :
    (∀ z ∈ MandelDim.Qreg (some (ξ : ℂ)) none, ξ / 2 < ‖z‖) ∧
    (∀ z ∈ MandelDim.Qreg none (some (-(ξ : ℂ))), ξ / 2 < ‖z‖) ∧
    (∀ x : ℝ, (∀ y : ℝ, (x : ℂ) + y * I ∈ MandelDim.Qreg (some (ξ : ℂ)) none) → ξ ≤ x) ∧
    (∀ x : ℝ, (∀ y : ℝ, (x : ℂ) + y * I ∈ MandelDim.Qreg none (some (-(ξ : ℂ)))) → x ≤ -ξ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- lower vertex `ξ`: `z.re + |z.im| > ξ`, while both are `≤ ‖z‖`.
    intro z hz
    have h := hz.1 (ξ : ℂ) rfl
    have h₁ : (z - (ξ : ℂ)).re = z.re - ξ := by simp
    have h₂ : (z - (ξ : ℂ)).im = z.im := by simp
    rw [h₁, h₂] at h
    have h₃ : z.re ≤ |z.re| := le_abs_self _
    have h₄ : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have h₅ : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    linarith
  · -- upper vertex `-ξ`: `z.re + ξ < |z.im| ≤ ‖z‖` and `z.re ≥ -‖z‖`.
    intro z hz
    have h := hz.2 (-(ξ : ℂ)) rfl
    have h₁ : (z - (-(ξ : ℂ))).re = z.re + ξ := by simp
    have h₂ : (z - (-(ξ : ℂ))).im = z.im := by simp
    rw [h₁, h₂] at h
    have h₃ : -|z.re| ≤ z.re := neg_abs_le _
    have h₄ : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
    have h₅ : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    linarith
  · -- the vertical line through `x`: use `y = 0`.
    intro x hx
    have h := (hx 0).1 (ξ : ℂ) rfl
    have h₁ : ((x : ℂ) + (0 : ℝ) * I - (ξ : ℂ)).re = x - ξ := by simp
    have h₂ : ((x : ℂ) + (0 : ℝ) * I - (ξ : ℂ)).im = 0 := by simp
    rw [h₁, h₂] at h
    simp only [abs_zero, neg_zero] at h
    linarith
  · intro x hx
    have h := (hx 0).2 (-(ξ : ℂ)) rfl
    have h₁ : ((x : ℂ) + (0 : ℝ) * I - (-(ξ : ℂ))).re = x + ξ := by simp
    have h₂ : ((x : ℂ) + (0 : ℝ) * I - (-(ξ : ℂ))).im = 0 := by simp
    rw [h₁, h₂] at h
    simp only [abs_zero] at h
    linarith

end Work.Pert

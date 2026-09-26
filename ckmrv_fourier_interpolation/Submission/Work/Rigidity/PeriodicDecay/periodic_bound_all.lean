import Mathlib
import Submission.Work.Rigidity.Basic
import Submission.Work.Rigidity.Diff

namespace Work.Rigidity.PeriodicDecay

open Work.Rigidity

/-- A `1`-periodic function on `ℍ` (invariant under `τ ↦ τ + 1`) is invariant under horizontal
shifts by any integer. -/
lemma vadd_int_eq {f : UpperHalfPlane → ℂ}
    (hper : ∀ τ : UpperHalfPlane, f ((1 : ℝ) +ᵥ τ) = f τ)
    (τ : UpperHalfPlane) (m : ℤ) :
    f ((m : ℝ) +ᵥ τ) = f τ := by
  have hFper : Function.Periodic (fun x : ℝ => f (x +ᵥ τ)) 1 := by
    intro x
    show f ((x + 1) +ᵥ τ) = f (x +ᵥ τ)
    have h : (x + 1) +ᵥ τ = (1 : ℝ) +ᵥ (x +ᵥ τ) := by
      rw [UpperHalfPlane.ext_iff]
      simp only [UpperHalfPlane.coe_vadd]
      push_cast
      ring
    rw [h, hper]
  have h0 := (hFper.int_mul m) 0
  simp only [mul_one, zero_add] at h0
  rw [h0]
  congr 1
  rw [UpperHalfPlane.ext_iff]
  simp

theorem periodic_bound_all {u : UpperHalfPlane → ℂ} {Ψ : ℝ → ℝ}
    (hper : ∀ τ : UpperHalfPlane, u ((1 : ℝ) +ᵥ τ) = u τ)
    (h : ∀ τ : UpperHalfPlane, Work.Rigidity.InStrip τ → 1 ≤ τ.im →
      ‖u τ‖ ≤ Ψ τ.im * Real.exp (-(2 * Real.pi * τ.im))) :
    ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖u τ‖ ≤ Ψ τ.im * Real.exp (-(2 * Real.pi * τ.im)) := by
  intro τ hτ
  -- Shift `τ` horizontally by the integer `⌊τ.re⌋` so that its real part lies in `[0, 1)`.
  set m : ℤ := ⌊τ.re⌋
  set σ : UpperHalfPlane := (-(m : ℝ)) +ᵥ τ
  have hσ_re : σ.re = τ.re - m := by
    rw [Work.Rigidity.re_vadd]
    ring
  have hσ_im : σ.im = τ.im := by rw [Work.Rigidity.im_vadd]
  have hstrip : Work.Rigidity.InStrip σ := by
    constructor
    · rw [hσ_re]
      have h1 := Int.floor_le τ.re
      linarith
    · rw [hσ_re]
      have h1 := Int.lt_floor_add_one τ.re
      linarith
  have hshift : u σ = u τ := by
    have hh := vadd_int_eq hper τ (-m)
    simpa [σ] using hh
  have hσ_im_ge : 1 ≤ σ.im := by rw [hσ_im]; exact hτ
  have hb := h σ hstrip hσ_im_ge
  rw [hσ_im, hshift] at hb
  exact hb

end Work.Rigidity.PeriodicDecay

import Mathlib
import Submission.Work.Rigidity.Basic
import Submission.Work.Rigidity.Diff

namespace Work.Rigidity.PeriodicDecay

open Work.Rigidity

/-- A `1`-periodic function on `ℍ` (invariant under `τ ↦ τ + 1`) is invariant under shifts
by any integer. -/
lemma fstDiff_vadd_int {f : UpperHalfPlane → ℂ}
    (hper : ∀ τ : UpperHalfPlane, fstDiff f ((1 : ℝ) +ᵥ τ) = fstDiff f τ)
    (τ : UpperHalfPlane) (m : ℤ) :
    fstDiff f ((m : ℝ) +ᵥ τ) = fstDiff f τ := by
  have hFper : Function.Periodic (fun x : ℝ => fstDiff f (x +ᵥ τ)) 1 := by
    intro x
    show fstDiff f ((x + 1) +ᵥ τ) = fstDiff f (x +ᵥ τ)
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

theorem fstDiff_bound_all {c : ℝ} {f : UpperHalfPlane → ℂ} {ψ : ℝ → ℝ}
    (hper : ∀ τ : UpperHalfPlane,
      Work.Rigidity.fstDiff f ((1 : ℝ) +ᵥ τ) = Work.Rigidity.fstDiff f τ)
    (hbd : ∀ τ : UpperHalfPlane, Work.Rigidity.InStrip τ →
      ‖Work.Rigidity.fstDiff f τ‖ ≤ ψ τ.im * Real.exp (-(2 * Real.pi * c * τ.im))) :
    ∀ τ : UpperHalfPlane,
      ‖Work.Rigidity.fstDiff f τ‖ ≤ ψ τ.im * Real.exp (-(2 * Real.pi * c * τ.im)) := by
  intro τ
  -- Shift `τ` horizontally by the integer `⌊τ.re⌋` so that its real part lies in `[0, 1)`.
  set m : ℤ := ⌊τ.re⌋
  set u : UpperHalfPlane := (-(m : ℝ)) +ᵥ τ
  have hu_re : u.re = τ.re - m := by
    rw [Work.Rigidity.re_vadd]
    ring
  have hu_im : u.im = τ.im := by rw [Work.Rigidity.im_vadd]
  have hstrip : Work.Rigidity.InStrip u := by
    constructor
    · rw [hu_re]
      have h1 := Int.floor_le τ.re
      linarith
    · rw [hu_re]
      have h1 := Int.lt_floor_add_one τ.re
      linarith
  have hshift : Work.Rigidity.fstDiff f u = Work.Rigidity.fstDiff f τ := by
    have h := fstDiff_vadd_int hper τ (-m)
    simpa [u] using h
  have h := hbd u hstrip
  rw [hu_im, hshift] at h
  exact h

end Work.Rigidity.PeriodicDecay

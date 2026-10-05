import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPV.VBasic
import Submission.Work.RPV.dchord_symplectic

/-!
# Injectivity of the chord differential (`Work.RPB.B2.dchord_injective`)

`dchord z w a ζ η` is the differential of the chord map `chordPS` at `(z,w)`
(with `a` a lift of `arg (z - w)`).  The statement proved here says that for `z ≠ w`
this linear map `ℂ × ℂ → PS = ℝ⁴` has trivial kernel.

The proof does **not** unfold `dchord` at all.  It uses the symplectic compatibility
proved in `Work.RPV.dchord_symplectic`:

`symp (dchord z w a ζ₁ η₁) (dchord z w a ζ₂ η₂) = ωC ζ₁ ζ₂ + ωC η₁ η₂`.

If `dchord z w a ζ η = 0` then pairing against every `dchord z w a ζ₂ η₂` gives
`ωC ζ ζ₂ + ωC η η₂ = 0`.  Choosing `η₂ = 0` and then `ζ₂ = 0` separates the two terms,
and `ωC u (u * I) = ‖u‖ ^ 2` (`Work.RPV.ωC_mul_I`) makes each of them vanish alone.
-/

open Complex

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B2

/-- An ℝ-bilinear form `ωC` on `ℂ` with `ωC u (u * I) = ‖u‖ ^ 2` has trivial kernel. -/
private lemma eq_zero_of_forall_ωC_eq_zero {u : ℂ} (h : ∀ v : ℂ, Work.RPV.ωC u v = 0) :
    u = 0 := by
  have h2 : Work.RPV.ωC u (u * I) = 0 := h (u * I)
  rw [Work.RPV.ωC_mul_I] at h2
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h2)

theorem dchord_injective (z w : ℂ) (a : ℝ) (hzw : z ≠ w)
    (harg : z - w = (‖z - w‖ : ℂ) * Complex.exp (a * I)) (ζ η : ℂ) :
    Work.RPV.dchord z w a ζ η = 0 → ζ = 0 ∧ η = 0 := by
  intro h
  -- Pairing the vanishing vector against every other vector of the image isolates `ζ` and `η`.
  have hsymp : ∀ ζ₂ η₂ : ℂ, Work.RPV.ωC ζ ζ₂ + Work.RPV.ωC η η₂ = 0 := by
    intro ζ₂ η₂
    have h1 := Work.RPV.dchord_symplectic z w a hzw harg ζ η ζ₂ η₂
    rw [h] at h1
    rw [← h1]
    simp [Work.RPV.symp]
  have hωζ : ∀ ζ₂ : ℂ, Work.RPV.ωC ζ ζ₂ = 0 := by
    intro ζ₂
    have h2 := hsymp ζ₂ 0
    simpa only [Work.RPV.ωC, mul_zero, Complex.zero_im, add_zero] using h2
  have hωη : ∀ η₂ : ℂ, Work.RPV.ωC η η₂ = 0 := by
    intro η₂
    have h2 := hsymp 0 η₂
    simpa only [Work.RPV.ωC, mul_zero, Complex.zero_im, zero_add] using h2
  exact ⟨eq_zero_of_forall_ωC_eq_zero hωζ, eq_zero_of_forall_ωC_eq_zero hωη⟩

end Work.RPB.B2

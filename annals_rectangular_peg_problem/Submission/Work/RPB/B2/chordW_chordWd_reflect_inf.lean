import Mathlib
import Submission.Work.RPB.B2.PhaseDefs
import Submission.Work.RPB.B2.chordVec_eq_mul_chordW_inf
import Submission.Work.RPB.B2.chordW_chordWd_reflect

/-!
# Reflection of the divided chord under the chord swap, for `C^∞` curves

This is the smooth (`C^∞`, i.e. `ContDiff ℝ ∞`) counterpart of `chordW_chordWd_reflect`, which
assumes the stronger analyticity hypothesis `ContDiff ℝ ⊤`.  Nothing in the argument beyond
`chordVec c τ t r = r · chordW c τ t r` is used, and that identity is available at `C^∞` strength as
`chordVec_eq_mul_chordW_inf`.

The chord swap `(t, r) ↦ (t + π, π - r)` reverses the chord direction,

  `chordVec c τ (t + π) (π - r) = - chordVec c τ t r`   (`chordVec_swap`, needs only periodicity),

and dividing by `r` gives the weighted reflection law of the divided chord

  `chordW c τ (t + π) (π - r) = -(r/(π - r)) · chordW c τ t r`,  `0 < r < π`,

for every `τ`; the same law for the `τ`-derivative `chordWd` follows because the scalar factor
`-(r/(π-r))` does not depend on `τ`.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B2

theorem chordW_chordWd_reflect_inf (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => c z.1 z.2))
    (hper : ∀ τ t, c τ (t + 2 * Real.pi) = c τ t) (τ t r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Work.RPB.B2.chordW c τ (t + Real.pi) (Real.pi - r)
        = ((-(r / (Real.pi - r)) : ℝ) : ℂ) * Work.RPB.B2.chordW c τ t r ∧
    Work.RPB.B2.chordWd c τ (t + Real.pi) (Real.pi - r)
        = ((-(r / (Real.pi - r)) : ℝ) : ℂ) * Work.RPB.B2.chordWd c τ t r := by
  -- the factor `π - r` is nonzero because `r < π`
  have hne : ((π - r : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]
    linarith [hr.2]
  have hcoef : ((π - r : ℝ) : ℂ) * ((-(r / (π - r)) : ℝ) : ℂ) = -(r : ℂ) := by
    have hne' : (π - r : ℝ) ≠ 0 := by linarith [hr.2]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.ofReal_inj]
    field_simp
  -- the reflection law of the divided chord, for *every* `σ` (needed for the `τ`-derivative)
  have key : ∀ σ : ℝ, Work.RPB.B2.chordW c σ (t + π) (π - r)
      = ((-(r / (π - r)) : ℝ) : ℂ) * Work.RPB.B2.chordW c σ t r := by
    intro σ
    -- the chord swap reverses the chord vector
    have hveceq : Work.RPB.chordVec c σ (t + π) (π - r) = -Work.RPB.chordVec c σ t r :=
      chordVec_swap c hper σ t r
    -- express both chord vectors through the divided chord
    rw [chordVec_eq_mul_chordW_inf c hc σ (t + π) (π - r),
        chordVec_eq_mul_chordW_inf c hc σ t r] at hveceq
    -- cancel the common factor `π - r`
    apply mul_left_cancel₀ hne
    rw [hveceq]
    rw [show ((π - r : ℝ) : ℂ) * (((-(r / (π - r)) : ℝ) : ℂ) * Work.RPB.B2.chordW c σ t r)
        = (((π - r : ℝ) : ℂ) * ((-(r / (π - r)) : ℝ) : ℂ)) * Work.RPB.B2.chordW c σ t r
        from by ring]
    rw [hcoef]
    ring
  refine ⟨key τ, ?_⟩
  -- the `τ`-derivative: the scalar factor is independent of `τ`
  rw [Work.RPB.B2.chordWd, Work.RPB.B2.chordWd, funext key, deriv_const_mul_field]

end Work.RPB.B2

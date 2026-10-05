import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPV.VBasic
import Submission.Work.RPV.chordPS_phase_rev
import Submission.Work.RPV.chord_ends_ne
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.Defs

/-!
# B5: the middle part of `ℓ` is a chord of the curve (`Work.RPB.B5.lagPt_chord`)

The family `ℓ τ (x,t) = lagPt W Γc Ac rho τ x t` of `Defs.lean` is the chord chart `W` of the
chord annulus on the region `|x| < √2` (on `x > 0` it is the `τ_π`-image of the left half).
This module proves the second extra conjunct of node B5: for `|x| < √2` the point `ℓ τ (x,t)` really
is the image under `chordPS` of a genuine chord `(c τ t₁, c τ t₂)` of the curve `c = CI.c` at time
`τ`, with `a'` a lift of the argument of `c τ t₁ - c τ t₂`.

## Proof

Since `|x| < √2`, the branch `x ≤ -√2` of `basePt` (the collar) is never taken:

* for `x ≤ 0`: `lagPt τ x t = basePt τ x t = W τ t (ρ τ x t)`, and with `r = √(ρ τ x t) ∈ (0, π/2]`
  (because `0 < ρ ≤ π²/4` on `x ∈ (-√2,0]` by `hrho`) the hypothesis `hchord` gives
  `W τ t (r^2) = chordSurf c a τ t r = chordPS (c τ (t+r)) (c τ (t-r)) (a τ t r)`; the phase
  equation is `ha.2.1` and `c τ (t+r) ≠ c τ (t-r)` is `Work.RPV.chord_ends_ne`;
* for `x > 0`: `lagPt τ x t = τ_π (basePt τ (-x) (t-π))`, and the same computation at
  `(t-π, -x)` gives `τ_π (chordPS z w a) = chordPS w z (a+π)` by `Work.RPV.chordPS_swap`; the phase
  of the reversed chord `w - z` is `a + π` by `Work.RPV.chordPS_phase_rev`, and the endpoints are
  again distinct.

The `C^8`-hypothesis `hW` is not used: only the reduction `W τ t (r^2) = chordSurf …` matters.
-/

open RectangularPegProblem
open Manifold Complex Real

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

theorem lagPt_chord (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (ρ₀ : ℝ) (W : ℝ → ℝ → ℝ → Work.RPV.PS)
    (hW : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => W z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hchord : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2),
        W τ t (r ^ 2) = Work.RPB.chordSurf CI.c a τ t r)
    (Γc : ℝ → ℝ → ℝ → ℂ) (Ac : ℝ → ℝ → ℝ → ℝ) (rho : ℝ → ℝ → ℝ → ℝ)
    (hrho : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x ∈ Set.Ioc (-Real.sqrt 2) 0, ∀ t : ℝ,
      0 < rho τ x t ∧ rho τ x t ≤ Real.pi ^ 2 / 4) :
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ x t : ℝ, |x| < Real.sqrt 2 →
      ∃ t₁ t₂ a' : ℝ, CI.c τ t₁ ≠ CI.c τ t₂ ∧
        CI.c τ t₁ - CI.c τ t₂ = (‖CI.c τ t₁ - CI.c τ t₂‖ : ℂ) * Complex.exp (a' * Complex.I) ∧
        lagPt W Γc Ac rho τ x t = Work.RPV.chordPS (CI.c τ t₁) (CI.c τ t₂) a' := by
  intro τ hτ x t hx
  have hx1 : -Real.sqrt 2 < x := (abs_lt.mp hx).1
  have hx2 : x < Real.sqrt 2 := (abs_lt.mp hx).2
  by_cases hxle : x ≤ 0
  · -- ## the left half: the chord chart itself
    obtain ⟨hr0, hr1⟩ := hrho τ hτ x ⟨hx1, hxle⟩ t
    let r : ℝ := Real.sqrt (rho τ x t)
    have hrsq : r ^ 2 = rho τ x t := by
      show Real.sqrt (rho τ x t) ^ 2 = rho τ x t
      exact Real.sq_sqrt hr0.le
    have hrpos : 0 < r := by
      show 0 < Real.sqrt (rho τ x t)
      exact Real.sqrt_pos.mpr hr0
    have hrle : r ≤ Real.pi / 2 := by
      show Real.sqrt (rho τ x t) ≤ Real.pi / 2
      calc Real.sqrt (rho τ x t) ≤ Real.sqrt (Real.pi ^ 2 / 4) := Real.sqrt_le_sqrt hr1
        _ = Real.pi / 2 := by
            rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
            exact Real.sqrt_sq (by positivity)
    have hrpi : r ∈ Set.Ioo (0 : ℝ) Real.pi := ⟨hrpos, by linarith [Real.pi_pos, hrle]⟩
    have hch := hchord τ hτ t r ⟨hrpos, hrle⟩
    refine ⟨t + r, t - r, a τ t r,
      Work.RPV.chord_ends_ne CI hτ (t := t) (r := r) ⟨hrpos, hrle⟩, ?_, ?_⟩
    · simpa only [Work.RPB.chordVec] using ha.2.1 τ hτ t r hrpi
    · rw [lagPt, if_pos hxle, basePt, if_neg (not_le.mpr hx1), ← hrsq]
      exact hch
  · -- ## the right half: the `τ_π`-image of the (reflected) chord chart
    have hxpos : 0 < x := not_le.mp hxle
    have hnx1 : -Real.sqrt 2 < -x := by linarith
    have hnx0 : -x ≤ 0 := by linarith
    obtain ⟨hr0, hr1⟩ := hrho τ hτ (-x) ⟨hnx1, hnx0⟩ (t - Real.pi)
    let r : ℝ := Real.sqrt (rho τ (-x) (t - Real.pi))
    have hrsq : r ^ 2 = rho τ (-x) (t - Real.pi) := by
      show Real.sqrt (rho τ (-x) (t - Real.pi)) ^ 2 = rho τ (-x) (t - Real.pi)
      exact Real.sq_sqrt hr0.le
    have hrpos : 0 < r := by
      show 0 < Real.sqrt (rho τ (-x) (t - Real.pi))
      exact Real.sqrt_pos.mpr hr0
    have hrle : r ≤ Real.pi / 2 := by
      show Real.sqrt (rho τ (-x) (t - Real.pi)) ≤ Real.pi / 2
      calc Real.sqrt (rho τ (-x) (t - Real.pi)) ≤ Real.sqrt (Real.pi ^ 2 / 4) :=
            Real.sqrt_le_sqrt hr1
        _ = Real.pi / 2 := by
            rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
            exact Real.sqrt_sq (by positivity)
    have hrpi : r ∈ Set.Ioo (0 : ℝ) Real.pi := ⟨hrpos, by linarith [Real.pi_pos, hrle]⟩
    have hch := hchord τ hτ (t - Real.pi) r ⟨hrpos, hrle⟩
    refine ⟨(t - Real.pi) - r, (t - Real.pi) + r, a τ (t - Real.pi) r + Real.pi, ?_, ?_, ?_⟩
    · exact Ne.symm
        (Work.RPV.chord_ends_ne CI hτ (t := t - Real.pi) (r := r) ⟨hrpos, hrle⟩)
    · have h0 : CI.c τ ((t - Real.pi) + r) - CI.c τ ((t - Real.pi) - r) =
          (‖CI.c τ ((t - Real.pi) + r) - CI.c τ ((t - Real.pi) - r)‖ : ℂ) *
            Complex.exp (a τ (t - Real.pi) r * Complex.I) :=
        by simpa only [Work.RPB.chordVec] using ha.2.1 τ hτ (t - Real.pi) r hrpi
      simpa only [Complex.ofReal_add] using Work.RPV.chordPS_phase_rev h0
    · rw [lagPt, if_neg (not_le.mpr hxpos), basePt, if_neg (not_le.mpr hnx1), ← hrsq, hch]
      simp only [Work.RPB.chordSurf]
      rw [← Work.RPV.chordPS_swap]

end Work.RPB.B5

import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.SurgeryInvariance.API

namespace Work.Smooth.Morse.MorseModel

/-- **The winding span is locally constant at `t₀` as soon as the two regions immediately below
and above `t₀` have the same winding span.**

The sublevel regions `region ψ g s = F ∩ {g < s}` are monotone in the level (`region_mono`), and
so is the winding span (`WindingSpan_mono`).  Hence if `WindingSpan` takes the same value at
`t₀ - ε` and at `t₀ + ε`, the span is squeezed on the whole window `[t₀ - ε, t₀ + ε]`: for
`t₀ - ε ≤ u ≤ t₀ + ε`,
`span (t₀ - ε) ≤ span u ≤ span (t₀ + ε) = span (t₀ - ε)`.
In particular the span at `t₀` itself equals that common value, so the span is constant on the
open window of radius `ε` around `t₀`. -/
theorem windingSpan_locally_const_of_span_eq (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} {t₀ : ℝ} (h : ∃ ε : ℝ, 0 < ε ∧ Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ) (Work.Smooth.Morse.region ψ g (t₀ - ε)) = Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ) (Work.Smooth.Morse.region ψ g (t₀ + ε))) : ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t₀| < ε → Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ) (Work.Smooth.Morse.region ψ g s) = Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ) (Work.Smooth.Morse.region ψ g t₀) := by
  obtain ⟨ε, hε, hspan⟩ := h
  refine ⟨ε, hε, fun s hs => ?_⟩
  -- every level in the closed window has the winding span of the lower end of the window
  have hkey : ∀ u : ℝ, t₀ - ε ≤ u → u ≤ t₀ + ε →
      Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.Smooth.Morse.region ψ g u) =
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.Smooth.Morse.region ψ g (t₀ - ε)) := by
    intro u hu₁ hu₂
    refine le_antisymm ?_ ?_
    · calc Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
              (Work.Smooth.Morse.region ψ g u)
          ≤ Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
              (Work.Smooth.Morse.region ψ g (t₀ + ε)) :=
            Work.SurgeryInvariance.WindingSpan_mono _
              (Work.Smooth.Morse.region_mono ψ g hu₂)
        _ = Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
              (Work.Smooth.Morse.region ψ g (t₀ - ε)) := hspan.symm
    · exact Work.SurgeryInvariance.WindingSpan_mono _
        (Work.Smooth.Morse.region_mono ψ g hu₁)
  have hs₁ : t₀ - ε ≤ s := by
    have := (abs_lt.mp hs).1
    linarith
  have hs₂ : s ≤ t₀ + ε := by
    have := (abs_lt.mp hs).2
    linarith
  rw [hkey s hs₁ hs₂, hkey t₀ (by linarith) (by linarith)]

end Work.Smooth.Morse.MorseModel

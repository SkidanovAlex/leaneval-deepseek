import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.Smooth.Morse.MorseModel
import Submission.Work.Smooth.Morse.Span
import Submission.Work.SurgeryInvariance.API

/-!
# The winding span is locally constant at a critical value with a disc model

If the passage through the critical value `t₀` of `g|_F` adds the interior of an embedded disc of
the surface (`Work.Smooth.Morse.DiscModel ψ g t₀`), then the winding span of the sublevel region
`F ∩ {g < s}` does not change as `s` crosses `t₀`: the span of the region is *locally constant* at
`t₀`.

The proof does not need the actual disc: it only uses that the two regions immediately below and
immediately above `t₀` have the same winding span (`DiscModel.windingSpan_eq`), together with
monotonicity of the region and of the winding span (`region_mono`, `WindingSpan_mono`).  Indeed
for `|s - t₀| < ε` the region `F ∩ {g < s}` is squeezed between `F ∩ {g < t₀ - ε}` and
`F ∩ {g < t₀ + ε}`, and the two extreme regions have equal winding span; the span of the region
at `t₀` itself is squeezed the same way.  Hence all three spans coincide.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.Morse.MorseModel

/-- **Local constancy of the winding span at a critical value with a disc model.** -/
theorem windingSpan_locally_const (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hg : Continuous g) {t₀ : ℝ} (h : Work.Smooth.Morse.DiscModel ψ g t₀) : ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, |s - t₀| < ε → Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ) (Work.Smooth.Morse.region ψ g s) = Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ) (Work.Smooth.Morse.region ψ g t₀) := by
  obtain ⟨ε₁, hε₁, hspan⟩ :=
    Work.Smooth.Morse.DiscModel.windingSpan_eq ψ hg h
  refine ⟨ε₁ / 2, half_pos hε₁, fun s hs => ?_⟩
  have hεpos : (0 : ℝ) < ε₁ / 2 := half_pos hε₁
  have hεlt : ε₁ / 2 < ε₁ := half_lt_self hε₁
  have hend : Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.Smooth.Morse.region ψ g (t₀ - ε₁ / 2)) =
      Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (Work.Smooth.Morse.region ψ g (t₀ + ε₁ / 2)) :=
    hspan (ε₁ / 2) hεpos hεlt
  -- any level within the window has the winding span of the lower end of the window
  have hkey : ∀ u : ℝ, t₀ - ε₁ / 2 ≤ u → u ≤ t₀ + ε₁ / 2 →
      Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.Smooth.Morse.region ψ g u) =
        Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (Work.Smooth.Morse.region ψ g (t₀ - ε₁ / 2)) := by
    intro u hu₁ hu₂
    refine le_antisymm ?_ ?_
    · calc Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
              (Work.Smooth.Morse.region ψ g u)
          ≤ Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
              (Work.Smooth.Morse.region ψ g (t₀ + ε₁ / 2)) :=
            Work.SurgeryInvariance.WindingSpan_mono _
              (Work.Smooth.Morse.region_mono ψ g hu₂)
        _ = Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
              (Work.Smooth.Morse.region ψ g (t₀ - ε₁ / 2)) := hend.symm
    · exact Work.SurgeryInvariance.WindingSpan_mono _
        (Work.Smooth.Morse.region_mono ψ g hu₁)
  have hs₁ : t₀ - ε₁ / 2 ≤ s := by
    have := (abs_lt.mp hs).1
    linarith
  have hs₂ : s ≤ t₀ + ε₁ / 2 := by
    have := (abs_lt.mp hs).2
    linarith
  rw [hkey s hs₁ hs₂,
    hkey t₀ (by linarith) (by linarith)]

end Work.Smooth.Morse.MorseModel

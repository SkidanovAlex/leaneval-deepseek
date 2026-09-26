import Mathlib
import Submission.Work.BoxShrink.Bubble.Smooth.GaugeFlow

namespace Work.BoxShrink.Bubble.Smooth

/-- **The curve-level Sard input gives the push-off.**

The hypothesis is the "last mile" of the smooth argument in the form in which it is
curve-local: every closed curve `γ` of the surface lying in the region inside the box admits a
`C²` function `hh` whose sublevel region `{hh < a}` (`a < 0`) lies in `upperRegion ∪ lowerRegion`,
which is bounded below by `b > 0` along `γ` (`hh (γ t) < b`), and whose interval `[a,b]` is
critical-value-free.

Given such data, `Work.Smooth.Morse.Flow.exists_homotopic_curve_in_region` — the normalised
gradient flow of `hh|_F` — homotopes `γ` to a curve of `F ∩ {hh < a} ⊆ upperRegion ∪ lowerRegion`,
and the winding vector is unchanged by homotopy
(`Work.SurgeryInvariance.WindingOf.homotopic_eq`).  Since `hh` is produced for each `γ`
individually, this transports every realised winding vector of the box region off the slicing
plane, i.e. it proves `SlicePushOff`. -/
theorem curveSard {ψ : Submission.Diffeo} {s : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (h : ∀ γ : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
      (∀ t : ℝ, γ t ∈ Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ) →
      ∃ (hh : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ) (a b : ℝ),
        ContDiff ℝ 2 hh ∧ a < 0 ∧ 0 < b ∧
          (∀ x : LeanEval.KnotTheory.PardonDistortion.R3,
            x ∈ (Work.Smooth.Morse.torus ψ).carrier → hh x < a →
              x ∈ Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
                Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u) ∧
          (∀ t : ℝ, hh (γ t) < b) ∧
          (∀ t ∈ Set.Icc a b, Work.Smooth.Morse.IsRegularValue ψ hh t)) :
    SlicePushOff (Work.Smooth.Morse.torus ψ) s c σ u := by
  refine (Toolkit.subset_realizedWindings_iff
    (P := Work.Smooth.Morse.torus ψ)
    (A := Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ)
    (B := Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
      Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u)).mpr ?_
  intro γ hγ
  obtain ⟨hh, a, b, hcont, ha, hb, hlow, hγb, hreg⟩ := h γ hγ
  have hab : a ≤ b := le_of_lt (lt_trans ha hb)
  have hγmem : ∀ t : ℝ, γ t ∈ Work.Smooth.Morse.region ψ hh b :=
    fun t => ⟨(hγ t).1, hγb t⟩
  obtain ⟨γ', hγ', hhom⟩ :=
    Work.Smooth.Morse.Flow.exists_homotopic_curve_in_region ψ hcont hab hreg γ hγmem
  exact ⟨γ', fun t => hlow (γ' t) (hγ' t).1 (hγ' t).2,
    (Work.SurgeryInvariance.WindingOf.homotopic_eq hhom).symm⟩

end Work.BoxShrink.Bubble.Smooth

import Mathlib
import Submission.Work.Drive.chordSweepSmooth
import Submission.Work.Drive.chordSweepDefs
import Submission.Work.Drive.sweepLoop_injective
import Submission.Work.Drive.sweepFam_slices_knots

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant


/-- **The (a.e.) derivative of the chamfered sweep loop in its loop parameter.**
The four branches are the derivatives of the four branches of `sweepLoopChamfer` w.r.t. the loop
parameter `t`; the (measure-zero) breakpoints are assigned the preceding branch, which is
irrelevant for the `intervalIntegral` identities.  Combined with the fundamental theorem of
calculus along the loop this is the workhorse for turning differences
`sweepFam … (t+h) - sweepFam … t` into box integrals of these directions. -/
noncomputable def sweepLoopChamferDeriv (r : ℝ → Space) {d : BandArcData} (D : SweepData d)
    (lam s : ℝ) : ℝ → Space :=
  fun t =>
    let u := sweepParam t
    (1 / period) •
      (if u ≤ 1 / 2 then
        (2 * (1 - 2 * lam)) •
          ((sweepW' D s) •
            deriv r (taR D s + (lam + (1 - 2 * lam) * (2 * u)) * sweepW' D s))
      else if u ≤ 1 / 2 + lam / 2 then
        (2 / lam) • (sweepChord' r D s (1 - lam) - sweepArc' r D s (1 - lam))
      else if u ≤ 1 - lam / 2 then
        (-(1 - 2 * lam) / (1 / 2 - lam)) • (r (tbR D s) - r (taR D s))
      else
        (2 / lam) • (sweepArc' r D s lam - sweepChord' r D s lam))

/-- For a smooth knot `r` with an `O`-avoiding non-separating band arc `(d, D)`, on any compact
sweep-parameter window `[ε, σ₀] ⊂ (0,1)` and for all sufficiently small rounding/smoothing
parameters `lam, δ₁, δ₂`, every slice of the smoothed chamfered sweep is a knot: injective on one
period, with nonvanishing velocity.  (`sweepFam` is the doubly smoothed chamfered sweep of
`Submission/Work/Drive/chordSweepSmooth.lean`; `sweepLoopChamfer` chamfers the two corners of the
raw sweep loop `sweepArc ∪ sweepChord` at the parameter fraction `lam`.) -/
theorem sweepWindowKnots {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    {d : LeanEval.KnotTheory.Quadrisecant.BandArcData} (D : Work.Drive.SweepData d)
    (havoid : ∀ s : Set.Icc (0 : ℝ) 1, ∀ (hs0 : (s : ℝ) ≠ 0) (hs1 : (s : ℝ) ≠ 1),
      LeanEval.KnotTheory.Quadrisecant.mobiusCover
        ⟨(d.a s, d.b s), d.offdiag s hs0 hs1⟩ ∉
        LeanEval.KnotTheory.Quadrisecant.trisecantSet r)
    {ε σ₀ : ℝ} (hε : 0 < ε) (hεσ : ε < σ₀) (hσ : σ₀ < 1) :
    ∃ L : ℝ, 0 < L ∧
      ∀ (lam δ₁ δ₂ : ℝ), 0 < lam → lam ≤ L → 0 < δ₁ → δ₁ ≤ L → 0 < δ₂ → δ₂ ≤ L →
        ∀ σ : ℝ, ε ≤ σ → σ ≤ σ₀ →
          Set.InjOn (fun t : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ σ t)
            (Set.Ico 0 LeanEval.KnotTheory.Quadrisecant.period) ∧
          (∀ t : ℝ, LeanEval.KnotTheory.Quadrisecant.velocity
            (fun t : ℝ => Work.Drive.sweepFam r D lam δ₁ δ₂ σ t) t ≠ 0) := by sorry

end Work.Drive

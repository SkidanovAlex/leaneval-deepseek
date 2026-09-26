import Mathlib
import Submission.Work.Drive.Mono.OneEventNDDefs
import Submission.Work.Drive.Final.sweep_mono
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Mono.Band.BandChartDefs

/-!
# One event per level along the tilted sweep, from the non-degenerate bad set

`Work.Drive.Mono.OneEvBad ψ s c σ v a₀ b₀ u h τ` is the bad set of the route-I formulation of "one
event per level": two *distinct* (in the parameter plane) non-degenerate events of the swept level
`ℓ_τ = ⟪dirOf τ a₀ b₀, ·⟫` lie on the same level, and not both of them are critical points of the
sweep height.

Here we prove the *consumer* direction, which is what the `GoodSweepData3` field "one event per level
for `IsAnyEvent`" asks for: under the non-degeneracy of every event (`hND`) and the non-membership of
the bad set (`hgood`), any two events of the sweep that share the level `ℓ_τ` coincide in the
parameter plane.  The only other ingredient is clause (iv) of `Work.Drive.Final.TiltedGenericity`
(two critical points of the sweep height with the same value coincide), which rules out the excluded
case "both events are critical points": in that case the two points *would* coincide, contradicting
the distinctness that `OneEvBad` records.
-/

namespace Work.Drive.Mono

/-- **The good data give one event per level.**  Non-degeneracy of every event of the tilted sweep
(`hND`), together with the genericity of the sweep height (`hTG`, needed only for its clause (iv):
one critical point per level), forbids the bad set `OneEvBad`; hence two events at the same level
`ℓ_τ` are the same point of the parameter plane.

Indeed, if two events `p ≠ p'` (in the parameter plane) lay on the same level and *not* both were
critical points, they would exhibit `OneEvBad`; while if *both* were critical points, clause (iv) of
`TiltedGenericity` would force `par ψ p = par ψ p'` — and `ψ` being a diffeomorphism of the plane,
that is `p = p'`. -/
theorem oneEventPerLevel_of_nd {ψ : Submission.Diffeo} {s u h : ℝ}
    {c v : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3} {τ : ℝ}
    (hℓ : ℓ = (innerSL ℝ) (Work.Drive.Mono.Band.dirOf τ a₀ b₀))
    (hTG : Work.Drive.Final.TiltedGenericity ψ s c σ u v h ℓ exc)
    (hND : ∀ p : ℝ × ℝ,
      Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p →
      Work.Drive.Mono.NDEvent ψ s c σ u v h ℓ p)
    (hgood : ¬ Work.Drive.Mono.OneEvBad ψ s c σ v a₀ b₀ u h τ) :
    ∀ p p' : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p →
      Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ p' →
      ℓ (Work.BoxShrink.Pinch.par ψ p) = ℓ (Work.BoxShrink.Pinch.par ψ p') →
      Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p' := by
  subst hℓ
  intro p p' hp hp' hval
  by_contra hne
  refine hgood ⟨p, p', hND p hp, hND p' hp', ?_, hne, ?_⟩
  · -- the two events lie on the same level of `ℓ_τ`
    exact hval
  · -- they are not both critical points: clause (iv) of the genericity would make them coincide
    rintro ⟨he, he'⟩
    exact hne (hTG.2.2.2 p p' he.1 he'.1 he.2.1 he'.2.1 he.2.2 he'.2.2 hval)

end Work.Drive.Mono

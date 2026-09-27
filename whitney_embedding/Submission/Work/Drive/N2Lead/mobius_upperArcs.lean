import Mathlib
import Submission.Work.Drive.N2Lead.mobiusGeomDefs
import Submission.Work.Drive.N2Lead.twistDefs
import Submission.Work.Drive.N2Lead.mobiusArcDefs
import Submission.Work.Drive.N2Lead.upperArcToolkit
import Submission.Work.Drive.N2Lead.upperArcsYSigns
import Submission.Work.Drive.N2Lead.upperArcXDerivPosAlt

/-!
# The two untwisted model arcs of the upper level (`D2d.4` of the Möbius saddle note)

The statement `Work.Drive.N2Lead.mobius_upperArcs`, with the calculus it rests on in
`Submission/Work/Drive/N2Lead/upperArcToolkit.lean`.
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology in
/-- **The two untwisted model arcs of the upper level** (§4 `D2d.4` of
`N2Lead/NOTES_LEAD_mobiusSaddle.md`, first item).  With `ρ w = √(σ (s, w) + i w)`
(`mobiusRho η δ s w`) and the untwisted arcs
`α w = twistX ε (-1) (twistY a' (-1) (cE3 (-ρ w)))`, `β w = twistX ε (-1) (twistY a' (-1) (cE3 (ρ w)))`
(`mobiusAlpha`, `mobiusBeta` in `mobiusGeomDefs.lean`), the signs and the `x`-monotonicity after the
two slab twists are:

* `α` lies in the half-space `{y > 0}` and `β` in `{y < 0}` on `[-2,2]`;
* the `x`-coordinate of both arcs is strictly increasing on `[-2,2]` (pointwise positive derivative).

Route (the note's sign analysis): after `twistY a' (-1)`, a point `(x₀, y₀, z₀)` becomes
`(x, y₀, z)` with `x = x₀ cos θ(y₀)`, `z = -x₀ sin θ(y₀)`, `θ = π · smoothTransition ((a' - y₀)/(2a'))`,
and `sign (cos θ y₀) = sign y₀`, `θ 0 = π/2` (from `ST t + ST (1 - t) = 1` and strict monotonicity of
`ST`); then `twistX ε (-1)` turns `(x, y₀, z)` into `(x, y₀ cos φ - z sin φ, -y₀ sin φ - z cos φ)` with
`φ = π · smoothTransition ((x + ε)/(2ε))`, and `hεa : ε ≤ √(a'² + s)` forces `|x| < ε ⇒ |y₀| < a'`.
The `x`-monotonicity uses the `Re √` estimate `Work.Drive.N2Lead.modelArc_re_strictMono` (`σ' · a + b`
against the twist term) and the `Im √` estimate `Work.Drive.N2Lead.modelArc_im_strictMonoOn`
(`σ' ≤ 0`); both are *in flight/on disk* in this directory (`modelArc_re_strictMono.lean`,
`modelArc_im_strictMonoOn.lean`) - import them once available, otherwise prove the instance inline.
Careful with the pointwise derivative at `w = 0`: `(Re √(σ + i w))'` vanishes there by evenness, so
the positivity at `w = 0` comes from the twist terms (whose `w`-derivatives do not vanish), not from
the monotonicity of `Re √`; a `StrictMonoOn`-only form of the `Re √` estimate is not enough for the
interior points, the pointwise positivity on `(0,2]` plus the separate `w = 0` argument is.
Endpoint values: `α 0 = (0, √s, 0)`, `β 0 = (0, -√s, 0)`.  The result goes in namespace
`Work.Drive.N2Lead`. -/
theorem mobius_upperArcs {η δ s a' ε C₀ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 10) (hs : 0 < s) (hsη : s ≤ η)
    (hC₀ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C₀) (hsmall : 4 * C₀ * η ≤ δ)
    (ha' : 0 < a') (hε : 0 < ε) (hεa : ε ≤ Real.sqrt (a' ^ 2 + s)) :
    (∀ w ∈ Set.Icc (-2) 2,
      0 < (Work.Drive.N2Lead.mobiusAlpha η δ s a' ε w) 1 ∧
      (Work.Drive.N2Lead.mobiusBeta η δ s a' ε w) 1 < 0) ∧
    (∀ w ∈ Set.Icc (-2) 2,
      0 < deriv (fun w : ℝ => (Work.Drive.N2Lead.mobiusAlpha η δ s a' ε w) 0) w ∧
      0 < deriv (fun w : ℝ => (Work.Drive.N2Lead.mobiusBeta η δ s a' ε w) 0) w) := by
  have hδ₂ : δ < 1 / 2 := by linarith
  refine ⟨?_, ?_⟩
  · exact upperArcsYSigns hδ hδ₂ hη hs ha' hε
  · intro w hw
    refine ⟨?_, ?_⟩
    · rw [show (fun w : ℝ => (Work.Drive.N2Lead.mobiusAlpha η δ s a' ε w) 0)
          = fun w : ℝ => uaX η δ s a' w from
        funext (fun w => mobiusAlpha_zero η δ s a' ε w ha')]
      exact upperArcXDerivPosAlt hδ hδ' hη hη' hs hsη hC₀ hsmall ha' w hw
    · rw [show (fun w : ℝ => (Work.Drive.N2Lead.mobiusBeta η δ s a' ε w) 0)
          = fun w : ℝ => uaX η δ s a' w from
        funext (fun w => mobiusBeta_zero η δ s a' ε w)]
      exact upperArcXDerivPosAlt hδ hδ' hη hη' hs hsη hC₀ hsmall ha' w hw

end Work.Drive.N2Lead

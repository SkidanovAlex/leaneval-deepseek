import Mathlib
import Submission.Work.Drive.exists_embedded_configuration_strip

/-!
# The offset parametrisation of the configuration strip

`Work.Drive.exists_embedded_configuration_strip` presents the configuration Möbius strip `M` of a
smooth plane curve `γ` as the image of a map `μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ` which
is symmetric and injective on unordered pairs.  The present file fixes the **offset parametrisation**
of the same strip: the point

> `Work.Drive.stripOffsetPt μ x s = μ (x, x * Circle.exp (2 * π * s))`

is the chord from `γ x` to `γ (x * e^{2πi s})`, i.e. the chord whose second endpoint is obtained from
the first by the rotation of the circle by `s` turns.  For `s ∈ (0, 1/2)` these are the "short" chords
and every chord of the strip has exactly one such presentation, with the single exception of the
*diameters* `s = 1/2`, whose two presentations are `(x, 1/2)` and `(-x, 1/2)`.

This is the layer at which the strip is seen as a **Möbius band**: the parametrisation
`(x, s) ∈ Circle × [0, 1/2]` of the closed strip quotients by the antipodal identification on the
boundary circle `s = 1/2`, while the circle `s = 0` is the diagonal `∂M` (the curve `γ` itself, where
the cap disk of the capping is glued).  In the chain route to `Work.Drive.ParityCore γ`
(`CHAIN_ROUTE_REDUCTION.md` §3–§4) this is the coordinate on which the *disk model of `ℝP²`* used by
the intersection-form chapter (`Submission/Work/Drive/Surf/`) is built: the capped plane
`P_u = u·M ∪ cap_u` is a disk with its boundary circle identified antipodally, the boundary circle
being the *core* of the Möbius band, i.e. the loop `s = 1/2` (`Work.Drive.core_loop` with `w = -1`).

The properties of the parametrisation (injectivity away from the two presentations of a diameter,
surjectivity onto the strip) are the content of the delegated lemma
`Work.Drive.stripOffset_param`.
-/

namespace Work.Drive

noncomputable section

/-- **The offset parametrisation of the configuration strip.**  The configuration point of the chord
joining `γ x` to `γ (x * e^{2πi s})`: the second endpoint of the chord is the first, rotated by `s`
turns of the circle. -/
def stripOffsetPt (μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ) (x : Circle) (s : ℝ) :
    (ℝ × ℝ) × UnitAddCircle × ℝ :=
  μ (x, x * Circle.exp (2 * Real.pi * s))

@[simp] lemma stripOffsetPt_zero (μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ)
    (x : Circle) : stripOffsetPt μ x 0 = μ (x, x) := by
  simp [stripOffsetPt]

end

end Work.Drive

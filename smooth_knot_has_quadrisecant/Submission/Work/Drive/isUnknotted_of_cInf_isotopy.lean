import Mathlib
import Submission.Work.Drive.cInfKnot
import Submission.Work.Drive.isUnknotted_of_cInf_knotPath
import Submission.Work.Drive.exists_analytic_close_twoVar

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-!
# The analytic-smoothing kit: a `C¹` family of `C^∞` knots from `r` to the round circle makes `r`
unknotted

`IsUnknotted r` demands a **jointly analytic** isotopy `R : ℝ → ℝ → Space` with `R · 0 = r`,
`R · 1 = standardCircle` and analytic knot slices.  In this Mathlib `ContDiff ℝ ⊤` is analyticity, so
a construction that produces its isotopy by smooth operations (mollification, convolution, patchwork,
an explicit `C^∞` formula) does not qualify as it stands.

This module records that the *only* obstruction is two purely analytic smoothing lemmas, and that
they are available:

* `Work.Drive.isUnknotted_of_cInf_knotPath` (proved): the assembly — if the jointly-`C¹` family `F`
  of `C^∞` knots can be `C¹`-approximated, uniformly on the slab, by a jointly *analytic* family `G`,
  then `IsUnknotted r`;
* `Work.Drive.exists_analytic_close_twoVar` (proved): that approximation exists for every `ε > 0`
  (trigonometric approximation in `t` — `Work.Drive.exists_analytic_periodic_close` — blended in `s`
  by Bernstein approximation);
* `Work.Drive.uniformCorrection_clauses`, `Work.Drive.smallCorrection_clauses_cInf`,
  `Work.Drive.isUnknotted_of_path_to_unknotted` and `Work.Drive.isUnknotted_of_close`: the
  perturbation and propagation lemmas consumed by the assembly.

Note the honest scope: the *slices* must be smooth (the `s = 0` slice of an analytic isotopy is
analytic, so `IsUnknotted r` cannot hold for a merely `C¹` curve `r` at all); what is dropped is the
regularity of the *parameter* dependence.  Nothing here removes the topological content of an
unknotting — producing such a family in the first place is the Dehn/Schoenflies step.
-/

namespace Work.Drive

/-- **The smoothing kit.**  A `C¹`-in-parameter family of `C^∞` knots from `r` to the round circle
is enough for `IsUnknotted r`: the parameter regularity is smoothed by
`Work.Drive.exists_analytic_close_twoVar` and the loss of the knot property under the correction is
excluded by the (uniform) small-correction lemmas. -/
theorem isUnknotted_of_cInf_isotopy {r : ℝ → Space} (hr : IsSmoothKnot r)
    {F : ℝ → ℝ → Space} (hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => F p.1 p.2))
    (hper : ∀ s t : ℝ, F (t + period) s = F t s)
    (h0 : ∀ t : ℝ, F t 0 = r t) (h1 : ∀ t : ℝ, F t 1 = standardCircle t)
    (hslice : ∀ s ∈ Set.Icc (0 : ℝ) 1, IsCInfKnot (fun t : ℝ => F t s)) :
    IsUnknotted r :=
  isUnknotted_of_cInf_knotPath hr hF h0 h1 hslice
    (fun ε hε => exists_analytic_close_twoVar hF hper hε)

end Work.Drive

import Mathlib
import Submission.Work.Drive.projCharted
import Submission.Work.Drive.exists_localModel_projCharted
import Submission.Work.Drive.isCoveringMap_projOfUnitSphere
import Submission.Work.Drive.exists_nonvanishing_lift_of_data

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

-- Proof notes: the three ingredients are
--  * `Work.Drive.exists_localModel_projCharted` (`Submission/Work/Drive/exists_localModel_projCharted.lean`):
--    every point of the box has a neighbourhood on which `h` agrees with a `C^inf` map;
--  * `Work.Drive.isCoveringMap_projOfUnitSphere`
--    (`Submission/Work/Drive/isCoveringMap_projOfUnitSphere.lean`): the unit sphere is a covering
--    space of `RP^3`, so (the box being convex, hence contractible and simply connected) `h` has a
--    continuous nonvanishing lift on the box;
--  * `Work.Drive.exists_nonvanishing_lift_of_data`
--    (`Submission/Work/Drive/exists_nonvanishing_lift_of_data.lean`): the combination of the two,
--    producing the globally smooth nowhere vanishing lift by extending the box lift off the box
--    (`Work.Drive.exists_contDiff_extension_box`) and pulling it back along a flattening of the
--    plane into a box-neighbourhood on which the extension does not vanish
--    (`Work.Drive.exists_contDiff_flattening`).

/-- **A nonvanishing global lift of a smooth-on-a-box map into `RP^3`.**

If `h : R^2 -> RP^3` is `C^inf` (Whitney) on the closed box `[a,b] x [c,d]` (`a < b`, `c < d`),
then there is a globally `C^inf`, nowhere vanishing `V : R^2 -> R^4` whose projective class agrees
with `h` on the box.

Consequence (for the requester): `x ↦ [V x]` is a globally `C^inf` extension of `h`, by
`Work.Drive.contMDiffAt_projMk`.

Suggested route (not binding).  The box is convex, hence contractible, so the pulled-back
tautological line bundle is trivial and a smooth nonvanishing lift `v` of `h` exists *on the box*:
on each point of the box use the canonical lift provided by one of the four projective charts
`projChart i`, and glue along a cover whose nerve is a *path* (e.g. horizontal strips, which cover
the box and have connected consecutive overlaps only), matching the constant sign on the connected
overlaps.  For the *global* nonvanishing extension, first extend `v` off the box as a plain
vector-valued `C^inf` map, and then pull it back along a smooth "flattening" `Ψ : R^2 → (a-ε,b+ε) x
(c-ε,d+ε)` with `Ψ = id` on the box and `ε` small enough that the image of `Ψ` lies in the open set
where the extension does not vanish. -/
theorem exists_nonvanishing_lift_projCharted (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    {h : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (EuclideanSpace ℝ (Fin 4))}
    (hh : letI := Work.Drive.projCharted 3
      ContMDiffOn (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) h
        {q : EuclideanSpace ℝ (Fin 2) | q 0 ∈ Set.Icc a b ∧ q 1 ∈ Set.Icc c d}) :
    ∃ (V : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 4)) (hV : ∀ x, V x ≠ 0),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧
      ∀ x : EuclideanSpace ℝ (Fin 2), x 0 ∈ Set.Icc a b → x 1 ∈ Set.Icc c d →
        Projectivization.mk ℝ (V x) (hV x) = h x := by
  have hloc := exists_localModel_projCharted a b c d hab hcd hh
  exact exists_nonvanishing_lift_of_data a b c d hab hcd hh hloc
    isCoveringMap_projOfUnitSphere

end Work.Drive

import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.Helpers
import Submission.Work.Milnor.MkCharted
import Submission.Work.Milnor.Homeo7
import Submission.Work.Milnor.NoCapping
import Submission.Work.Milnor.FinalWiring

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Manifold ContDiff
open Metric (sphere)

noncomputable section

namespace Submission

/-- **Milnor's exotic 7-sphere.**

There exists a smooth `7`-manifold `M` which is homeomorphic to `S⁷` but admits no diffeomorphism
to `S⁷` (for the standard smooth structure on `S⁷`).

The manifold is Milnor's `M_k`, realised in this workspace as `Submission.Milnor.Mk k`, the
quotient of two copies of `ℝ⁴ × S³` glued along `{x ≠ 0}` by the clutching map
`φ(x, y) = (x/‖x‖², u^{-k} y u⁻¹)`, `u = x/‖x‖` (see `Submission.Work.Milnor.Clutch`); here
`k = -2`, the value for which the Euler number of the underlying `S³`-bundle over `S⁴` is `1`.

The manifold and its smooth structure are provided explicitly by
`Submission.Work.Milnor.mkChartedSpace (-2)` / `mk_isManifold (-2)` (an explicit re-charting over
`ℝ⁷` of the product construction), and the homeomorphism to `S⁷` is

* `Submission.Work.Milnor.mk_minus_two_homeo` — proved from Milnor's explicit Morse function
  (`Work.Milnor.morseFun`, with exactly two nondegenerate critical points, indices `0` and `7`)
  and Reeb's theorem (`Work.Morse.reeb`); see `Submission.Work.Milnor.Homeo7`.

The exoticness `IsEmpty (M ≃ₘ⟮𝓡 7, 𝓡 7⟯ S⁷)` is reduced here to the single statement
`Work.Milnor.no_cappingDiffeo` (file `Submission/Work/Milnor/NoCapping.lean`): there is no smooth
identification of `Mk (-2)` with `S⁷`.  The reduction is pure bookkeeping
(`Work.Milnor.cappingDiffeo_of_diffeo` turns a `ℝ⁷`-diffeomorphism into a *capping*
diffeomorphism, for which the disc bundle can be capped by a disc); the mathematical content of
`no_cappingDiffeo` is the endgame of `Submission/NOTES.md` §§14.7-14.10: a capping diffeomorphism
produces the closed oriented `8`-manifold `X = D(ξ) ∪ D⁸`, whose middle self-intersection is `±1`
(`Work.Cohomology.capped_cupSquare_generates`, Poincaré duality in the middle degree), while
Hirzebruch in dimension `8` together with `p₁(X) = ±6·x` makes that impossible (the arithmetic is
`Work.Milnor.endgame_congruence_route'` / `Work.Milnor.six_sq_not_dvd`).
-/
theorem milnor_exotic_sphere_seven :
    ∃ (M : Type) (_ : TopologicalSpace M)
      (_ : ChartedSpace (EuclideanSpace ℝ (Fin 7)) M)
      (_ : IsManifold (𝓡 7) ∞ M)
      (_homeo : M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin 8)) 1),
      IsEmpty (M ≃ₘ⟮𝓡 7, 𝓡 7⟯ sphere (0 : EuclideanSpace ℝ (Fin 8)) 1) := by
  refine ⟨Milnor.Mk (-2), inferInstance, Work.Milnor.mkChartedSpace (-2), Work.Milnor.mk_isManifold (-2),
    Work.Milnor.mk_minus_two_homeo.some, ?_⟩
  -- the exoticness.  A diffeomorphism `φ : Mk (-2) ≃ₘ S⁷` would be a *capping diffeomorphism*
  -- (`Work.Milnor.cappingDiffeo_of_diffeo`), and no capping diffeomorphism exists
  -- (`Work.Milnor.no_cappingDiffeo`, the endgame of `Submission/NOTES.md` §14.7–§14.10: the
  -- middle self-intersection of the closed `8`-manifold `X = D(ξ) ∪_φ D⁸` is `±1`, while
  -- Hirzebruch in dimension `8` together with `p₁(X) = ±6 x` forbids that).
  refine ⟨fun φ => Work.Milnor.no_cappingDiffeo_proved ⇑φ (Work.Milnor.cappingDiffeo_of_diffeo φ)⟩

end Submission

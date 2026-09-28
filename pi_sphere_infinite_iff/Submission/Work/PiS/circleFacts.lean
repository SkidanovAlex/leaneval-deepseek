import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.Serre.C1SphOne
import Submission.Work.Serre.sphOneAspherical

set_option synthInstance.maxHeartbeats 400000

/-!
# Area CIRCLE: `π₁(S¹)` infinite, `π_k(S¹) = 1` for `k ≥ 2`

`S¹` is `Work.PiS.Sph 1 = Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1` with base point
`pt 1 = EuclideanSpace.single 0 1`.

Both halves are already available in the seed (proved axiom-clean):

* `π₁(S¹,x) ≅ ℤ` for *every* `x : S¹` — `Work.Serre.pi1SphOne_addEquiv_int`
  (covering `ℝ → Circle ≃ₜ S¹`, deck group `2πℤ ≅ ℤ`);
* `S¹` is aspherical — `Work.Serre.sphOneAspherical` (the same covering, plus `π_*(ℝ) = 0` and
  discreteness of the fibre, through the long exact homotopy sequence of a Serre fibration).

Since `Work.Serre.Sph` and `Work.PiS.Sph` are both `abbrev`s for the literal sphere, these
statements apply with no transport at all; only the passage from an additive equivalence with `ℤ`
to `Infinite` is needed for the first half.
-/

set_option autoImplicit false

namespace Work.PiS

theorem circleFacts : Work.PiS.CircleFacts := by
  refine ⟨?_, fun k hk => Work.Serre.sphOneAspherical k hk (pt 1)⟩
  obtain ⟨e⟩ := Work.Serre.pi1SphOne_addEquiv_int (pt 1)
  exact e.toEquiv.infinite_iff.mpr (inferInstance : Infinite ℤ)

end Work.PiS

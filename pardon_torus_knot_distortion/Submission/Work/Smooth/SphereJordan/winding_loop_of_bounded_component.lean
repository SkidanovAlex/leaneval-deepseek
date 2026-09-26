import Submission.Work.Smooth.SphereJordan.loopSharedLemmas
import Submission.Work.Smooth.SphereJordan.existsWindingLoop

namespace Work.Smooth.SphereJordan

open Set

noncomputable section

/-- If `F ⊆ ℂ` is closed, contains `0`, and the connected component of `0`
in `F` is bounded, then there is a closed loop avoiding `F` (hence avoiding `0`) whose index about
`0` is non-zero. -/
theorem winding_loop_of_bounded_component {F : Set ℂ} (hF : IsClosed F) (h0 : (0 : ℂ) ∈ F)
    (hbdd : Bornology.IsBounded (connectedComponentIn F (0 : ℂ))) :
    ∃ c : C(unitInterval, ℂ), (∀ t, c t ∉ F) ∧ (∀ t, c t ≠ 0) ∧ c 0 = c 1
      ∧ Work.Smooth.SphereJordan.loopIndex c ≠ 0 :=
  existsWindingLoop hF h0 hbdd

end

end Work.Smooth.SphereJordan

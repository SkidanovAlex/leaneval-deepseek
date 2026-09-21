import Mathlib
import Submission.Work.OddRadon.RadialDefs

/-!
# The Euclidean ball satisfies the two-power radial system (`Work.OddRadon`)

The ball (`d = 2n+1`) is the body of revolution with both radial functions equal to `1`; its
semicircular profile corresponds to the data `Φ α = 2 cos²α`, `Ψ = 0`.  Both equations of
`RadialSystem n ballPhi ballPsi ballR ballr` reduce to `1`-power identities:

* `(1^{2n+2} + 1^{2n+2}) cos²α = 2 cos²α = ballPhi α`,
* `(1^{2n+1} - 1^{2n+1}) cos α = 0 = ballPsi α`.
-/

namespace Work.OddRadon

theorem radialSystem_ball (n : ℕ) : RadialSystem n ballPhi ballPsi ballR ballr := by
  intro α _hα
  refine ⟨?_, ?_⟩
  · simp only [ballR, ballr, ballPhi, one_pow]
    ring
  · simp only [ballR, ballr, ballPsi, one_pow]
    ring

end Work.OddRadon

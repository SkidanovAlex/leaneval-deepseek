import Mathlib
import Submission.Work.Pi6.MSS.SerreCF
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The cochain complex of the Serre filtration is the singular cochain complex of `E`

`Work.Pi6.MSS.serreCF 𝕜 E B p` is built on `Work.Cohomology.SSetCochainComplex 𝕜 (sSing E)`, while
`Work.Pi6.Coh 𝕜 E n` is the cohomology of `Work.Cohomology.singularCochainComplex 𝕜 (TopCat.of E)`.
The two complexes have the same terms and the same differentials (both are the transpose of the
singular boundary), so their homologies agree.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

namespace Work.Pi6.MSS

noncomputable section

/-- The cohomology of the complex underlying the Serre filtration is the singular cohomology of
`E`. -/
theorem serreCF_homology (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (n : ℕ) :
    (serreCF 𝕜 E B p).C.homology n = Work.Pi6.Coh 𝕜 E n := rfl

end

end Work.Pi6.MSS

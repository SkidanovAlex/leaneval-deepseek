import Mathlib
import Submission.Work.Pi6.MSS.e2Bar
import Submission.Work.Pi6.MSS.e2Lbar_exists
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The pairing `E_2^{s,q} × E²_{s,q} → 𝕜`

`Work.Pi6.MSS.e2Lbar` is the descent of `Work.Pi6.MSS.e2L0` to the second page of the Serre
filtration (`Work.Pi6.MSS.e2Lbar_exists`), with the computation rule `e2Lbar_mkQ` on
representatives.
-/

set_option autoImplicit false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The pairing on the second page**, on the level of `d¹`-cycles:
`E_2^{s,q} → (ker d¹ : E¹_{s,q} → E¹_{s-1,q})^*`, the descent of `e2L0`. -/
noncomputable def e2Lbar (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (s q : ℕ) :
    mssE 𝕜 (Wc 𝕜 p) 2 ((s : ℤ), (q : ℤ)) →ₗ[𝕜] (↥(e2KerD 𝕜 p s q) →ₗ[𝕜] 𝕜) :=
  Classical.choose (e2Lbar_exists 𝕜 E B p s q)

/-- The computation rule of `e2Lbar` on a representative. -/
theorem e2Lbar_mkQ (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s q : ℕ) (x : ↥(pZ 𝕜 (Wc 𝕜 p) 2 s (s + q))) :
    e2Lbar 𝕜 E B p s q
        (Submodule.mkQ ((pDen 𝕜 (Wc 𝕜 p) 2 s (s + q)).comap
          (pZ 𝕜 (Wc 𝕜 p) 2 s (s + q)).subtype) x)
      = e2L0 𝕜 E B p s q x :=
  Classical.choose_spec (e2Lbar_exists 𝕜 E B p s q) x

end

end Work.Pi6.MSS

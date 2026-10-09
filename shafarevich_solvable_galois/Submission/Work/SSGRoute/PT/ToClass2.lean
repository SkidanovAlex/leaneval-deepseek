import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `toClass2`: the total class map for the local `H²`

Mirror of `Work.SSGRoute.toClass` in degree `2`.  `toClass2 c` is the class of the `2`-cochain `c`
in the local `H²` of `H`, and `0` when `c` is not a locally constant `2`-cocycle on `H` (so that
the map is total and can be used as the computation rule of the degree-`2` localisation map
`H²(k,M) → ∏_A H²(k_v, M)` on arbitrary representatives).
-/

open Classical
open scoped Pointwise

namespace Work.SSGRoute

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- The class of `c` in the local `H²`; `0` if `c` is not a locally constant `2`-cocycle on `H`. -/
def toClass2 (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) : H2loc p k Ω K M H :=
  if hc : c ∈ lcCocycles2 p k Ω K M H then
    Submodule.mkQ (Submodule.comap (lcCocycles2 p k Ω K M H).subtype (coboundaries2 p k Ω K M H))
      ⟨c, hc⟩
  else 0

end

end Work.SSGRoute

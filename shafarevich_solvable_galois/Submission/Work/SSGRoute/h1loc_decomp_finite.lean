import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.local_tate_duality_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- Finiteness of the local `H¹` at a finite place, in `Module.Finite` form: this is the
`Module.Finite` restatement of `Work.SSGRoute.local_tate_duality_finite`. -/
theorem h1loc_decomp_finite
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M] :
    Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) := by
  haveI : Finite (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) :=
    Work.SSGRoute.local_tate_duality_finite p k Ω K A hA M
  exact Module.Finite.of_finite

end Work.SSGRoute

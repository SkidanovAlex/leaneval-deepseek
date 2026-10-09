import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.DualMod.Main
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local Euler characteristic (locally constant cochain model)

This module restates the **local Euler characteristic** of the Poitou–Tate workshop
(`Work.SSGRoute.local_tate_duality_euler`), one of the two arithmetic inputs of the local Tate
duality in degree one (Milne, *Arithmetic Duality Theorems* I.2.8; Neukirch–Schmidt–Wingberg 7.3.1):
for every finite place `A` of `Ω` over `k` there is a uniform constant `ε` (the local degree
`[k_v : ℚ_p]` in the residue-characteristic case, and `0` otherwise) such that

  `h¹ = h⁰ + h² + ε · dim M`   for every finite `𝔽_p[Gal(K|k)]`-module `M`,

with `h^i = dim H^i(D_A, M)` in the locally constant cochain model of `LTDDefs/Basic`, the
finiteness of `H¹` being part of the statement.

**Status.**  The source of this module had been lost from the tree (only its compiled artifact
remained; that artifact depended on `sorryAx`, so the statement below is a faithful restoration of
an *unproved* statement).  The file is restored again so that the local-duality rung
`Work.SSGRoute.local_tate_duality_mup_dim` builds from source; **the proof is an open obligation**
(the arithmetic of the `PTembedding`/`PT` lanes).  The companion module
`Submission/Work/SSGRoute/local_tate_duality_02.lean` restates the other input.
-/

namespace Work.SSGRoute

open scoped TensorProduct

/-- **The local Euler characteristic.**  For a finite place `A` of `Ω` over `k` there is a uniform
constant `ε` such that every finite `𝔽_p[Gal(K|k)]`-module `M` satisfies
`h¹ = h⁰ + h² + ε · dim M`, where `h^i = finrank (ZMod p) (H^i(D_A, M))`. -/
theorem local_tate_duality_euler
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    ∃ ε, ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Module.Finite (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) ∧
        Module.finrank (ZMod p) (Work.SSGRoute.H1loc p k Ω K M (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) ↥(Work.SSGRoute.H0loc p k Ω K M (SSGRoute.decomp k A)) +
              Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) +
            ε * Module.finrank (ZMod p) M := by
  sorry

end Work.SSGRoute

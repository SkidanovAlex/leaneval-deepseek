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
# Tate duality in degrees `0` and `2` at a finite place

This module restates **Tate duality in degrees `0` and `2`** for a decomposition group
(`Work.SSGRoute.local_tate_duality_02`), the second arithmetic input of the local Tate duality in
degree one (Milne, *Arithmetic Duality Theorems*, Cor. I.2.3 at `r = 0`): for every finite place `A`
of `Ω` over `k` and every finite `𝔽_p[Gal(K|k)]`-module `M`,

  `dim H²(D_A, M) = dim H⁰(D_A, M^∨(1))`   and   `dim H²(D_A, M^∨(1)) = dim H⁰(D_A, M)`,

where `M^∨(1) = DualMod p (M ⊗ T)` for a cyclotomic dual `T` (`SSGRoute.IsCyclotomicDual`).

**Status.**  The source of this module had been lost from the tree (only its compiled artifact
remained; that artifact depended on `sorryAx`, so the statement below is a faithful restoration of
an *unproved* statement).  The file is restored again so that the local-duality rung
`Work.SSGRoute.local_tate_duality_mup_dim` — and with it the reduction
`Work.SSGRoute.PT.localDuality02_of_core` — builds from source; **the proof is an open obligation**
(the arithmetic of the `PTembedding`/`PT` lanes).  The companion module
`Submission/Work/SSGRoute/local_tate_duality_euler.lean` restates the Euler-characteristic input.
-/

namespace Work.SSGRoute

open scoped TensorProduct

/-- **Tate duality in degrees `0` and `2` for a decomposition group.** -/
theorem local_tate_duality_02
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
    ∀ (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (M : Type)
        [AddCommGroup M] [Module (ZMod p) M]
        [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
        (Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K M (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A))) ∧
        (Module.finrank (ZMod p) (Work.SSGRoute.H2loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A)) =
          Module.finrank (ZMod p) (Work.SSGRoute.H0loc p k Ω K M (SSGRoute.decomp k A))) := by
  sorry

end Work.SSGRoute

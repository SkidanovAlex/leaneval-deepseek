import Mathlib
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.PT.ContModule
import Submission.Work.SSGRoute.PT.ToClass2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The product of the local cohomology groups over the finite places

`H1locProd p k Ω K M` (resp. `H2locProd`) is the product of the local `H¹` (resp. `H²`) groups
over the finite places `A` of `Ω` over `k`, i.e. the codomain of the assembled localisation map
`H¹(k, M) → ∏_A H¹(k_v, M)`.

It is packaged as a named `abbrev` because writing the codomain
`∀ A : {A // IsFinPlace k A}, H1loc … (decomp k A.1)` inline does not elaborate in reasonable time
(timeout at 8M heartbeats) — naming it once, with a raised budget, keeps the downstream statements
cheap.
-/

set_option maxHeartbeats 16000000

namespace Work.SSGRoute

noncomputable section

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- The product of the local `H¹`s over the finite places of `Ω` over `k`. -/
abbrev H1locProd (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] : Type _ :=
  ∀ A : {A : ValuationSubring Ω // SSGRoute.IsFinPlace k A},
    H1loc p k Ω K M (SSGRoute.decomp k A.1)

/-- The product of the local `H²`s over the finite places of `Ω` over `k`. -/
abbrev H2locProd (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] : Type _ :=
  ∀ A : {A : ValuationSubring Ω // SSGRoute.IsFinPlace k A},
    H2loc p k Ω K M (SSGRoute.decomp k A.1)

-- Does a `LinearMap` into the packaged product elaborate cheaply once the type is named?
example (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (locA : ∀ A : {A : ValuationSubring Ω // SSGRoute.IsFinPlace k A},
      H1contS p (Ω ≃ₐ[k] Ω) (K ≃ₐ[k] K) M (SSGRoute.res k K) ⊤ →ₗ[ZMod p]
        H1loc p k Ω K M (SSGRoute.decomp k A.1)) :
    H1contS p (Ω ≃ₐ[k] Ω) (K ≃ₐ[k] K) M (SSGRoute.res k K) ⊤ →ₗ[ZMod p]
      H1locProd p k Ω K M :=
  LinearMap.pi locA

/-- **Assembly of the degree-`1` localisation map.**  A per-place family of `ZMod p`-linear maps
with the `toClass` computation rule assembles, via `LinearMap.pi`, into the single map
`H¹(k,M) → ∏_A H¹(k_v,M)`. -/
theorem h1LocalizationAssembly
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (locA : ∀ A : {A : ValuationSubring Ω // SSGRoute.IsFinPlace k A},
      H1contS p (Ω ≃ₐ[k] Ω) (K ≃ₐ[k] K) M (SSGRoute.res k K) ⊤ →ₗ[ZMod p]
        H1loc p k Ω K M (SSGRoute.decomp k A.1))
    (hrule : ∀ (A : {A : ValuationSubring Ω // SSGRoute.IsFinPlace k A})
        (φ : ↥(Z1cont (Ω ≃ₐ[k] Ω) (K ≃ₐ[k] K) M (SSGRoute.res k K) ⊤)),
      locA A (QuotientAddGroup.mk φ) =
        toClass p k Ω K M (SSGRoute.decomp k A.1) (φ : (Ω ≃ₐ[k] Ω) → M)) :
    ∃ loc : H1contS p (Ω ≃ₐ[k] Ω) (K ≃ₐ[k] K) M (SSGRoute.res k K) ⊤ →ₗ[ZMod p]
        H1locProd p k Ω K M,
      ∀ (A : {A : ValuationSubring Ω // SSGRoute.IsFinPlace k A})
        (φ : ↥(Z1cont (Ω ≃ₐ[k] Ω) (K ≃ₐ[k] K) M (SSGRoute.res k K) ⊤)),
        loc (QuotientAddGroup.mk φ) A =
          toClass p k Ω K M (SSGRoute.decomp k A.1) (φ : (Ω ≃ₐ[k] Ω) → M) :=
  ⟨LinearMap.pi locA, fun A φ => hrule A φ⟩

/-- **Assembly of the degree-`2` localisation map.** -/
theorem h2LocalizationAssembly
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (locA : ∀ A : {A : ValuationSubring Ω // SSGRoute.IsFinPlace k A},
      H2contS p (Ω ≃ₐ[k] Ω) (K ≃ₐ[k] K) M (SSGRoute.res k K) ⊤ →ₗ[ZMod p]
        H2loc p k Ω K M (SSGRoute.decomp k A.1))
    (hrule : ∀ (A : {A : ValuationSubring Ω // SSGRoute.IsFinPlace k A})
        (c : ↥(Z2cont (Ω ≃ₐ[k] Ω) (K ≃ₐ[k] K) M (SSGRoute.res k K))),
      locA A (QuotientAddGroup.mk c) =
        toClass2 p k Ω K M (SSGRoute.decomp k A.1)
          (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M)) :
    ∃ loc : H2contS p (Ω ≃ₐ[k] Ω) (K ≃ₐ[k] K) M (SSGRoute.res k K) ⊤ →ₗ[ZMod p]
        H2locProd p k Ω K M,
      ∀ (A : {A : ValuationSubring Ω // SSGRoute.IsFinPlace k A})
        (c : ↥(Z2cont (Ω ≃ₐ[k] Ω) (K ≃ₐ[k] K) M (SSGRoute.res k K))),
        loc (QuotientAddGroup.mk c) A =
          toClass2 p k Ω K M (SSGRoute.decomp k A.1)
            (c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) :=
  ⟨LinearMap.pi locA, fun A c => hrule A c⟩

end

end Work.SSGRoute

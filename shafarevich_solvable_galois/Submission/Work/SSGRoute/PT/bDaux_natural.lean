import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.PT.archPairLocal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **`bDaux` is natural in the coefficient module.**  For a `ZMod p`-linear map
`f' : M₂' → M'` of coefficient modules, applying `f'` to a `⟨c⟩`-cocycle `b` and then descending to
`D_{u_c}` gives the same cochain as descending `b` first and then applying `f'`.

`bDaux` is `Classical.choose` of `PT.localCocycle_descent_exists`, whose spec pins it on *all* of
`D_{u_c} = (⟨c⟩).map (res k L)` (`bDaux_spec`); since `res k L` maps `⟨c⟩` onto `D_{u_c}` (`hDu`),
every `g : D_{u_c}` is `⟨res k L σ, _⟩` for some `σ ∈ ⟨c⟩`, so `bDaux (f' ∘ b)` and `bDaux b` are
determined by `b` alone and the identity is pointwise. -/
theorem bDaux_natural
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
    (f' : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T) →ₗ[ZMod p]
      Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (hres : SSGRoute.res k L c ≠ 1)
    (u : NK.GlobalCFT.Place ↥L)
    (hDu : SSGRoute.PTExt.decompK (k := k) u = (Subgroup.zpowers c).map (SSGRoute.res k L))
    (b : (Ω ≃ₐ[k] Ω) → VFcoef p M₂ T)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (fun σ => f' (b σ)))
    (w : NK.GlobalCFT.Place ↥K) (hu : NK.GlobalCFT.Place.LiesOver u w) :
    ∀ g, bDaux p k Ω K T M c hc2 L hKL hres u hDu (fun σ => f' (b σ)) hb' w hu g
      = f' (bDaux p k Ω K T M₂ c hc2 L hKL hres u hDu b hb w hu g) := by
  -- `bDaux` at an element of the form `⟨res k L σ, _⟩` is `b σ`, for *every* proof of membership.
  have keyM : ∀ (σ : ↥(Subgroup.zpowers c))
      (h : SSGRoute.res k L σ.1 ∈ SSGRoute.PTExt.decompK (k := k) u),
      (bDaux p k Ω K T M c hc2 L hKL hres u hDu (fun σ => f' (b σ)) hb' w hu
        ⟨SSGRoute.res k L σ.1, h⟩ : VFcoef p M T) = f' (b σ.1) := by
    intro σ h
    rw [show (⟨SSGRoute.res k L σ.1, h⟩ : ↥(SSGRoute.PTExt.decompK (k := k) u))
        = ⟨SSGRoute.res k L σ.1, by rw [hDu]; exact Subgroup.mem_map_of_mem _ σ.2⟩
      from Subtype.ext rfl]
    exact (bDaux_spec p k Ω K T M c hc2 L hKL hres u hDu (fun σ => f' (b σ)) hb' w hu).2 σ
  have keyM₂ : ∀ (σ : ↥(Subgroup.zpowers c))
      (h : SSGRoute.res k L σ.1 ∈ SSGRoute.PTExt.decompK (k := k) u),
      (bDaux p k Ω K T M₂ c hc2 L hKL hres u hDu b hb w hu
        ⟨SSGRoute.res k L σ.1, h⟩ : VFcoef p M₂ T) = b σ.1 := by
    intro σ h
    rw [show (⟨SSGRoute.res k L σ.1, h⟩ : ↥(SSGRoute.PTExt.decompK (k := k) u))
        = ⟨SSGRoute.res k L σ.1, by rw [hDu]; exact Subgroup.mem_map_of_mem _ σ.2⟩
      from Subtype.ext rfl]
    exact (bDaux_spec p k Ω K T M₂ c hc2 L hKL hres u hDu b hb w hu).2 σ
  intro g
  -- `bDaux`'s declared codomain is the carrier of `zRep`, which is only *definitionally* the bare
  -- module `VFcoef`; rewriting inside the goal needs the two spellings unified, so the pointwise
  -- goal is moved to the bare module first (`show` at default transparency).
  show ((bDaux p k Ω K T M c hc2 L hKL hres u hDu (fun σ => f' (b σ)) hb' w hu g
      : VFcoef p M T) = f' (bDaux p k Ω K T M₂ c hc2 L hKL hres u hDu b hb w hu g
        : VFcoef p M₂ T))
  obtain ⟨σ, hσ, hσeq⟩ := Subgroup.mem_map.mp (by rw [← hDu]; exact g.2)
  have hg : g = ⟨SSGRoute.res k L σ, by rw [hDu]; exact Subgroup.mem_map_of_mem _ hσ⟩ :=
    Subtype.ext hσeq.symm
  rw [hg, keyM ⟨σ, hσ⟩ (by rw [hDu]; exact Subgroup.mem_map_of_mem _ hσ),
    keyM₂ ⟨σ, hσ⟩ (by rw [hDu]; exact Subgroup.mem_map_of_mem _ hσ)]

end Work.SSGRoute.PT

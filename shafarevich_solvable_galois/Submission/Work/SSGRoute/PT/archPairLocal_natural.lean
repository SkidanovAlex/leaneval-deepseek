import Mathlib
import Submission.Work.SSGRoute.PT.archPairLocalClauses
import Submission.Work.SSGRoute.PT.archPairGuard_coefficient
import Submission.Work.SSGRoute.PT.G1plusOwn.naturalityBricks
import Submission.Work.SSGRoute.E7cOmega.unramifiedDetector_dwQuotient
import Submission.Work.SSGRoute.local_duality_ext_detect_h
import Submission.Work.SSGRoute.PT.bDaux_natural
import Submission.Work.SSGRoute.PT.archPairAbstract
import Submission.Work.SSGRoute.PT.archPairLocal_add_right
import Submission.Work.SSGRoute.PT.archPairLocal_coboundary
import Submission.Work.SSGRoute.PT.archPair_level_independent
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
set_option linter.style.haveILetI false

/-! ## The descent `PT.zLocal` is natural in the coefficient module

Given an equivariant `f' : M₂' → M'` of coefficient modules (and its induced morphism
`modRepMap f'` of `Gal(K/k)`-representations), the descended class `z_b` of a `⟨c⟩`-cocycle `b` is
natural:

`zLocal_M (f' ∘ b) = (zLocal_{M₂} b) · (mk₀ (res_{D_u} modRepMap f'))`,

i.e. pushing `zLocal_{M₂} b` along the coefficient morphism restricted to the decomposition group
`D_{u_c}` gives the descended class of `f' ∘ b`. -/

/-- **Naturality of `PT.zLocal` in the coefficient module.**  The two descended cocycles
`bDaux_M (f' ∘ b)` and `f' ∘ bDaux_{M₂} b` agree pointwise
(`PT.bDaux_natural`, because `bDaux_spec` pins the descent on all of `D_{u_c}`), so the classes in
`H¹(D_{u_c}, ·)` correspond under the coefficient morphism
`Rep.resMap (decompKRestrict) (Rep.resMap (decompK w).subtype (modRepMap f' hf')) =:
zRep M₂ ⟶ zRep M`; the `eCoh`/`H1π` packaging is natural in the coefficient module by
`Work.SSGRoute.E7cOmega.eCoh_one_comp_mk0`. -/
theorem zLocal_coeffNatural
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
    (hf' : ∀ (g : K ≃ₐ[k] K) (ψ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)),
      f' (g • ψ) = g • f' ψ)
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (hres : SSGRoute.res k L c ≠ 1)
    (u : NK.GlobalCFT.Place ↥L)
    (hDu : SSGRoute.PTExt.decompK (k := k) u = (Subgroup.zpowers c).map (SSGRoute.res k L))
    (b : (Ω ≃ₐ[k] Ω) → VFcoef p M₂ T)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (fun σ => f' (b σ)))
    (w : NK.GlobalCFT.Place ↥K) (hu : NK.GlobalCFT.Place.LiesOver u w)
    (hbD : ∀ g, bDaux p k Ω K T M c hc2 L hKL hres u hDu (fun σ => f' (b σ)) hb' w hu g
      = f' (bDaux p k Ω K T M₂ c hc2 L hKL hres u hDu b hb w hu g)) :
    (zLocal p k Ω K T M₂ c hc2 L hKL hres u hDu b hb w hu).comp
        (Abelian.Ext.mk₀ (Rep.resMap (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
          (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype
            (Work.SSGRoute.PTdualControl.modRepMap f' hf')))) (add_zero 1)
      = zLocal p k Ω K T M c hc2 L hKL hres u hDu (fun σ => f' (b σ)) hb' w hu := by
  simp only [zLocal]
  refine Work.SSGRoute.E7cOmega.eCoh_one_comp_mk0 (↥(SSGRoute.PTExt.decompK (k := k) u))
    (zRep p k Ω K T M₂ L u w hu) (zRep p k Ω K T M L u w hu)
    (Rep.resMap (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype
        (Work.SSGRoute.PTdualControl.modRepMap f' hf')))
    ⟨bDaux p k Ω K T M₂ c hc2 L hKL hres u hDu b hb w hu,
      bDaux_mem p k Ω K T M₂ c hc2 L hKL hres u hDu b hb w hu⟩
    ⟨bDaux p k Ω K T M c hc2 L hKL hres u hDu (fun σ => f' (b σ)) hb' w hu,
      bDaux_mem p k Ω K T M c hc2 L hKL hres u hDu (fun σ => f' (b σ)) hb' w hu⟩
    ?_
  intro g
  show ((bDaux p k Ω K T M c hc2 L hKL hres u hDu (fun σ => f' (b σ)) hb' w hu g
      : VFcoef p M T) = f' (bDaux p k Ω K T M₂ c hc2 L hKL hres u hDu b hb w hu g
        : VFcoef p M₂ T))
  exact hbD g

/-- **Clause (5) at the value level**: naturality of `PT.archPairValueZ` in the coefficient module,
at a fixed level `L`, place `u`, cocycles `a`, `b` and the two `zLocal`-classes. -/
theorem archPairValueZ_natural
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : G1pOwn.ChiK p k Ω K T)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
    (f' : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T) →ₗ[ZMod p]
      Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hff' : ∀ (ψ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)) (e : M) (t : T),
      f' ψ (TensorProduct.tmul (ZMod p) e t) = ψ (TensorProduct.tmul (ZMod p) (f e) t))
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → VFcoef p M₂ T)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (fun σ => f' (b σ)))
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (hres : SSGRoute.res k L c ≠ 1)
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (archW k Ω K φ))
    (hDu : SSGRoute.PTExt.decompK (k := k) u = (Subgroup.zpowers c).map (SSGRoute.res k L)) :
    archPairValueZ p k Ω K ζ hζ hζK T hT χ M₂ c (archW k Ω K φ) (fun σ => f (a σ)) L hKL u hu
        (zLocal p k Ω K T M₂ c hc2 L hKL hres u hDu b hb (archW k Ω K φ) hu)
      = archPairValueZ p k Ω K ζ hζ hζK T hT χ M c (archW k Ω K φ) a L hKL u hu
        (zLocal p k Ω K T M c hc2 L hKL hres u hDu (fun σ => f' (b σ)) hb'
          (archW k Ω K φ) hu) := by
  simp only [archPairValueZ]
  have hEq : ∀ (γ : K ≃ₐ[k] K) (ψ : VFcoef p M₂ T), f' (γ • ψ) = γ • f' ψ :=
    Work.SSGRoute.PT.G1pOwn.transpose_equivariant p k Ω K T M M₂ f hf f' hff'
  have hF' : ∀ (ψ : VFcoef p M₂ T) (e : M) (t : T),
      (show VFcoef p M T from
        (Work.SSGRoute.PTdualControl.modRepMap f' hEq).hom ψ) (TensorProduct.tmul (ZMod p) e t)
        = ψ (TensorProduct.tmul (ZMod p) (f e) t) := by
    intro ψ e t
    rw [Work.SSGRoute.PTdualControl.modRepMap_hom]
    exact hff' ψ e t
  rw [archβc_natural p k Ω K ζ hζ hζK T hT M M₂ f hf
        (Work.SSGRoute.PTdualControl.modRepMap f' hEq) hF' c hc2 hc1 φ hφ a ha,
      Work.SSGRoute.levelPair_coeff_naturality
        (f := Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
        (ι := Work.SSGRoute.localUnitsMap k ↥K ↥L (archW k Ω K φ) u hu)
        (π := Rep.resMap (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
          (Work.SSGRoute.PTdualControl.modRepMap f' hEq))
        (y := archβc p k Ω K ζ hζ hζK T hT M c (archW k Ω K φ) a)
        (h := zLocal p k Ω K T M₂ c hc2 L hKL hres u hDu b hb (archW k Ω K φ) hu),
      zLocal_coeffNatural p k Ω K T M M₂ f' hEq c hc2 L hKL hres u hDu b hb hb'
        (archW k Ω K φ) hu
        (bDaux_natural p k Ω K T M M₂ f' c hc2 L hKL hres u hDu b hb hb'
          (archW k Ω K φ) hu)]

/-- **Clause (5) at the involution for the local single-level archimedean pairing
`PT.archPairLocal`**: naturality in the coefficient module, for an equivariant
`f : M →ₗ[ZMod p] M₂` with transpose `f' : DualMod p (M₂ ⊗ T) →ₗ DualMod p (M ⊗ T)`.

Route.  Unfold both sides with `PT.archPairLocal_unfold` and install the instances for the named
level `PT.archPairLocalL k Ω K c hc1` exactly as `PT.archPairLocal_add_left` does.  The left-hand
side is `χ (ι (levelPair (archβc M₂ c (archW k Ω K φ) (f ∘ a)) (zLocal_{M₂} b)))`, the right-hand
side `χ (ι (levelPair (archβc M c (archW k Ω K φ) a) (zLocal_M (f' ∘ b))))`.  The three inputs are:
first, `PT.archβc_natural` (`PT/archβcClauses.lean`, proved), the `βc`-naturality mirror of the
`βl` clause, identifying `archβc M₂ c w (f ∘ a)` with the coefficient-transported
`archβc M c w a` (used through the proved `levelPair_coeff_naturality` of
`SSGRoute/local_duality_ext_detect_h.lean`); second, naturality of `PT.zLocal`: `bDaux` is the
descent of the cocycle through the fixed bijection from the group generated by the involution onto
`D_{u_c}` (`PT.bDaux_spec` pins it on all of `D_u`), so
`bDaux_M (f' ∘ b) = f' ∘ bDaux_{M₂} b` pointwise, whence `zLocal` commutes with the coefficient
transport (`H1π` and `eCoh` are natural in `zRep`, built from `VFcoef p M T`); third,
`PT.archPairGuard_coefficient` (proved) for the transport of the guard. -/
theorem archPairLocal_natural
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : G1pOwn.ChiK p k Ω K T)
    (hχcompat : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (L' : IntermediateField k Ω) [NumberField L']
      [FiniteDimensional k L'] [IsGalois k L'] (hKL' : K ≤ L') (hLL : L ≤ L')
      (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L' hKL' (Work.SSGRoute.PT.inflLevel L L' hLL u) = χ L hKL u)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
    (f' : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T) →ₗ[ZMod p]
      Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hff' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)) (e : M) (t : T),
      f' φ (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → VFcoef p M₂ T)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :
    archPairLocal p k Ω K ζ hζ hζK T hT χ M₂ c hc2 hc1 φ hφ (fun σ => f (a σ)) b
      = archPairLocal p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a (fun σ => f' (b σ)) := by
  -- the guard of the right-hand side: `f' ∘ b` is again a `⟨c⟩`-cocycle
  have hEq : ∀ (γ : K ≃ₐ[k] K) (ψ : VFcoef p M₂ T), f' (γ • ψ) = γ • f' ψ :=
    Work.SSGRoute.PT.G1pOwn.transpose_equivariant p k Ω K T M M₂ f hf f' hff'
  have hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (fun σ => f' (b σ)) := by
    intro g hg h hh
    show f' (b (g * h)) = f' (b g) + SSGRoute.res k K g • f' (b h)
    rw [hb g hg h hh, map_add, hEq (SSGRoute.res k K g) (b h)]
  rw [archPairLocal_unfold p k Ω K ζ hζ hζK T hT χ M₂ c hc2 hc1 φ hφ (fun σ => f (a σ)) b hb,
    archPairLocal_unfold p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a (fun σ => f' (b σ)) hb']
  haveI : FiniteDimensional k (archPairLocalL k Ω K c hc1) := archPairLocalL_fin k Ω K c hc1
  haveI : IsGalois k (archPairLocalL k Ω K c hc1) := archPairLocalL_gal k Ω K c hc1
  haveI : NumberField ↥(archPairLocalL k Ω K c hc1) := inferInstance
  have hKL' : K ≤ archPairLocalL k Ω K c hc1 := archPairLocalL_le k Ω K c hc1
  letI : Algebra ↥K ↥(archPairLocalL k Ω K c hc1) := (IntermediateField.inclusion hKL').toAlgebra
  letI : IsScalarTower k ↥K ↥(archPairLocalL k Ω K c hc1) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower ↥K ↥(archPairLocalL k Ω K c hc1) Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact archPairValueZ_natural p k Ω K ζ hζ hζK T hT χ M M₂ f hf f' hff' c hc2 hc1 φ hφ a b
    ha hb hb'
    (archPairLocalL k Ω K c hc1) (archPairLocalL_le k Ω K c hc1)
    (archPairLocalL_res k Ω K c hc1)
    (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
      (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω))))
    (liesOver_linked k Ω K (archPairLocalL k Ω K c hc1) φ)
    (decompK_linked k Ω (archPairLocalL k Ω K c hc1) c hc2 hc1 φ hφ)

/-- **Clause (5) at the value level, over an abstract seam dictionary.**

The mirror of `PT.archPairValueZ_natural` with `PT.archβc` replaced by the parameter
`bc : PT.SeamDict` and the `βc`-naturality clause supplied as the hypothesis `hbc`.  Nothing
concrete is used, so (unlike the concrete `archPairValueZ_natural`) this declaration is
`sorryAx`-free: the seam dictionary only occurs as a variable. -/
theorem archPairValueZAbs_natural
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (bc : SeamDict p k Ω K ζ hζ hζK T hT)
    (hbc : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (E2 : Type) [AddCommGroup E2] [Module (ZMod p) E2]
        [DistribMulAction (K ≃ₐ[k] K) E2] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E2] [Finite E2]
        (f : E →ₗ[ZMod p] E2) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
        (F' : SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) ⟶
          SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
        (hF' : ∀ (ψ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) (e : E) (t : T),
          (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom ψ)
            (TensorProduct.tmul (ZMod p) e t) = ψ (TensorProduct.tmul (ZMod p) (f e) t))
        (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
        (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
        (b : (Ω ≃ₐ[k] Ω) → E)
        (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b),
        bc E2 c (archW k Ω K φ) (fun σ => f (b σ)) =
          (CategoryTheory.Abelian.Ext.mk₀
            (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype F')).comp
            (bc E c (archW k Ω K φ) b) (zero_add 1))
    (χ : G1pOwn.ChiK p k Ω K T)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
    (f' : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T) →ₗ[ZMod p]
      Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hff' : ∀ (ψ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)) (e : M) (t : T),
      f' ψ (TensorProduct.tmul (ZMod p) e t) = ψ (TensorProduct.tmul (ZMod p) (f e) t))
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → VFcoef p M₂ T)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (fun σ => f' (b σ)))
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (hres : SSGRoute.res k L c ≠ 1)
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (archW k Ω K φ))
    (hDu : SSGRoute.PTExt.decompK (k := k) u = (Subgroup.zpowers c).map (SSGRoute.res k L)) :
    archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M₂ c (archW k Ω K φ) (fun σ => f (a σ))
        L hKL u hu (zLocal p k Ω K T M₂ c hc2 L hKL hres u hDu b hb (archW k Ω K φ) hu)
      = archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c (archW k Ω K φ) a L hKL u hu
        (zLocal p k Ω K T M c hc2 L hKL hres u hDu (fun σ => f' (b σ)) hb'
          (archW k Ω K φ) hu) := by
  simp only [archPairValueZAbs]
  have hEq : ∀ (γ : K ≃ₐ[k] K) (ψ : VFcoef p M₂ T), f' (γ • ψ) = γ • f' ψ :=
    Work.SSGRoute.PT.G1pOwn.transpose_equivariant p k Ω K T M M₂ f hf f' hff'
  have hF' : ∀ (ψ : VFcoef p M₂ T) (e : M) (t : T),
      (show VFcoef p M T from
        (Work.SSGRoute.PTdualControl.modRepMap f' hEq).hom ψ) (TensorProduct.tmul (ZMod p) e t)
        = ψ (TensorProduct.tmul (ZMod p) (f e) t) := by
    intro ψ e t
    rw [Work.SSGRoute.PTdualControl.modRepMap_hom]
    exact hff' ψ e t
  rw [hbc M M₂ f hf (Work.SSGRoute.PTdualControl.modRepMap f' hEq) hF' c hc2 hc1 φ hφ a ha,
      Work.SSGRoute.levelPair_coeff_naturality
        (f := Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
        (ι := Work.SSGRoute.localUnitsMap k ↥K ↥L (archW k Ω K φ) u hu)
        (π := Rep.resMap (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
          (Work.SSGRoute.PTdualControl.modRepMap f' hEq))
        (y := bc M c (archW k Ω K φ) a)
        (h := zLocal p k Ω K T M₂ c hc2 L hKL hres u hDu b hb (archW k Ω K φ) hu),
      zLocal_coeffNatural p k Ω K T M M₂ f' hEq c hc2 L hKL hres u hDu b hb hb'
        (archW k Ω K φ) hu
        (bDaux_natural p k Ω K T M M₂ f' c hc2 L hKL hres u hDu b hb hb'
          (archW k Ω K φ) hu)]

/-- **Clause (5) at the involution, over an abstract seam dictionary**: the taint-free form of
`PT.archPairLocal_natural`.  Same statement with `archPairLocal` replaced by the parameter
`bc : PT.SeamDict`, the `βc`-naturality clause carried as the hypothesis `hbc`; its type and body
mention no `Classical.choose`d dictionary, hence no `sorryAx`.

This is the form the abstract archimedean half consumes: instantiated at `bc := PT.archβcSeam` and
`hbc := PT.archβc_natural` it gives back the concrete clause (5). -/
theorem archPairLocalAbs_natural
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (bc : SeamDict p k Ω K ζ hζ hζK T hT)
    (hbc : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (E2 : Type) [AddCommGroup E2] [Module (ZMod p) E2]
        [DistribMulAction (K ≃ₐ[k] K) E2] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E2] [Finite E2]
        (f : E →ₗ[ZMod p] E2) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
        (F' : SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) ⟶
          SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
        (hF' : ∀ (ψ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) (e : E) (t : T),
          (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom ψ)
            (TensorProduct.tmul (ZMod p) e t) = ψ (TensorProduct.tmul (ZMod p) (f e) t))
        (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
        (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
        (b : (Ω ≃ₐ[k] Ω) → E)
        (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b),
        bc E2 c (archW k Ω K φ) (fun σ => f (b σ)) =
          (CategoryTheory.Abelian.Ext.mk₀
            (Rep.resMap (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype F')).comp
            (bc E c (archW k Ω K φ) b) (zero_add 1))
    (χ : G1pOwn.ChiK p k Ω K T)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
    (f' : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T) →ₗ[ZMod p]
      Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hff' : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M₂ T)) (e : M) (t : T),
      f' φ (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → VFcoef p M₂ T)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :
    archPairLocalAbs p k Ω K ζ hζ hζK T hT bc χ M₂ c hc2 hc1 φ hφ (fun σ => f (a σ)) b
      = archPairLocalAbs p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a (fun σ => f' (b σ)) := by
  have hEq : ∀ (γ : K ≃ₐ[k] K) (ψ : VFcoef p M₂ T), f' (γ • ψ) = γ • f' ψ :=
    Work.SSGRoute.PT.G1pOwn.transpose_equivariant p k Ω K T M M₂ f hf f' hff'
  have hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (fun σ => f' (b σ)) := by
    intro g hg h hh
    show f' (b (g * h)) = f' (b g) + SSGRoute.res k K g • f' (b h)
    rw [hb g hg h hh, map_add, hEq (SSGRoute.res k K g) (b h)]
  rw [archPairLocalAbs_unfold p k Ω K ζ hζ hζK T hT bc χ M₂ c hc2 hc1 φ hφ
        (fun σ => f (a σ)) b hb,
      archPairLocalAbs_unfold p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a
        (fun σ => f' (b σ)) hb']
  haveI : FiniteDimensional k (archPairLocalL k Ω K c hc1) := archPairLocalL_fin k Ω K c hc1
  haveI : IsGalois k (archPairLocalL k Ω K c hc1) := archPairLocalL_gal k Ω K c hc1
  haveI : NumberField ↥(archPairLocalL k Ω K c hc1) := inferInstance
  have hKL' : K ≤ archPairLocalL k Ω K c hc1 := archPairLocalL_le k Ω K c hc1
  letI : Algebra ↥K ↥(archPairLocalL k Ω K c hc1) := (IntermediateField.inclusion hKL').toAlgebra
  letI : IsScalarTower k ↥K ↥(archPairLocalL k Ω K c hc1) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower ↥K ↥(archPairLocalL k Ω K c hc1) Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact archPairValueZAbs_natural p k Ω K ζ hζ hζK T hT bc hbc χ M M₂ f hf f' hff' c hc2 hc1 φ hφ
    a b ha hb hb'
    (archPairLocalL k Ω K c hc1) (archPairLocalL_le k Ω K c hc1)
    (archPairLocalL_res k Ω K c hc1)
    (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
      (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω))))
    (liesOver_linked k Ω K (archPairLocalL k Ω K c hc1) φ)
    (decompK_linked k Ω (archPairLocalL k Ω K c hc1) c hc2 hc1 φ hφ)

/-- **Abstract clause (1) at the value level**: additivity of `archPairValueZAbs` in the first
variable, from the additivity of the seam dictionary `bc` (mirror of `PT.archPairValueZ_add_left`). -/
theorem archPairValueZAbs_add_left
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (bc : SeamDict p k Ω K ζ hζ hζK T hT)
    (hbcAdd : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
        (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
        (b b' : (Ω ≃ₐ[k] Ω) → E)
        (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
        (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b'),
        bc E c (archW k Ω K φ) (b + b') =
          bc E c (archW k Ω K φ) b + bc E c (archW k Ω K φ) b')
    (χ : G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a a' : (Ω ≃ₐ[k] Ω) → M)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (archW k Ω K φ))
    (z : SSGRoute.PTExt.extH (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T)))) 1)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a)
    (ha' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a') :
    archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c (archW k Ω K φ) (a + a') L hKL u hu z
      = archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c (archW k Ω K φ) a L hKL u hu z
        + archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c (archW k Ω K φ) a' L hKL u hu z := by
  simp only [archPairValueZAbs]
  rw [hbcAdd M c hc2 hc1 φ hφ a a' ha ha']
  exact chi_iota_levelPair_add_fst (k := k) (L := ↥L) p u (χ L hKL) (hχadd L hKL)
    (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
    (Work.SSGRoute.localUnitsMap k ↥K ↥L (archW k Ω K φ) u hu)
    (bc M c (archW k Ω K φ) a)
    (bc M c (archW k Ω K φ) a') z
    (by
      have hX : ∀ x : VFcoef p M T, p • x = 0 := fun x => nsmul_eq_zero_of_zmod' p x
      exact Work.SSGRoute.E6Util.ext_nsmul_p_torsion_left p hX
        (bc M c (archW k Ω K φ) a))
    (by
      have hX : ∀ x : VFcoef p M T, p • x = 0 := fun x => nsmul_eq_zero_of_zmod' p x
      exact Work.SSGRoute.E6Util.ext_nsmul_p_torsion_left p hX
        (bc M c (archW k Ω K φ) a'))

/-- **Abstract clause (1) at the wrapper level**: additivity of `archPairLocalAbs` in the first
variable (mirror of `PT.archPairLocal_add_left`). -/
theorem archPairLocalAbs_add_left
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (bc : SeamDict p k Ω K ζ hζ hζK T hT)
    (hbcAdd : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
        (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
        (b b' : (Ω ≃ₐ[k] Ω) → E)
        (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
        (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b'),
        bc E c (archW k Ω K φ) (b + b') =
          bc E c (archW k Ω K φ) b + bc E c (archW k Ω K φ) b')
    (χ : G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a a' : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a)
    (ha' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a')
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :
    archPairLocalAbs p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ (a + a') b
      = archPairLocalAbs p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a b
        + archPairLocalAbs p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a' b := by
  rw [archPairLocalAbs_unfold p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ (a + a') b hb,
    archPairLocalAbs_unfold p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a b hb,
    archPairLocalAbs_unfold p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a' b hb]
  haveI : FiniteDimensional k (archPairLocalL k Ω K c hc1) := archPairLocalL_fin k Ω K c hc1
  haveI : IsGalois k (archPairLocalL k Ω K c hc1) := archPairLocalL_gal k Ω K c hc1
  haveI : NumberField ↥(archPairLocalL k Ω K c hc1) := inferInstance
  have hKL' : K ≤ archPairLocalL k Ω K c hc1 := archPairLocalL_le k Ω K c hc1
  letI : Algebra ↥K ↥(archPairLocalL k Ω K c hc1) := (IntermediateField.inclusion hKL').toAlgebra
  letI : IsScalarTower k ↥K ↥(archPairLocalL k Ω K c hc1) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower ↥K ↥(archPairLocalL k Ω K c hc1) Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact archPairValueZAbs_add_left p k Ω K ζ hζ hζK T hT bc hbcAdd χ hχadd M c hc2 hc1 φ hφ a a'
    (archPairLocalL k Ω K c hc1) (archPairLocalL_le k Ω K c hc1)
    (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
      (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω))))
    (liesOver_linked k Ω K (archPairLocalL k Ω K c hc1) φ)
    (zLocal p k Ω K T M c hc2 (archPairLocalL k Ω K c hc1) (archPairLocalL_le k Ω K c hc1)
      (archPairLocalL_res k Ω K c hc1)
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω))))
      (decompK_linked k Ω (archPairLocalL k Ω K c hc1) c hc2 hc1 φ hφ) b hb
      (archW k Ω K φ) (liesOver_linked k Ω K (archPairLocalL k Ω K c hc1) φ))
    ha ha'

/-- **Abstract clause (2) at the value level**: additivity of `archPairValueZAbs` in its second
(`H¹`/`DualMod`) argument (mirror of `PT.archPairValueZ_add_snd`; no property of `bc` is used). -/
theorem archPairValueZAbs_add_snd
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (bc : SeamDict p k Ω K ζ hζ hζK T hT)
    (χ : G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a : (Ω ≃ₐ[k] Ω) → M)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (archW k Ω K φ))
    (z z' : SSGRoute.PTExt.extH (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T)))) 1) :
    archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c (archW k Ω K φ) a L hKL u hu (z + z')
      = archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c (archW k Ω K φ) a L hKL u hu z
        + archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c (archW k Ω K φ) a L hKL u hu z' := by
  simp only [archPairValueZAbs]
  refine chi_iota_levelPair_add_snd (k := k) (L := ↥L) p u (χ L hKL) (hχadd L hKL)
    (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
    (Work.SSGRoute.localUnitsMap k ↥K ↥L (archW k Ω K φ) u hu)
    (bc M c (archW k Ω K φ) a) z z' ?_ ?_
  · have hX : ∀ x : VFcoef p M T, p • x = 0 := fun x => nsmul_eq_zero_of_zmod' p x
    exact Work.SSGRoute.E6Util.ext_nsmul_p_torsion p hX z
  · have hX : ∀ x : VFcoef p M T, p • x = 0 := fun x => nsmul_eq_zero_of_zmod' p x
    exact Work.SSGRoute.E6Util.ext_nsmul_p_torsion p hX z'

/-- **Abstract clause (2) at the value level, on `zLocal`**: additivity of `archPairValueZAbs` in the
cocycle `b`, using the (clean) additivity `PT.zLocal_add` of the descent. -/
theorem archPairValueZAbs_add_snd_local
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (bc : SeamDict p k Ω K ζ hζ hζK T hT)
    (χ : G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a : (Ω ≃ₐ[k] Ω) → M)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (hres : SSGRoute.res k L c ≠ 1)
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (archW k Ω K φ))
    (hDu : SSGRoute.PTExt.decompK (k := k) u = (Subgroup.zpowers c).map (SSGRoute.res k L))
    (b b' : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b')
    (hsum : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (b + b')) :
    archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c (archW k Ω K φ) a L hKL u hu
        (zLocal p k Ω K T M c hc2 L hKL hres u hDu (b + b') hsum (archW k Ω K φ) hu)
      = archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c (archW k Ω K φ) a L hKL u hu
          (zLocal p k Ω K T M c hc2 L hKL hres u hDu b hb (archW k Ω K φ) hu)
        + archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c (archW k Ω K φ) a L hKL u hu
          (zLocal p k Ω K T M c hc2 L hKL hres u hDu b' hb' (archW k Ω K φ) hu) := by
  rw [zLocal_add p k Ω K T M c hc2 L hKL hres u hDu b b' hb hb' hsum (archW k Ω K φ) hu]
  exact archPairValueZAbs_add_snd p k Ω K ζ hζ hζK T hT bc χ hχadd M c hc2 hc1 φ hφ a L hKL u hu
    (zLocal p k Ω K T M c hc2 L hKL hres u hDu b hb (archW k Ω K φ) hu)
    (zLocal p k Ω K T M c hc2 L hKL hres u hDu b' hb' (archW k Ω K φ) hu)

/-- **Abstract clause (2) at the wrapper level**: additivity of `archPairLocalAbs` in the second
variable (mirror of `PT.archPairLocal_add_right`). -/
theorem archPairLocalAbs_add_right
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (bc : SeamDict p k Ω K ζ hζ hζK T hT)
    (χ : G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a : (Ω ≃ₐ[k] Ω) → M) (b b' : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (hb' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b') :
    archPairLocalAbs p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a (b + b')
      = archPairLocalAbs p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a b
        + archPairLocalAbs p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a b' := by
  have hsum : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (b + b') :=
    Work.SSGRoute.isCocycleOn_add hb hb'
  rw [archPairLocalAbs_unfold p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a (b + b') hsum,
    archPairLocalAbs_unfold p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a b hb,
    archPairLocalAbs_unfold p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a b' hb']
  haveI : FiniteDimensional k (archPairLocalL k Ω K c hc1) := archPairLocalL_fin k Ω K c hc1
  haveI : IsGalois k (archPairLocalL k Ω K c hc1) := archPairLocalL_gal k Ω K c hc1
  haveI : NumberField ↥(archPairLocalL k Ω K c hc1) := inferInstance
  have hKL' : K ≤ archPairLocalL k Ω K c hc1 := archPairLocalL_le k Ω K c hc1
  letI : Algebra ↥K ↥(archPairLocalL k Ω K c hc1) := (IntermediateField.inclusion hKL').toAlgebra
  letI : IsScalarTower k ↥K ↥(archPairLocalL k Ω K c hc1) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower ↥K ↥(archPairLocalL k Ω K c hc1) Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact archPairValueZAbs_add_snd_local p k Ω K ζ hζ hζK T hT bc χ hχadd M c hc2 hc1 φ hφ a
    (archPairLocalL k Ω K c hc1) (archPairLocalL_le k Ω K c hc1)
    (archPairLocalL_res k Ω K c hc1)
    (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
      (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω))))
    (liesOver_linked k Ω K (archPairLocalL k Ω K c hc1) φ)
    (decompK_linked k Ω (archPairLocalL k Ω K c hc1) c hc2 hc1 φ hφ)
    b b' hb hb' hsum

/-- **Abstract clause (3) at the wrapper level**: `archPairLocalAbs` vanishes when one argument is a
coboundary (mirror of `PT.archPairLocal_coboundary`), with the kernel clause of the seam dictionary
supplied as the hypothesis `hbcKer`. -/
theorem archPairLocalAbs_coboundary
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (bc : SeamDict p k Ω K ζ hζ hζK T hT)
    (hbcKer : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
        (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
        (b : (Ω ≃ₐ[k] Ω) → E)
        (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b),
        (bc E c (archW k Ω K φ) b = 0 ↔
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b))
    (χ : G1pOwn.ChiK p k Ω K T)
    (hχadd : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → p • v = 0 → χ L hKL (u + v) = χ L hKL u + χ L hKL v)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (hcob : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) a ∨
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :
    archPairLocalAbs p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a b = 0 := by
  rcases hcob with hacob | hbcob
  · rw [archPairLocalAbs_unfold p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a b hb]
    haveI : FiniteDimensional k (archPairLocalL k Ω K c hc1) := archPairLocalL_fin k Ω K c hc1
    haveI : IsGalois k (archPairLocalL k Ω K c hc1) := archPairLocalL_gal k Ω K c hc1
    haveI : NumberField ↥(archPairLocalL k Ω K c hc1) := inferInstance
    have hKL' : K ≤ archPairLocalL k Ω K c hc1 := archPairLocalL_le k Ω K c hc1
    letI : Algebra ↥K ↥(archPairLocalL k Ω K c hc1) :=
      (IntermediateField.inclusion hKL').toAlgebra
    letI : IsScalarTower k ↥K ↥(archPairLocalL k Ω K c hc1) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI : IsScalarTower ↥K ↥(archPairLocalL k Ω K c hc1) Ω :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    simp only [archPairValueZAbs]
    rw [(hbcKer M c hc2 hc1 φ hφ a ha).mpr hacob,
      Work.SSGRoute.levelPair_zero, Work.SSGRoute.PT.pt_iota_zero]
    exact chi_zero p k Ω K χ hχadd (archPairLocalL k Ω K c hc1) hKL'
  · rw [archPairLocalAbs_unfold p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a b hb]
    haveI : FiniteDimensional k (archPairLocalL k Ω K c hc1) := archPairLocalL_fin k Ω K c hc1
    haveI : IsGalois k (archPairLocalL k Ω K c hc1) := archPairLocalL_gal k Ω K c hc1
    haveI : NumberField ↥(archPairLocalL k Ω K c hc1) := inferInstance
    have hKL' : K ≤ archPairLocalL k Ω K c hc1 := archPairLocalL_le k Ω K c hc1
    letI : Algebra ↥K ↥(archPairLocalL k Ω K c hc1) :=
      (IntermediateField.inclusion hKL').toAlgebra
    letI : IsScalarTower k ↥K ↥(archPairLocalL k Ω K c hc1) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    letI : IsScalarTower ↥K ↥(archPairLocalL k Ω K c hc1) Ω :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    simp only [archPairValueZAbs]
    rw [zLocal_eq_zero_of_isCoboundaryOn p k Ω K T M c hc2 (archPairLocalL k Ω K c hc1) hKL'
        (archPairLocalL_res k Ω K c hc1)
        (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
          (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω))))
        (decompK_linked k Ω (archPairLocalL k Ω K c hc1) c hc2 hc1 φ hφ) b hb
        (archW k Ω K φ) (liesOver_linked k Ω K (archPairLocalL k Ω K c hc1) φ) hbcob,
      Work.SSGRoute.levelPair_zero_h, Work.SSGRoute.PT.pt_iota_zero]
    exact chi_zero p k Ω K χ hχadd (archPairLocalL k Ω K c hc1) hKL'

/-- **Clause (4), left, at the value level over an abstract seam dictionary.**

If the value of the pairing at a *fixed* level `L`, place `u | archW k Ω K φ` with `hDu`, vanishes
against every `z ∈ H¹(D_u, M^∨(1))`, then the dictionary value `bc M c (archW k Ω K φ) a` is `0`.
This is the first-variable detection of clause (4) over `bc`; converting `bc … a = 0` into
`SSGRoute.IsCoboundaryOn (res k K) (zpowers c) a` is the *kernel clause* `hbcKer` of the dictionary
(see `PT.archPairLocalAbs_coboundary`'s mirror), and `(∀ b, …) ↦ (∀ z, …)` is `PT.zLocal_surjective`
(hypothesis `hzSurj`).

Route (all inputs proved).  For `z = zLocal b hb` (`hzSurj`), the hypothesis reads
`χ (ι_u (levelPair (bc … a) z)) = 0` (`simp only [archPairValueZAbs]`).  `bc … a` is `p`-torsion
because `Ext¹` in a `p`-torsion first variable is `p`-torsion
(`archPair_ext_nsmul_eq_zero_of_ptorsion_left` + `nsmul_id_eq_zero_pt`), hence so is the level class
(`levelPair_nsmul_fst` + `levelPair_zero`) and its image under `ι_u` (`pt_iota_nsmul` + `pt_iota_zero`);
`hχinj` then gives `ι_u (levelPair (bc … a) z) = 0`, and
`PT.iota_injective_of_ptorsion` (`pt_orbitIdele_H2_eq_zero`) gives
`levelPair (bc … a) z = 0`.  As every `z` is a `zLocal b hb`, the non-degeneracy hypothesis `hnd2`
finishes. -/
theorem archPairValueZAbs_perfect_left
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (bc : SeamDict p k Ω K ζ hζ hζK T hT)
    (χ : G1pOwn.ChiK p k Ω K T)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (a : (Ω ≃ₐ[k] Ω) → M)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (hres : SSGRoute.res k L c ≠ 1)
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (archW k Ω K φ))
    (hDu : SSGRoute.PTExt.decompK (k := k) u = (Subgroup.zpowers c).map (SSGRoute.res k L))
    (hχinj : ∀ v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2,
      p • v = 0 → χ L hKL v = 0 → v = 0)
    (hnd2 : ∀ y : CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (archW k Ω K φ)) 1,
      (∀ z : SSGRoute.PTExt.extH
          (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
            (Rep.res (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
              (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T)))) 1,
        SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
          (Work.SSGRoute.localUnitsMap k ↥K ↥L (archW k Ω K φ) u hu) y z = 0) → y = 0)
    (hzSurj : ∀ z : SSGRoute.PTExt.extH (zRep p k Ω K T M L u (archW k Ω K φ) hu) 1,
      ∃ (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
        (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b),
        zLocal p k Ω K T M c hc2 L hKL hres u hDu b hb (archW k Ω K φ) hu = z) :
    (∀ z : SSGRoute.PTExt.extH
        (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T)))) 1,
      archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c (archW k Ω K φ) a L hKL u hu z = 0) →
      bc M c (archW k Ω K φ) a = 0 := by
  intro h
  -- the coefficient `bc M c (archW k Ω K φ) a` is `p`-torsion: its first variable `M^∨(1)` is
  have hptorn : (p : ℕ) • (bc M c (archW k Ω K φ) a) = 0 :=
    archPair_ext_nsmul_eq_zero_of_ptorsion_left p
      (nsmul_id_eq_zero_pt (G := ↥(SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)))
        (X := Rep.res (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
        p (fun x : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T) =>
          nsmul_eq_zero_of_zmod' p x))
      (bc M c (archW k Ω K φ) a)
  apply hnd2 (bc M c (archW k Ω K φ) a)
  intro z
  obtain ⟨b, hb, rfl⟩ := hzSurj z
  -- the level class of the pairing is `p`-torsion
  have hptlevel : p • (SSGRoute.PTExt.levelPair
      (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L (archW k Ω K φ) u hu)
      (bc M c (archW k Ω K φ) a)
      (zLocal p k Ω K T M c hc2 L hKL hres u hDu b hb (archW k Ω K φ) hu)) = 0 := by
    rw [← SSGRoute.PT.levelPair_nsmul_fst, hptorn, SSGRoute.levelPair_zero]
  -- the hypothesis, unfolded to `χ (ι_u (levelPair …)) = 0`
  have hzero : χ L hKL (iota (k := k) (L := ↥L) u
      (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
        (Work.SSGRoute.localUnitsMap k ↥K ↥L (archW k Ω K φ) u hu)
        (bc M c (archW k Ω K φ) a)
        (zLocal p k Ω K T M c hc2 L hKL hres u hDu b hb (archW k Ω K φ) hu))) = 0 := by
    have hb' := h (zLocal p k Ω K T M c hc2 L hKL hres u hDu b hb (archW k Ω K φ) hu)
    simpa only [archPairValueZAbs] using hb'
  have hptiota : p • iota (k := k) (L := ↥L) u
      (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
        (Work.SSGRoute.localUnitsMap k ↥K ↥L (archW k Ω K φ) u hu)
        (bc M c (archW k Ω K φ) a)
        (zLocal p k Ω K T M c hc2 L hKL hres u hDu b hb (archW k Ω K φ) hu)) = 0 := by
    rw [← SSGRoute.PT.pt_iota_nsmul, hptlevel, SSGRoute.PT.pt_iota_zero]
  refine Work.SSGRoute.PT.iota_injective_of_ptorsion (k := k) (L := ↥L) p u _ hptlevel
    (hχinj _ hptiota hzero)

/-- **Clause (4), right, at the value level over an abstract seam dictionary.**

If the value at a fixed level vanishes against every `M`-cocycle `a`, then the class `z` is `0`.
This is the second-variable detection of clause (4) over `bc`.  Combined with `hbcKer` and `PT.zLocal_surjective`
(`hzSurj`) it is what turns "pairing to zero against everything" into "is a coboundary" for the
second variable, through the two auxiliary lemmas `PT.zLocal_zero_imp_coboundary` (`heps`) and the
first-variable non-degeneracy `hnd1` of `levelPair`.

Route.  `hnd1` reduces to `levelPair y z = 0` for every `y`; the surjectivity clause `hbcSurj` of
the dictionary writes `y = bc … a` for a cocycle `a`, and the hypothesis at that `a` unfolds to
`χ (ι_u (levelPair y z)) = 0`; `z` is `p`-torsion (`extH_nsmul_eq_zero_of_ptorsion`, the coefficient
module `M^∨(1)` being a `ZMod p`-space), hence so is `levelPair y z`
(`levelPair_nsmul_snd` + `levelPair_zero_h`) and its `ι_u`-image (`pt_iota_nsmul` + `pt_iota_zero`),
so `hχinj` and `PT.iota_injective_of_ptorsion` finish. -/
theorem archPairValueZAbs_perfect_right
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (bc : SeamDict p k Ω K ζ hζ hζK T hT)
    (hbcSurj : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
        (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
        (y : CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
            (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (archW k Ω K φ)) 1),
        ∃ b : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧
          bc E c (archW k Ω K φ) b = y)
    (χ : G1pOwn.ChiK p k Ω K T)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (hres : SSGRoute.res k L c ≠ 1)
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (archW k Ω K φ))
    (hDu : SSGRoute.PTExt.decompK (k := k) u = (Subgroup.zpowers c).map (SSGRoute.res k L))
    (hχinj : ∀ v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2,
      p • v = 0 → χ L hKL v = 0 → v = 0)
    (hnd1 : ∀ z : SSGRoute.PTExt.extH
        (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T)))) 1,
      (∀ y : CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (archW k Ω K φ)) 1,
        SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
          (Work.SSGRoute.localUnitsMap k ↥K ↥L (archW k Ω K φ) u hu) y z = 0) → z = 0)
    (z : SSGRoute.PTExt.extH
        (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T)))) 1)
    (h : ∀ (a : (Ω ≃ₐ[k] Ω) → M),
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a →
      archPairValueZAbs p k Ω K ζ hζ hζK T hT bc χ M c (archW k Ω K φ) a L hKL u hu z = 0) :
    z = 0 := by
  -- `z` is `p`-torsion: the coefficient module `VFcoef p M T` is a `ZMod p`-space
  have hztor : (p : ℕ) • z = 0 :=
    Work.SSGRoute.PT.extH_nsmul_eq_zero_of_ptorsion _
      (fun x : Work.SSGRoute.PT.VFcoef p M T => nsmul_eq_zero_of_zmod' p x) z
  apply hnd1 z
  intro y
  obtain ⟨a, ha, rfl⟩ := hbcSurj M c hc2 hc1 φ hφ y
  have hzero : χ L hKL (iota (k := k) (L := ↥L) u
      (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
        (Work.SSGRoute.localUnitsMap k ↥K ↥L (archW k Ω K φ) u hu)
        (bc M c (archW k Ω K φ) a) z)) = 0 := by
    have hb' := h a ha
    simpa only [archPairValueZAbs] using hb'
  have hptlevel : p • (SSGRoute.PTExt.levelPair
      (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L (archW k Ω K φ) u hu)
      (bc M c (archW k Ω K φ) a) z) = 0 := by
    rw [← SSGRoute.PT.levelPair_nsmul_snd, hztor, SSGRoute.levelPair_zero_h]
  have hptiota : p • iota (k := k) (L := ↥L) u
      (SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
        (Work.SSGRoute.localUnitsMap k ↥K ↥L (archW k Ω K φ) u hu)
        (bc M c (archW k Ω K φ) a) z) = 0 := by
    rw [← SSGRoute.PT.pt_iota_nsmul, hptlevel, SSGRoute.PT.pt_iota_zero]
  exact Work.SSGRoute.PT.iota_injective_of_ptorsion (k := k) (L := ↥L) p u _ hptlevel
    (hχinj _ hptiota hzero)

/-- **Clause (4) (perfectness) at the involution, over an abstract seam dictionary.**

The `sorryAx`-free mirror of `Work.SSGRoute.PT.archPairLocal_perfect` with `archPairLocal ↦
archPairLocalAbs bc`, `archβc ↦ bc`: both perfectness conjuncts for the pairing
`archPairLocalAbs p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ`.

The content is the two value-level detections `archPairValueZAbs_perfect_left` /
`archPairValueZAbs_perfect_right` (this file), together with the dictionary's kernel clause
`hbcKer` and the local-duality inputs of the *linked* level, taken here in the level-generic form
that the consumers have:

* `hχinj` — `χ` is injective on `p`-torsion at every level (`ℤ/2`-involution case of the hub's
  `hχinj`);
* `hnd1`, `hnd2` — the two non-degeneracy halves of `levelPair` at `(L, seam place)`; in the
  workspace these come from `PT.archYoneda_perfect` (proved) plus
  `PT.archLevelPair_injective` (`PT/archLevelPair_injective.lean`, the level transport is
  injective);
* `hzSurj` — `PT.zLocal` is onto `H¹(D_u, PT.zRep …)` (`PT.zLocal_surjective`);
* `heps` — `PT.zLocal … b = 0 → b` is a `⟨c⟩`-coboundary (`PT.zLocal_zero_imp_coboundary`, the
  converse of the proved `PT.zLocal_eq_zero_of_isCoboundaryOn`);
* `hbcSurj` — the surjectivity clause of the dictionary (mirror of `PT.archβc_surjective`).

The first conjunct applies `hbcKer` in the direction `bc … a = 0 → a` coboundary after
`archPairValueZAbs_perfect_left` at `L_c := PT.archPairLocalL k Ω K c hc1` (unfolding
`PT.archPairLocalAbs` by `archPairLocalAbs_unfold` with the given guard `hb`); the second applies
`heps` and `archPairValueZAbs_perfect_right` in the same way. -/
theorem archPairLocalAbs_perfect
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (bc : SeamDict p k Ω K ζ hζ hζK T hT)
    (hbcKer : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
        (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
        (b : (Ω ≃ₐ[k] Ω) → E)
        (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b),
        (bc E c (archW k Ω K φ) b = 0 ↔
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b))
    (hbcSurj : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E]
        [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
        (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
        (y : CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
            (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (archW k Ω K φ)) 1),
        ∃ b : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧
          bc E c (archW k Ω K φ) b = y)
    (χ : G1pOwn.ChiK p k Ω K T)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hχinj : ∀ (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L]
      [IsGalois k ↥L] (hKL : K ≤ L) (v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • v = 0 → χ L hKL v = 0 → v = 0)
    (hnd1 : ∀ (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L]
      [IsGalois k ↥L] (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L]
      [IsScalarTower ↥K ↥L Ω]
      (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (archW k Ω K φ)),
      ∀ z : SSGRoute.PTExt.extH
          (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
            (Rep.res (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
              (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T)))) 1,
        (∀ y : CategoryTheory.Abelian.Ext
            (Rep.res (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
              (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
                (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
            (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (archW k Ω K φ)) 1,
          SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
            (Work.SSGRoute.localUnitsMap k ↥K ↥L (archW k Ω K φ) u hu) y z = 0) → z = 0)
    (hnd2 : ∀ (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L]
      [IsGalois k ↥L] (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L]
      [IsScalarTower ↥K ↥L Ω]
      (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (archW k Ω K φ)),
      ∀ y : CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
          (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (archW k Ω K φ)) 1,
        (∀ z : SSGRoute.PTExt.extH
            (Rep.res (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
              (Rep.res (SSGRoute.PTExt.decompK (k := k) (archW k Ω K φ)).subtype
                (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T)))) 1,
          SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (archW k Ω K φ) u hu)
            (Work.SSGRoute.localUnitsMap k ↥K ↥L (archW k Ω K φ) u hu) y z = 0) → y = 0)
    (hzSurj : ∀ (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L]
      [IsGalois k ↥L] (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L]
      [IsScalarTower ↥K ↥L Ω]
      (hres : SSGRoute.res k L c ≠ 1)
      (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (archW k Ω K φ))
      (hDu : SSGRoute.PTExt.decompK (k := k) u = (Subgroup.zpowers c).map (SSGRoute.res k L)),
      ∀ z : SSGRoute.PTExt.extH (zRep p k Ω K T M L u (archW k Ω K φ) hu) 1,
        ∃ (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
          (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b),
          zLocal p k Ω K T M c hc2 L hKL hres u hDu b hb (archW k Ω K φ) hu = z)
    (heps : ∀ (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L]
      [IsGalois k ↥L] (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L]
      [IsScalarTower ↥K ↥L Ω]
      (hres : SSGRoute.res k L c ≠ 1)
      (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u (archW k Ω K φ))
      (hDu : SSGRoute.PTExt.decompK (k := k) u = (Subgroup.zpowers c).map (SSGRoute.res k L))
      (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
      (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b),
      zLocal p k Ω K T M c hc2 L hKL hres u hDu b hb (archW k Ω K φ) hu = 0 →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :
    ((∀ a : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a →
        (∀ b : (Ω ≃ₐ[k] Ω) → VFcoef p M T,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
          archPairLocalAbs p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a b = 0) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) a) ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → VFcoef p M T,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        (∀ a : (Ω ≃ₐ[k] Ω) → M,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a →
          archPairLocalAbs p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a b = 0) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b)) := by
  haveI : FiniteDimensional k (archPairLocalL k Ω K c hc1) := archPairLocalL_fin k Ω K c hc1
  haveI : IsGalois k (archPairLocalL k Ω K c hc1) := archPairLocalL_gal k Ω K c hc1
  haveI : NumberField ↥(archPairLocalL k Ω K c hc1) := inferInstance
  have hKL' : K ≤ archPairLocalL k Ω K c hc1 := archPairLocalL_le k Ω K c hc1
  letI : Algebra ↥K ↥(archPairLocalL k Ω K c hc1) := (IntermediateField.inclusion hKL').toAlgebra
  letI : IsScalarTower k ↥K ↥(archPairLocalL k Ω K c hc1) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower ↥K ↥(archPairLocalL k Ω K c hc1) Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hres' : SSGRoute.res k (archPairLocalL k Ω K c hc1) c ≠ 1 := archPairLocalL_res k Ω K c hc1
  have hDu' : SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω))))
      = (Subgroup.zpowers c).map (SSGRoute.res k (archPairLocalL k Ω K c hc1)) :=
    decompK_linked k Ω (archPairLocalL k Ω K c hc1) c hc2 hc1 φ hφ
  have hu' : NK.GlobalCFT.Place.LiesOver
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω))))
      (archW k Ω K φ) := liesOver_linked k Ω K (archPairLocalL k Ω K c hc1) φ
  refine ⟨?_, ?_⟩
  · intro a ha h
    refine (hbcKer M c hc2 hc1 φ hφ a ha).mp ?_
    refine archPairValueZAbs_perfect_left p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a ha
      (archPairLocalL k Ω K c hc1) hKL' hres'
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω)))) hu' hDu'
      (hχinj (archPairLocalL k Ω K c hc1) hKL')
      (hnd2 (archPairLocalL k Ω K c hc1) hKL' _ hu')
      (hzSurj (archPairLocalL k Ω K c hc1) hKL' hres' _ hu' hDu') ?_
    intro z
    obtain ⟨b, hb, rfl⟩ :=
      hzSurj (archPairLocalL k Ω K c hc1) hKL' hres'
        (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
          (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω)))) hu' hDu' z
    have hb' := h b hb
    simpa only [archPairLocalAbs_unfold p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a b hb]
      using hb'
  · intro b hb h
    refine heps (archPairLocalL k Ω K c hc1) hKL' hres'
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω)))) hu' hDu' b hb ?_
    refine archPairValueZAbs_perfect_right p k Ω K ζ hζ hζK T hT bc
      (fun E _ _ _ _ _ c hc2 hc1 φ hφ y => hbcSurj E c hc2 hc1 φ hφ y) χ M c hc2 hc1 φ hφ
      (archPairLocalL k Ω K c hc1) hKL' hres'
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω)))) hu' hDu'
      (hχinj (archPairLocalL k Ω K c hc1) hKL') (hnd1 (archPairLocalL k Ω K c hc1) hKL' _ hu')
      (zLocal p k Ω K T M c hc2 (archPairLocalL k Ω K c hc1) hKL' hres'
        (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
          (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω))))
        hDu' b hb (archW k Ω K φ) hu') ?_
    intro a ha
    have hb' := h a ha
    simpa only [archPairLocalAbs_unfold p k Ω K ζ hζ hζK T hT bc χ M c hc2 hc1 φ hφ a b hb]
      using hb'

end Work.SSGRoute.PT

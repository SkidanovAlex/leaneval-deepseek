import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ExtChain.e1aCoeffH2_natural
import Submission.Work.SSGRoute.ExtChain.e1aDelta_natural
import Submission.Work.SSGRoute.ExtChain.e1c_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# E1a: the *canonical* Ext-side chain `Ext²_G(E',Kˣ) →+ H²(Γ,E)`

This module fixes, once and for all, the canonical chain used by the assembled map `β` of
`Work.SSGRoute.PT.e1a_ext_sha2_bridge`:

`Ext²_G(N, Kˣ) --(syzygy shift)⁻¹--> Ext¹_G(R_N, Kˣ) --(E1c)--> H¹(Γ, Hom_ℤ(R_N,Ωˣ))`
`  --δ--> H²(Γ, Hom_ℤ(N,Ωˣ)) --(coefficient)--> H²(Γ, E)`,

where `N = E' = DualMod p (E ⊗ T)`, `R_N = kernel (freeCover N)` is the canonical syzygy
(`Work.SSGRoute.ExtChain.FreeCover`), the `E1c` dictionary is the *canonical* one of
`Work.SSGRoute.ExtChain.e1c_natural` (chosen so that it carries a naturality square in the first
variable), `δ` is the connecting map `e1aDelta` of the dualised canonical resolution and the
coefficient map is `e1aCoeffH2`.

Every factor is a *named* map built from canonical data (no `Nonempty`-witnesses), which is what
makes the naturality clause of the target provable: the naturality squares of the four factors are
`syzygy shift` (`syzShift_natural`), `E1c` (`e1cMap_natural`), `δ` (`deltaH2_natural`) and the
coefficient (`e1aCoeffH2_natural`).
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]

attribute [local instance] Work.SSGRoute.freeCoverSES_finite

/-- **The canonical `Hom`-side chain**: the composite of the canonical syzygy shift (inverted),
the canonical `E1c` dictionary and the connecting map `δ` of the dualised canonical resolution. -/
noncomputable def e1aChainH (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V] :
    Abelian.Ext.{0} N (unitsK k K) 2 →+
      Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K N) :=
  (Work.SSGRoute.ExtChain.e1aDelta (k := k) (Ω := Ω) (K := K) N).comp
    ((Work.SSGRoute.ExtChain.e1cEquiv (k := k) (Ω := Ω) (K := K)
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))).toAddMonoidHom.comp
      (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N).symm.toAddMonoidHom)

/-- The computation rule of `e1aChainH`: it is the composite of the three canonical maps. -/
theorem e1aChainH_apply (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    (x : Abelian.Ext.{0} N (unitsK k K) 2) :
    e1aChainH (k := k) (Ω := Ω) (K := K) N x =
      Work.SSGRoute.ExtChain.e1aDelta (k := k) (Ω := Ω) (K := K) N
        (Work.SSGRoute.ExtChain.e1cEquiv (k := k) (Ω := Ω) (K := K)
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))
          ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N).symm x)) := rfl

/-- **The canonical `Hom`-side chain is injective** (each of its three factors is). -/
theorem e1aChainH_injective (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V] :
    Function.Injective (e1aChainH (k := k) (Ω := Ω) (K := K) N) :=
  (Work.SSGRoute.ExtChain.e1aDelta_injective (k := k) (Ω := Ω) (K := K) N).comp
    ((Work.SSGRoute.ExtChain.e1cEquiv (k := k) (Ω := Ω) (K := K)
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))).injective.comp
      (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N).symm.injective)

/-- **The canonical chain** `Ext²_G(E', Kˣ) →+ H²(Γ,E)`, `E' = DualMod p (E ⊗ T)`: the `Hom`-side
chain composed with the coefficient identification `e1aCoeffH2`. -/
noncomputable def e1aChainC (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
        (SSGRoute.PTExt.unitsK k K) 2 →+
      @Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω) E _ _ _
        (DistribMulAction.compHom E (SSGRoute.res k K)) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  haveI : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI : Finite (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  exact (Work.SSGRoute.ExtChain.e1aCoeffH2 p k Ω K ζ hζ hζK T hT E).comp
    (e1aChainH (k := k) (Ω := Ω) (K := K)
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))

/-- **The canonical chain is injective.** -/
theorem e1aChainC_injective (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] :
    Function.Injective (e1aChainC p k Ω K ζ hζ hζK T hT E) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E := DistribMulAction.compHom E (SSGRoute.res k K)
  haveI : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI : Finite (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  exact (Work.SSGRoute.ExtChain.e1aCoeffH2_injective p k Ω K ζ hζ hζK T hT E).comp
    (e1aChainH_injective (k := k) (Ω := Ω) (K := K)
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))


/-! ## Naturality of the canonical chain in the coefficient `E`

The four squares: syzygy shift (`ExtChain.syzShift_natural`), `E1c` (`ExtChain.e1cMap_natural`),
`δ` (`ExtChain.e1aDelta_natural`) and the coefficient (`ExtChain.e1aCoeffH2_natural`). -/

/-- The canonical `E1c` dictionary is the map `e1cMap`. -/
theorem e1cEquiv_apply (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (x : Abelian.Ext.{0} R (unitsK k K) 1) :
    Work.SSGRoute.ExtChain.e1cEquiv (k := k) (Ω := Ω) (K := K) R x =
      Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K) R x := rfl

/-- **Naturality of the `Hom`-side chain in the first variable**: for `F : N₂ ⟶ N₁`, the canonical
presentations' comparison makes `e1aChainH` commute with the precomposition maps. -/
theorem e1aChainH_natural (N₁ N₂ : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    [Finite N₁.V] [Finite N₂.V] (F : N₂ ⟶ N₁)
    (x : Abelian.Ext.{0} N₁ (unitsK k K) 2) :
    e1aChainH (k := k) (Ω := Ω) (K := K) N₂
        ((Abelian.Ext.mk₀ F).comp x (zero_add 2)) =
      Work.AbsoluteKummer.mapH2
        (Work.SSGRoute.precompAddHom (Rep.Hom.hom F).toAddMonoidHom)
        (Work.SSGRoute.ExtChain.precompAddHom_equivariant F)
        (e1aChainH (k := k) (Ω := Ω) (K := K) N₁ x) := by
  have hshift : (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N₂).symm
        ((Abelian.Ext.mk₀ F).comp x (zero_add 2))
      = (Abelian.Ext.mk₀ (Work.SSGRoute.freeMapKernel F)).comp
          ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N₁).symm x) (zero_add 1) := by
    have h := Work.SSGRoute.ExtChain.syzShift_natural (k := k) (Ω := Ω) (K := K) N₁ N₂ F
      ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N₁).symm x)
    have h2 : Work.SSGRoute.ExtChain.e1aSyzMap (k := k) (Ω := Ω) (K := K) N₁
        ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N₁).symm x) = x :=
      AddEquiv.apply_symm_apply (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N₁) x
    rw [h2] at h
    have h3 : (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N₂).symm
        (Work.SSGRoute.ExtChain.e1aSyzMap (k := k) (Ω := Ω) (K := K) N₂
          ((Abelian.Ext.mk₀ (Work.SSGRoute.freeMapKernel F)).comp
            ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N₁).symm x) (zero_add 1)))
        = (Abelian.Ext.mk₀ (Work.SSGRoute.freeMapKernel F)).comp
            ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N₁).symm x) (zero_add 1) :=
      AddEquiv.symm_apply_apply _ _
    have h4 := congrArg (Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N₂).symm h
    rw [h3] at h4
    exact h4.symm
  rw [e1aChainH_apply, e1aChainH_apply, hshift, e1cEquiv_apply,
    Work.SSGRoute.ExtChain.e1cMap_natural (k := k) (Ω := Ω) (K := K)
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N₂))
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N₁))
      (Work.SSGRoute.freeMapKernel F)
      (Work.SSGRoute.ExtChain.precompAddHom_equivariant (Work.SSGRoute.freeMapKernel F))
      ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N₁).symm x)]
  exact Work.SSGRoute.ExtChain.e1aDelta_natural (k := k) (Ω := Ω) (K := K) N₁ N₂ F
    (Work.SSGRoute.ExtChain.precompAddHom_equivariant F)
    (Work.SSGRoute.ExtChain.precompAddHom_equivariant (Work.SSGRoute.freeMapKernel F))
    (Work.SSGRoute.ExtChain.e1cMap (k := k) (Ω := Ω) (K := K)
      (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N₁))
      ((Work.SSGRoute.ExtChain.e1aSyzShift (k := k) (K := K) N₁).symm x))

/-- **Naturality of the canonical chain in the coefficient `E`**: for an equivariant
`f : E₁ →ₗ E₂` with transpose `F`, the chain commutes with the induced maps. -/
theorem e1aChainC_natural (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E₁ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
    (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
    (f : E₁ →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
    (F : SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) ⟶
        SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T)))
    (hF : ∀ (φ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E₁) (t : T),
      (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T) from F.hom φ)
        (TensorProduct.tmul (ZMod p) e t) = φ (TensorProduct.tmul (ZMod p) (f e) t))
    (y : Abelian.Ext.{0} (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T)))
        (SSGRoute.PTExt.unitsK k K) 2) :
    e1aChainC p k Ω K ζ hζ hζK T hT E₂ ((Abelian.Ext.mk₀ F).comp y (zero_add 2)) =
      e1aH2Map p k Ω K E₁ E₂ f hf (e1aChainC p k Ω K ζ hζ hζK T hT E₁ y) := by
  haveI hTfin : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI hN₁ : Finite (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T))).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E₁ T
  haveI hN₂ : Finite (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T))).V :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E₂ T
  show Work.SSGRoute.ExtChain.e1aCoeffH2 p k Ω K ζ hζ hζK T hT E₂
      (e1aChainH (k := k) (Ω := Ω) (K := K)
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)))
        ((Abelian.Ext.mk₀ F).comp y (zero_add 2)))
    = e1aH2Map p k Ω K E₁ E₂ f hf
        (Work.SSGRoute.ExtChain.e1aCoeffH2 p k Ω K ζ hζ hζK T hT E₁
          (e1aChainH (k := k) (Ω := Ω) (K := K)
            (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T))) y))
  rw [e1aChainH_natural (k := k) (Ω := Ω) (K := K)
    (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T)))
    (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)))
    F y]
  exact Work.SSGRoute.ExtChain.e1aCoeffH2_natural p k Ω K ζ hζ hζK T hT E₁ E₂ f hf F hF
    (Work.SSGRoute.ExtChain.precompAddHom_equivariant F)
    (e1aChainH (k := k) (Ω := Ω) (K := K)
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T))) y)

end

end Work.SSGRoute.PT

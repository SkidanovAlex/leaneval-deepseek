import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ArchDictionary.p2Link
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local coefficient identification at a complex archimedean place (`p = 2`)

At a complex archimedean place `w` of `K` (`decompK w ≠ ⊥`) with `p = 2`, the cyclotomic dual `T`
is trivial (`PTdualControl.T_trivial_p2`), so `E' = DualMod 2 (E ⊗ T) = Hom(E, F_2)` is `2`-torsion,
and every `Z`-linear map `E'.V → K_w^x` lands in `mu_2 = {±1} ⊆ K_w`.  The canonical coefficient
identification is therefore `E ≃+ Hom_Z(E'.V, K_w^x)` given by the *same* formula as the global one
(`E1aClean.coeffEquivGeneric`), namely `e ↦ (φ ↦ ζu ^ (φ (e ⊗ t0)))` with `ζu = -1 ∈ K_w^x`.

This module provides

* `neg_one_isPrimitiveRoot_units`, `localField_two_ne_zero`;
* `linAddEquiv_symm_apply` — the computation rule of the inverse of the linear/additive bridge;
* **`localCoeffP2`** — the family `E ≃+ ((Eprime 2 k Ω K T E).V ->l[Coeff] (localUnitsK w).V)`;
* **`localCoeffP2_apply`** — its computation rule;
* **`localCoeffP2_natural`** — its naturality in the coefficient `E` (the square with `homRepPre`).

The one missing ingredient (delegated, see the lane NOTE) is the *equivariance* of `localCoeffP2`
for the `D_w`-action, which is what makes `mapH1 (localCoeffP2)^{-1}` typecheck.
-/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]

/-- `-1` is a primitive square root of unity in a domain of characteristic `≠ 2`. -/
theorem neg_one_isPrimitiveRoot_units {A : Type} [CommRing A] [IsDomain A]
    (h2 : (2 : A) ≠ 0) : IsPrimitiveRoot (-1 : Aˣ) 2 := by
  have h1 : ((-1 : Aˣ)) ^ 2 = 1 := by ext; simp [sq]
  have hne : (-1 : Aˣ) ≠ 1 := by
    intro h
    apply h2
    have := congrArg (fun u : Aˣ => (u : A)) h
    simp at this
    linear_combination (norm := ring_nf) -this
  exact IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime h1 hne)

/-- The local field at a complex archimedean place has characteristic `0`. -/
theorem localField_two_ne_zero (w : NK.GlobalCFT.Place ↥K) :
    (2 : NK.GlobalCFT.Place.localField ↥K w) ≠ 0 := by
  rw [show (2 : NK.GlobalCFT.Place.localField ↥K w)
      = algebraMap ↥K _ (2 : ↥K) from (map_ofNat _ 2).symm]
  exact fun h => two_ne_zero (RingHom.injective (algebraMap ↥K _) (by rw [h, map_zero]))

/-- Computation rule for the inverse of `linAddEquiv`. -/
theorem linAddEquiv_symm_apply (V W : Type) [AddCommGroup V] [AddCommGroup W]
    [Module SSGRoute.PTExt.Coeff V] [Module SSGRoute.PTExt.Coeff W]
    (g : V →+ W) (x : V) :
    ((Work.SSGRoute.linAddEquiv V W).symm g) x = g x := rfl

/-- **The canonical coefficient identification at a complex archimedean place, `p = 2`**:
`E ≃+ Hom_Z(E', K_w^x)`, `e ↦ (φ ↦ (-1) ^ (φ (e ⊗ t0)))`. -/
noncomputable def localCoeffP2 (T : Type) [AddCommGroup T] [Module (ZMod 2) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) (-1 : Ω))
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    (w : NK.GlobalCFT.Place ↥K) :
    E ≃+ ((Eprime 2 k Ω K T E).V →ₗ[SSGRoute.PTExt.Coeff]
      (localUnitsK (k := k) w).V) := by
  refine (Work.SSGRoute.E1aClean.coeffEquivGeneric 2 E T hT.1
      (-1 : (NK.GlobalCFT.Place.localField ↥K w)ˣ)
      (neg_one_isPrimitiveRoot_units (localField_two_ne_zero (K := K) w))).trans ?_
  exact (Work.SSGRoute.linAddEquiv (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))
    (Additive ((NK.GlobalCFT.Place.localField ↥K w)ˣ))).symm

/-- The computation rule of `localCoeffP2`. -/
theorem localCoeffP2_apply (T : Type) [AddCommGroup T] [Module (ZMod 2) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) (-1 : Ω))
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    (w : NK.GlobalCFT.Place ↥K) (e : E) (φ : Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T)) :
    (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w e) φ
      = Work.SSGRoute.zetaPowHom (-1 : (NK.GlobalCFT.Place.localField ↥K w)ˣ)
          (neg_one_isPrimitiveRoot_units (localField_two_ne_zero (K := K) w))
          (φ (TensorProduct.tmul (ZMod 2) e (Work.SSGRoute.PT.e1aTGen 2 T hT.1))) := by
  have h : localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w e
      = (Work.SSGRoute.linAddEquiv (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))
          (Additive ((NK.GlobalCFT.Place.localField ↥K w)ˣ))).symm
          (Work.SSGRoute.E1aClean.coeffEquivGeneric 2 E T hT.1
            (-1 : (NK.GlobalCFT.Place.localField ↥K w)ˣ)
            (neg_one_isPrimitiveRoot_units (localField_two_ne_zero (K := K) w)) e) := rfl
  rw [h]
  exact Work.SSGRoute.E1aClean.coeffEquivGeneric_apply 2 E T hT.1
    (-1 : (NK.GlobalCFT.Place.localField ↥K w)ˣ)
    (neg_one_isPrimitiveRoot_units (localField_two_ne_zero (K := K) w)) e φ

/-- **Naturality of `localCoeffP2` in the coefficient module.** -/
theorem localCoeffP2_natural (T : Type) [AddCommGroup T] [Module (ZMod 2) T]
    [DistribMulAction (K ≃ₐ[k] K) T] [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) (-1 : Ω))
    (w : NK.GlobalCFT.Place ↥K)
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    (E₂ : Type) [AddCommGroup E₂] [Module (ZMod 2) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E₂] [Finite E₂]
    (f : E →ₗ[ZMod 2] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
    (F' : Eprime 2 k Ω K T E₂ ⟶ Eprime 2 k Ω K T E)
    (hF' : ∀ (θ : Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E₂ T)) (e : E) (t : T),
      (show Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T) from F'.hom θ)
        (TensorProduct.tmul (ZMod 2) e t) = θ (TensorProduct.tmul (ZMod 2) (f e) t))
    (e : E) :
    localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E₂ w (f e)
      = ((Work.SSGRoute.homRepPre
            (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime 2 k Ω K T E))
            (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime 2 k Ω K T E₂))
            (localUnitsK (k := k) w)
            (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype F')).hom
              (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w e)
          : (Eprime 2 k Ω K T E₂).V →ₗ[SSGRoute.PTExt.Coeff] (localUnitsK (k := k) w).V) := by
  apply LinearMap.ext
  intro φ
  rw [localCoeffP2_apply (k := k) (Ω := Ω) (K := K) T hT E₂ w (f e) φ]
  rw [Work.SSGRoute.homRepPre_apply
    (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime 2 k Ω K T E))
    (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype (Eprime 2 k Ω K T E₂))
    (localUnitsK (k := k) w)
    (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype F')
    (localCoeffP2 (k := k) (Ω := Ω) (K := K) T hT E w e) φ]
  dsimp only
  rw [localCoeffP2_apply (k := k) (Ω := Ω) (K := K) T hT E w e
    (Rep.Hom.hom (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype F') φ)]
  congr 1
  exact (hF' φ e (Work.SSGRoute.PT.e1aTGen 2 T hT.1)).symm

end Work.SSGRoute.ArchDictionary

import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.G1plusOwn.extHRestrict_infinite_eq_zero
import Submission.Work.SSGRoute.PT.G1plusOwn.extLocVanishing
import Submission.Work.SSGRoute.PT.G1plusOwn.reciprocityAux
import Submission.Work.SSGRoute.PT.classFormation_reciprocity_allPlaces
import Submission.Work.SSGRoute.PT.glue_realiser_abstract
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Clause (7) of `G1⁺`: the assembly pieces of the finite-place reciprocity

This file holds the *reusable* pieces of the proof of
`Work.SSGRoute.PT.G1plusOwn.g1FinHalf_reciprocity` (the frozen target in
`Submission/Work/SSGRoute/PT/G1plusOwn/g1FinHalf_reciprocity.lean`):

* the restriction of the local-constancy/cocycle hypotheses from `⊤` to a decomposition group;
* the crossed-homomorphism condition of the level-`L` factorisation `b₀` of a global cocycle `b`
  (from the surjectivity of `AlgEquiv.restrictNormalHom`);
* the *off-`S'` local vanishing* of the global class
  `Y = levelPair (galRes) (idleRepMap) (extToIdeles (finZBg a)) (hClass b₀ hb₀)`, both at the
  finite places outside the conjugacy classes of `S'` (via the level `L` of
  `exists_good_level_unramified` being unramified there and `PT.finZB`'s unramified clause) and at
  the infinite places (via `extHRestrict_infinite_eq_zero`);
* the `p`-torsion of `Y` and the exactness `extToClasses Y = 0`.
-/

namespace Work.SSGRoute.PT.G1plusOwn

open scoped TensorProduct
open SSGRoute.PTExt CategoryTheory

noncomputable section

set_option linter.unusedSectionVars false

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]

/-- Local constancy restricts to a subgroup. -/
theorem isLocConstOn_of_le {Γ G M' : Type} [Group Γ] [TopologicalSpace Γ] [Group G]
    [AddCommGroup M'] [DistribMulAction G M'] {H H' : Subgroup Γ} (hHH : H ≤ H')
    {f : Γ → M'} (hf : SSGRoute.IsLocConstOn H' f) : SSGRoute.IsLocConstOn H f := by
  obtain ⟨U, hU, hU'⟩ := hf
  exact ⟨U, hU, fun g hg u hu huH => hU' g (hHH hg) u hu (hHH huH)⟩

/-- The cocycle condition restricts to a subgroup. -/
theorem isCocycleOn_of_le {Γ G M' : Type} [Group Γ] [Group G] [AddCommGroup M']
    [DistribMulAction G M'] (act : Γ →* G) {H H' : Subgroup Γ} (hHH : H ≤ H')
    {f : Γ → M'} (hf : SSGRoute.IsCocycleOn act H' f) : SSGRoute.IsCocycleOn act H f :=
  fun g hg h hh => hf g (hHH hg) h (hHH hh)

/-- **The level-`L` factorisation `b₀` of a global cocycle `b` is a crossed homomorphism** for the
`Gal(K/k)`-action pulled back along `galRes k K L`.  Every pair `(g, h)` of `Gal(L/k)` lifts to
`Gal(Ω/k)` (`AlgEquiv.restrictNormalHom_surjective`), where the cocycle condition for `b` applies;
`res k K σ = galRes k K L (res k L σ)` (`PTExt.galRes_trans`). -/
theorem crossedHom_of_factorises {L : IntermediateField k Ω} [Normal k L]
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hb1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b)
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hb₀ : ∀ σ : Ω ≃ₐ[k] Ω, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)) :
    ∀ g h : ↥L ≃ₐ[k] ↥L,
      b₀ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • b₀ h + b₀ g := by
  intro g h
  obtain ⟨σ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := L) (E := Ω) g
  obtain ⟨τ, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := L) (E := Ω) h
  have h' := hb1 σ (Subgroup.mem_top σ) τ (Subgroup.mem_top τ)
  rw [hb₀ (σ * τ), hb₀ σ, hb₀ τ] at h'
  rw [map_mul] at h'
  rw [show SSGRoute.res k K σ
      = SSGRoute.PTExt.galRes k (↥K) (↥L) (AlgEquiv.restrictNormalHom L σ) from
    (SSGRoute.PTExt.galRes_trans (k := k) (K := ↥K) (L := ↥L) (L' := Ω) σ).symm] at h'
  rw [h']
  abel

/-- `hClass` is `levelClassOf` (both are `ExtH1.gammaHom` of the class of the same cocycle). -/
theorem hClass_eq_levelClassOf {L : IntermediateField k Ω} [NumberField L]
    [FiniteDimensional k L] [IsGalois k L] [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L]
    [IsScalarTower ↥K ↥L Ω]
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hψ : ∀ g h : ↥L ≃ₐ[k] ↥L,
      b₀ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • b₀ h + b₀ g) :
    Work.SSGRoute.PT.G1plusOwn.hClass p k Ω K T M (L := L) b₀ hψ
      = Work.SSGRoute.PT.levelClassOf (p := p) (k := k) (Ω := Ω) (K := K) (L := L)
          (T := T) (M := M) b₀ hψ := rfl

/-- `¬ IsRamifiedIn` is the containment of the inertia subgroup in the fixing subgroup. -/
theorem inertiaSub_le_of_not_isRamifiedIn {L : IntermediateField k Ω} (A : ValuationSubring Ω)
    (h : ¬ SSGRoute.IsRamifiedIn k L A) :
    Work.SSGRoute.inertiaSub k Ω A ≤ L.fixingSubgroup := by
  intro σ hσ
  by_contra hσ'
  exact h ⟨σ, (Work.SSGRoute.mem_inertiaSub k Ω A σ).mp hσ, hσ'⟩

/-- **The off-`S'` finite-place vanishing.**  At a finite place `v` of `Ω` which is not conjugate
to any element of `S'`, the `w_A`-component of the global class `Y` vanishes: the base class
`extLoc (finQ K v) X` is unramified at `finQ K v` (`finZB_unramified` + the square `finZB_square`)
and the level `L` is unramified at `finQW L v` (`hramLv`). -/
theorem extLoc_finQW_eq_zero_of_not_conj (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    {L : IntermediateField k Ω} [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    [Normal k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (a : (Ω ≃ₐ[k] Ω) → M)
    (ha1 : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a) (ha2 : SSGRoute.IsLocConstOn ⊤ a)
    (v : ValuationSubring Ω) (hv : SSGRoute.IsFinPlace k v)
    (hpv : ¬ v.valuation (p : Ω) < 1) (hramKv : ¬ SSGRoute.IsRamifiedIn k K v)
    (hramLv : ¬ SSGRoute.IsRamifiedIn k L v)
    (hiner : ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k v σ → a σ = 0)
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hb₀h : ∀ g h : ↥L ≃ₐ[k] ↥L,
      b₀ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • b₀ h + b₀ g) :
    SSGRoute.PTExt.extLoc (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L v hv))
        (SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k (↥K) (↥L))
          (Work.SSGRoute.idleRepMap k (↥K) (↥L))
          (SSGRoute.PTExt.extToIdeles (k := k)
            (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a))
          (Work.SSGRoute.PT.G1plusOwn.hClass p k Ω K T M (L := L) b₀ hb₀h)) = 0 := by
  rw [hClass_eq_levelClassOf]
  refine Work.SSGRoute.PT.G1plusOwn.extLoc_levelPair_galRes_eq_zero_of_unramified p k Ω K T M L
    hKL b₀ hb₀h
    (SSGRoute.PTExt.extToIdeles (k := k) (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a))
    (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v hv))
    (Work.SSGRoute.PT.finQW L v hv) (Work.SSGRoute.PT.G1plusOwn.finHWg hKL v hv) ?_ ?_
  · intro σ hσ
    exact Work.SSGRoute.PT.G1plusOwn.isInertiaAt_eq_one_of_inertiaSub_le k Ω v hv L
      (inertiaSub_le_of_not_isRamifiedIn k Ω v hramLv) σ hσ
  · rw [show SSGRoute.PTExt.extLoc (k := k) (K := ↥K)
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K v hv))
          (SSGRoute.PTExt.extToIdeles (k := k)
            (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a))
        = Work.SSGRoute.PT.finZB p K ζ hζ hζK T hT M v hv a from
      Work.SSGRoute.PT.G1plusOwn.finZB_square p K ζ hζ hζK T hT M v hv a ha1 ha2]
    exact Work.SSGRoute.PT.finZB_unramified p k Ω K ζ hζ hζK T hT M v hv hpv hramKv a
      (isCocycleOn_of_le (act := SSGRoute.res k K) (H := SSGRoute.decomp k v) (H' := ⊤)
        le_top (f := a) ha1)
      (isLocConstOn_of_le (Γ := Ω ≃ₐ[k] Ω) (G := ↥K ≃ₐ[k] ↥K) (M' := M)
        (H := SSGRoute.decomp k v) (H' := ⊤) le_top (f := a) ha2)
      hiner

/-- **The off-`S'` infinite-place vanishing.**  At an infinite place the decomposition group has
order `1` or `2` and the coefficients have odd exponent `p`, so the restriction of the level class
is `0` (`extHRestrict_infinite_eq_zero`) and hence so is the (linear) pairing. -/
theorem extLoc_infinite_eq_zero (hp : p ≠ 2) (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    {L : IntermediateField k Ω} [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hb₀h : ∀ g h : ↥L ≃ₐ[k] ↥L,
      b₀ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • b₀ h + b₀ g)
    (v : NumberField.InfinitePlace ↥L)
    (u : NK.GlobalCFT.Place ↥K)
    (hw : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite v) u) :
    SSGRoute.PTExt.extLoc (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofInfinite v)
        (SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k (↥K) (↥L))
          (Work.SSGRoute.idleRepMap k (↥K) (↥L))
          (SSGRoute.PTExt.extToIdeles (k := k)
            (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a))
          (Work.SSGRoute.PT.G1plusOwn.hClass p k Ω K T M (L := L) b₀ hb₀h)) = 0 := by
  rw [hClass_eq_levelClassOf]
  rw [← Work.SSGRoute.levelPair_extLoc_eq_push (k := k) (K := ↥K) (L := ↥L)
    (SSGRoute.PTExt.extToIdeles (k := k) (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a))
    (Work.SSGRoute.PT.levelClassOf (p := p) (k := k) (Ω := Ω) (K := K) (L := L)
      (T := T) (M := M) b₀ hb₀h) u (NK.GlobalCFT.Place.ofInfinite v) hw]
  rw [Work.SSGRoute.PT.G1plusOwn.extHRestrict_infinite_eq_zero (p := p) (hp := hp) (K := K)
    (L := L) (hKL := hKL) (M := M) (T := T) (v := v)
    (Work.SSGRoute.PT.levelClassOf (p := p) (k := k) (Ω := Ω) (K := K) (L := L)
      (T := T) (M := M) b₀ hb₀h)]
  exact Work.SSGRoute.levelPair_zero_h _ _ _

/-- **`extToClasses Y = 0`** for the global class `Y` of a localisation of the global dictionary
(`extToClasses ∘ extToIdeles = 0` for a global *dictionary* class). -/
theorem extToClasses_idleRepMap_levelPair_eq_zero (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    {L : IntermediateField k Ω} [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hb₀h : ∀ g h : ↥L ≃ₐ[k] ↥L,
      b₀ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • b₀ h + b₀ g) :
    SSGRoute.PTExt.extToClasses (k := k)
      (SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k (↥K) (↥L))
        (Work.SSGRoute.idleRepMap k (↥K) (↥L))
        (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a))
        (Work.SSGRoute.PT.G1plusOwn.hClass p k Ω K T M (L := L) b₀ hb₀h)) = 0 := by
  rw [SSGRoute.PTExt.extToClasses]
  rw [← Work.SSGRoute.phiAt_extToClasses_eq_idleRepMap k (↥K) (↥L)
    (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)))
    (SSGRoute.PTExt.extToIdeles (k := k) (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a))
    (Work.SSGRoute.PT.G1plusOwn.hClass p k Ω K T M (L := L) b₀ hb₀h)]
  rw [SSGRoute.PTExt.extToClasses_extToIdeles]
  exact Work.SSGRoute.levelPair_zero _ _ _

/-- **`p • Y = 0`** for the global class `Y` of a localisation of the global dictionary (the
coefficient module `M^∨ ⊗ T` has exponent `p`). -/
theorem nsmul_idleRepMap_levelPair_eq_zero (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    {L : IntermediateField k Ω} [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hb₀h : ∀ g h : ↥L ≃ₐ[k] ↥L,
      b₀ (g * h) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • b₀ h + b₀ g) :
    p • SSGRoute.PTExt.levelPair (SSGRoute.PTExt.galRes k (↥K) (↥L))
        (Work.SSGRoute.idleRepMap k (↥K) (↥L))
        (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a))
        (Work.SSGRoute.PT.G1plusOwn.hClass p k Ω K T M (L := L) b₀ hb₀h) = 0 := by
  have hExp : ∀ x : Work.SSGRoute.DualMod p (M ⊗[ZMod p] T), p • x = 0 :=
    fun x => Work.SSGRoute.PT.nsmul_eq_zero_of_zmod' p x
  have hX : p • SSGRoute.PTExt.extToIdeles (k := k)
      (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a) = 0 := by
    have h1 : p • Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a = 0 :=
      Work.SSGRoute.E6Util.ext_nsmul_p_torsion_left p hExp _
    rw [← Work.SSGRoute.PT.extToIdeles_nsmul p
        (Work.SSGRoute.PT.finZBg p K ζ hζ hζK T hT M a), h1,
      SSGRoute.PTExt.extToIdeles_zero]
  rw [Work.SSGRoute.PT.pt_levelPair_nsmul_fst, hX, Work.SSGRoute.levelPair_zero]

end

end Work.SSGRoute.PT.G1plusOwn

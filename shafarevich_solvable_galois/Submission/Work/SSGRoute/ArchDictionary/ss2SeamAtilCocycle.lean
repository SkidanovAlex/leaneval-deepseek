import Mathlib
import Submission.Work.SSGRoute.ArchDictionary.archSeamDefs
import Submission.Work.SSGRoute.ArchDictionary.archSeamDefs2
import Submission.Work.SSGRoute.ArchDictionary.ArchLocalP2Aux
import Submission.Work.SSGRoute.ArchDictionary.p2Link
import Submission.Work.SSGRoute.ArchDictionary.archPhiP2
import Submission.Work.SSGRoute.PT.PhiEgen_compat
import Submission.Work.SSGRoute.ArchNat.decompKSeamPair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory CategoryTheory.Limits SSGRoute.PTExt Work.SSGRoute.ArchDictionary
  Work.SSGRoute.ArchDictionary.ArchSeamP2

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 3200000

/-! ## The seam cocycle identity `ss2SeamAtilCocycle`

The statement is the pointwise identity expressing that the `D_w`-cochain
`g ↦ Ψ (b (g~)) ∘ coverMap_{D_w}` (the local evaluation of the global coefficient cocycle
`Ψ ∘ b`, restricted to the decomposition group through `ePowLift.symm`) is the coboundary of the
`0`-cochain `atil = seamUnitsCan ∘ ñ ∘ Φ.τ₂` on the canonical cover of `E'|_{D_w}`.

The mathematical content, in the order in which the proof uses it:

* `ss2CoeffNat_val_mul_self` — every value of `e1aCoeffNat` on the `2`-torsion module
  `E' = DualMod 2 (E ⊗ T)` is `±1`; hence the (choice-dependent) seam `seamUnits` used inside
  `seamCoeffLoc` agrees with the canonical seam `seamUnitsCan` on all those values
  (`seamUnitsCan_eq_seamUnits_of_mul_self`), so
  * `ss2SeamCoeffLoc_apply_val_can` — `seamCoeffLoc` can be evaluated with the canonical seam;
* `ss2SeamUnitsCan_localUnits_apply` — the equivariance of the canonical seam
  (`seamUnitsCan_equivariant`), i.e. the local action of `g ∈ D_w` on `K_wˣ` corresponds, through
  the seam, to the action of the lift `σ₀ ∈ ⟨c⟩` of `g` on `Ωˣ` (here `⟨c⟩ = {1, c}`, the only
  place where `mem_zpowers_eq_one_or_eq` enters);
* the hypothesis `hñ` identifies `e1aCoeffNat (b σ)` with the coboundary `d⁰ ñ` on the cover,
  and `freeCoverCompat_comp` (`Φ.τ₂ = freeCoverCompat D.subtype E'`) identifies the two cover
  maps, so the left hand side becomes `seamUnitsCan (σ • x₁ - x₀)`.

The final step is the additivity of `seamUnitsCan` on the difference of the two `Ωˣ`-values. -/

/-- Every value of the global coefficient map `e1aCoeffNat` on the (`2`-)torsion module
`E' = DualMod 2 (E ⊗ T)` is `±1`, i.e. `2`-torsion in `Ωˣ`. -/
theorem ss2CoeffNat_val_mul_self {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K]
    (T : Type) [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hζ : IsPrimitiveRoot (-1 : Ω) 2) (hζK : (-1 : Ω) ∈ K)
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) (-1 : Ω))
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    (e : E) (v : (Eprime 2 k Ω K T E).V) :
    let u : Ωˣ := Additive.toMul
      ((Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E e) v)
    u * u = 1 := by
  intro u
  have hvv : v + v = 0 := by
    have hf : ∀ f : Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T), f + f = 0 := by
      intro f
      rw [← two_nsmul, ← Nat.cast_smul_eq_nsmul (R := ZMod 2) 2 f,
        show ((2:ℕ):ZMod 2) = 0 from ZMod.natCast_self 2, zero_smul]
    exact hf v
  have hx : Additive.ofMul u + Additive.ofMul u = 0 := by
    show (Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E e) v
      + (Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E e) v = 0
    rw [← map_add, hvv, map_zero]
  have h3 : Additive.ofMul (u * u) = 0 := by
    rw [show Additive.ofMul (u*u) = Additive.ofMul u + Additive.ofMul u from by simp]
    exact hx
  exact Additive.ofMul.injective (by simpa using h3)

/-- Value rule of the local coefficient identification `seamCoeffLoc`. -/
theorem ss2SeamCoeffLoc_apply_val {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K]
    (T : Type) [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hζ : IsPrimitiveRoot (-1 : Ω) 2) (hζK : (-1 : Ω) ∈ K)
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) (-1 : Ω))
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hne : decompK (k := k) w ≠ ⊥)
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    (e : E) (v : (Eprime 2 k Ω K T E).V) :
    (seamCoeffLoc T hζ hζK hT c hc2 hc1 φ hlink w hw hne E e) v
      = Additive.ofMul (seamUnits c hc2 hc1 φ hlink w hw hne
          (Additive.toMul ((Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E e) v))) :=
  rfl

/-- Value rule of `seamCoeffLoc` with the canonical seam, using that every value of
`e1aCoeffNat` is `2`-torsion (so the two seams agree there). -/
theorem ss2SeamCoeffLoc_apply_val_can {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K]
    (T : Type) [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hζ : IsPrimitiveRoot (-1 : Ω) 2) (hζK : (-1 : Ω) ∈ K)
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) (-1 : Ω))
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥)
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    (e : E) (v : (Eprime 2 k Ω K T E).V) :
    (seamCoeffLoc T hζ hζK hT c hc2 hc1 φ hlink (seamPlace (K := K) φ) rfl hne E e) v
      = (MonoidHom.toAdditive (ArchSeamP2b.seamUnitsCan (K := K) φ hne))
          ((Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E e) v) := by
  let u : Ωˣ := Additive.toMul
      ((Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E e) v)
  have hu : u * u = 1 := ss2CoeffNat_val_mul_self T hζ hζK hT E e v
  rw [ss2SeamCoeffLoc_apply_val]
  change Additive.ofMul (seamUnits c hc2 hc1 φ hlink (seamPlace (K := K) φ) rfl hne u)
      = Additive.ofMul (ArchSeamP2b.seamUnitsCan (K := K) φ hne u)
  rw [ArchSeamP2b.seamUnitsCan_eq_seamUnits_of_mul_self c hc2 hc1 φ hlink hne u hu]

/-- **Equivariance of the canonical seam in the form needed for the cocycle identity**: the local
action of `g` on `K_wˣ` corresponds to the `σ₀`-action on `Ωˣ` (`σ₀` the lift of `g` through `c`). -/
theorem ss2SeamUnitsCan_localUnits_apply {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] [NumberField ↥K]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥)
    (g : ↥(decompK (k := k) (seamPlace (K := K) φ)))
    (σ₀ : ↥(Subgroup.zpowers c))
    (hσ₀ : ((σ₀ : Ω ≃ₐ[k] Ω) = 1) ∨ ((σ₀ : Ω ≃ₐ[k] Ω) = c))
    (hres : SSGRoute.res k K (σ₀ : Ω ≃ₐ[k] Ω) = (g : ↥K ≃ₐ[k] ↥K))
    (x : Additive Ωˣ) :
    (localUnitsK (k := k) (seamPlace (K := K) φ)).ρ g
        ((MonoidHom.toAdditive (ArchSeamP2b.seamUnitsCan (K := K) φ hne)) x)
      = (MonoidHom.toAdditive (ArchSeamP2b.seamUnitsCan (K := K) φ hne))
          ((σ₀ : Ω ≃ₐ[k] Ω) • x) := by
  rcases hσ₀ with h1 | hc
  · have hg : g = 1 := by
      apply Subtype.ext
      rw [← hres, show ((σ₀ : Ω ≃ₐ[k] Ω)) = 1 from h1, map_one]
      rfl
    subst hg
    rw [show ((σ₀ : Ω ≃ₐ[k] Ω)) = 1 from h1]
    rw [show (localUnitsK (k := k) (seamPlace (K := K) φ)).ρ
          (1 : ↥(decompK (k := k) (seamPlace (K := K) φ))) = LinearMap.id from by ext y; simp]
    rfl
  · have hg : (g : ↥K ≃ₐ[k] ↥K) = SSGRoute.res k K c := by
      rw [← hres, show ((σ₀ : Ω ≃ₐ[k] Ω)) = c from hc]
    rw [show ((σ₀ : Ω ≃ₐ[k] Ω)) = c from hc]
    apply Additive.toMul.injective
    show NK.HassePrinciple.localUnitsEquiv (K := k) (L := ↥K) (seamPlace (K := K) φ) g
          (ArchSeamP2b.seamUnitsCan (K := K) φ hne (Additive.toMul x))
        = ArchSeamP2b.seamUnitsCan (K := K) φ hne (Additive.toMul (c • x))
    rw [show Additive.toMul (c • x)
        = Work.SSGRoute.algEquivUnitsMapΩ k Ω c (Additive.toMul x) from rfl]
    rw [← ArchSeamP2b.seamUnitsCan_equivariant c φ hlink hne g hg (Additive.toMul x)]

theorem ss2SeamAtilCocycle {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K]
    (T : Type) [AddCommGroup T] [Module (ZMod 2) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) T]
    (hζ : IsPrimitiveRoot (-1 : Ω) 2) (hζK : (-1 : Ω) ∈ K)
    (hT : SSGRoute.IsCyclotomicDual 2 (T := T) (SSGRoute.res k K) (-1 : Ω))
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hne : decompK (k := k) (seamPlace (K := K) φ) ≠ ⊥)
    (E : Type) [AddCommGroup E] [Module (ZMod 2) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod 2) E] [Finite E]
    (Ψ : E ≃+ ((Eprime 2 k Ω K T E).V →ₗ[Coeff]
      (localUnitsK (k := k) (seamPlace (K := K) φ)).V))
    (hΨv : ∀ e, Ψ e = seamCoeffLoc T hζ hζK hT c hc2 hc1 φ hlink
      (seamPlace (K := K) φ) rfl hne E e)
    (b : (Ω ≃ₐ[k] Ω) → E) (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b)
    (Φ : CategoryTheory.ShortComplex.Hom
      (Work.SSGRoute.freeCoverSES
        (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)))
      ((Work.SSGRoute.freeCoverSES (Eprime 2 k Ω K T E)).map
        (Rep.resFunctor (k := SSGRoute.PTExt.Coeff)
          (decompK (k := k) (seamPlace (K := K) φ)).subtype)))
    (hΦ₂ : Φ.τ₂ = Work.SSGRoute.PT.freeCoverCompat
      (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E))
    (hΦ₃ : Φ.τ₃ = CategoryTheory.CategoryStruct.id
      (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype (Eprime 2 k Ω K T E)))
    (ñ : Work.SSGRoute.ExtChain.E1cGeneric.E1cN (Eprime 2 k Ω K T E))
    (hñ : ∀ σ : Ω ≃ₐ[k] Ω,
      Work.SSGRoute.ExtChain.E1cGeneric.iotaH (Eprime 2 k Ω K T E)
          (Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E (b σ))
        = Work.GroupCohomology.d0 (Ω ≃ₐ[k] Ω)
            (Work.SSGRoute.ExtChain.E1cGeneric.E1cN (Eprime 2 k Ω K T E)) ñ σ) :
    ∀ (g : ↥(decompK (k := k) (seamPlace (K := K) φ)))
      (f : (Rep.free SSGRoute.PTExt.Coeff
        ↥(decompK (k := k) (seamPlace (K := K) φ))
        (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype
          (Eprime 2 k Ω K T E)).V).V),
      let atil : (Rep.free SSGRoute.PTExt.Coeff
        ↥(decompK (k := k) (seamPlace (K := K) φ))
        (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype
          (Eprime 2 k Ω K T E)).V).V →+
          (localUnitsK (k := k) (seamPlace (K := K) φ)).V :=
        (MonoidHom.toAdditive (ArchSeamP2b.seamUnitsCan (K := K) φ hne)).comp
          (ñ.comp ((Rep.Hom.hom Φ.τ₂).toAddMonoidHom))
      Ψ (b (((ePowLift (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink
              (seamPlace (K := K) φ) rfl hne).symm g : ↥(Subgroup.zpowers c)) : Ω ≃ₐ[k] Ω))
          (Rep.Hom.hom
            (Work.SSGRoute.freeCover
              (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype
                (Eprime 2 k Ω K T E))) f)
        = (localUnitsK (k := k) (seamPlace (K := K) φ)).ρ g
            (atil (((Rep.free SSGRoute.PTExt.Coeff
                ↥(decompK (k := k) (seamPlace (K := K) φ))
                (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype
                  (Eprime 2 k Ω K T E)).V).ρ g⁻¹) f))
          - atil f := by
  intro g f
  dsimp only
  haveI hFintG : Fintype (K ≃ₐ[k] K) := Fintype.ofFinite _
  haveI hFintD : Fintype ↥(decompK (k := k) (seamPlace (K := K) φ)) := Fintype.ofFinite _
  let X : Rep.{0} Coeff (K ≃ₐ[k] K) := Eprime 2 k Ω K T E
  let EP : ↥(Subgroup.zpowers c) ≃* ↥(decompK (k := k) (seamPlace (K := K) φ)) :=
    ePowLift (k := k) (Ω := Ω) (K := K) c hc2 hc1 φ hlink (seamPlace (K := K) φ) rfl hne
  let σ₀ : ↥(Subgroup.zpowers c) := EP.symm g
  let σ : Ω ≃ₐ[k] Ω := (σ₀ : Ω ≃ₐ[k] Ω)
  have hres : SSGRoute.res k K σ = (g : ↥K ≃ₐ[k] ↥K) :=
    congrArg Subtype.val (EP.apply_symm_apply g)
  have hτ₂ : (Rep.Hom.hom Φ.τ₂).toAddMonoidHom
      = (Rep.Hom.hom (Work.SSGRoute.PT.freeCoverCompat
          (decompK (k := k) (seamPlace (K := K) φ)).subtype
          (Eprime 2 k Ω K T E))).toAddMonoidHom := by
    rw [hΦ₂]
    try rfl
  rw [hτ₂]
  let FD : Rep.{0} Coeff ↥(decompK (k := k) (seamPlace (K := K) φ)) :=
    Rep.free Coeff ↥(decompK (k := k) (seamPlace (K := K) φ))
      (Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype X).V
  let FX : Rep.{0} Coeff (K ≃ₐ[k] K) := Rep.free Coeff (K ≃ₐ[k] K) X.V
  let fcc : FD ⟶ Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype FX :=
    Work.SSGRoute.PT.freeCoverCompat (decompK (k := k) (seamPlace (K := K) φ)).subtype X
  let τ₂m : FD.V →+ FX.V := (Rep.Hom.hom fcc).toAddMonoidHom
  let atil : FD.V →+ (localUnitsK (k := k) (seamPlace (K := K) φ)).V :=
    (MonoidHom.toAdditive (ArchSeamP2b.seamUnitsCan (K := K) φ hne)).comp (ñ.comp τ₂m)
  let x₁ : Additive Ωˣ := ñ (τ₂m (FD.ρ g⁻¹ f))
  let x₀ : Additive Ωˣ := ñ (τ₂m f)
  change Ψ (b σ) ((Rep.Hom.hom (Work.SSGRoute.freeCover (Rep.res
      (decompK (k := k) (seamPlace (K := K) φ)).subtype X))) f)
      = (localUnitsK (k := k) (seamPlace (K := K) φ)).ρ g (atil (FD.ρ g⁻¹ f)) - atil f
  have hL : Ψ (b σ) ((Rep.Hom.hom (Work.SSGRoute.freeCover (Rep.res
        (decompK (k := k) (seamPlace (K := K) φ)).subtype X))) f)
      = (MonoidHom.toAdditive (ArchSeamP2b.seamUnitsCan (K := K) φ hne)) (σ • x₁ - x₀) := by
    have hv : (Rep.Hom.hom (Work.SSGRoute.freeCover (Rep.res
          (decompK (k := k) (seamPlace (K := K) φ)).subtype X))) f
        = (Work.SSGRoute.ExtChain.E1cGeneric.coverMap X) (τ₂m f) := by
      show (Rep.Hom.hom (Work.SSGRoute.freeCover (Rep.res
          (decompK (k := k) (seamPlace (K := K) φ)).subtype X))) f
        = (Rep.Hom.hom (Work.SSGRoute.freeCover X)) ((Rep.Hom.hom fcc) f)
      rw [← Work.SSGRoute.PT.freeCoverCompat_comp
          (decompK (k := k) (seamPlace (K := K) φ)).subtype X, Rep.comp_apply]
      rfl
    have hkey : ((Work.SSGRoute.ExtChain.e1aCoeffNat 2 k Ω K (-1) hζ hζK T hT E) (b σ))
          ((Rep.Hom.hom (Work.SSGRoute.freeCover (Rep.res
            (decompK (k := k) (seamPlace (K := K) φ)).subtype X))) f)
        = Work.SSGRoute.ExtChain.E1cGeneric.cnj X σ ñ (τ₂m f) - ñ (τ₂m f) := by
      have h := DFunLike.congr_fun (hñ σ) (τ₂m f)
      rw [Work.SSGRoute.ExtChain.E1cGeneric.iotaH_apply,
        Work.SSGRoute.ExtChain.E1cGeneric.d0_cnj] at h
      erw [AddMonoidHom.comp_apply, AddMonoidHom.sub_apply] at h
      rw [← hv] at h
      exact h
    have hcnj : Work.SSGRoute.ExtChain.E1cGeneric.cnj X σ ñ (τ₂m f) = σ • x₁ := by
      show (Work.SSGRoute.homCoind.smulHom (k := k) (Ω := Ω) σ)
          (ñ (((Work.SSGRoute.ExtChain.E1cGeneric.E1cF X).ρ
            ((SSGRoute.res k K σ)⁻¹)) (τ₂m f)))
        = σ • x₁
      have harg : ((Work.SSGRoute.ExtChain.E1cGeneric.E1cF X).ρ
            ((SSGRoute.res k K σ)⁻¹)) (τ₂m f) = τ₂m (FD.ρ g⁻¹ f) := by
        rw [show (SSGRoute.res k K σ)⁻¹ = ((g : ↥K ≃ₐ[k] ↥K))⁻¹ from by rw [hres]]
        show ((Rep.res (decompK (k := k) (seamPlace (K := K) φ)).subtype FX).ρ g⁻¹)
            ((Rep.Hom.hom fcc) f) = (Rep.Hom.hom fcc) ((FD.ρ g⁻¹) f)
        exact (LinearMap.congr_fun ((Rep.Hom.hom fcc).isIntertwining' g⁻¹) f).symm
      rw [harg]
      rfl
    rw [DFunLike.congr_fun (hΨv (b σ))
      ((Rep.Hom.hom (Work.SSGRoute.freeCover (Rep.res
        (decompK (k := k) (seamPlace (K := K) φ)).subtype X))) f)]
    rw [ss2SeamCoeffLoc_apply_val_can T hζ hζK hT c hc2 hc1 φ hlink hne E (b σ) _]
    rw [hkey, hcnj]
  have hR : (localUnitsK (k := k) (seamPlace (K := K) φ)).ρ g (atil (FD.ρ g⁻¹ f)) - atil f
      = (MonoidHom.toAdditive (ArchSeamP2b.seamUnitsCan (K := K) φ hne)) (σ • x₁ - x₀) := by
    have hA := ss2SeamUnitsCan_localUnits_apply c hc2 hc1 φ hlink hne g σ₀
        (mem_zpowers_eq_one_or_eq c hc2 σ₀.2) hres x₁
    have e1 : atil (FD.ρ g⁻¹ f)
        = (MonoidHom.toAdditive (ArchSeamP2b.seamUnitsCan (K := K) φ hne)) x₁ := rfl
    have e0 : atil f = (MonoidHom.toAdditive (ArchSeamP2b.seamUnitsCan (K := K) φ hne)) x₀ := rfl
    rw [e1, e0, hA]
    exact (map_sub (MonoidHom.toAdditive (ArchSeamP2b.seamUnitsCan (K := K) φ hne))
      (σ₀ • x₁) x₀).symm
  rw [hL, hR]

#print axioms Work.SSGRoute.ArchDictionary.ss2SeamAtilCocycle
#print axioms Work.SSGRoute.ArchDictionary.ss2CoeffNat_val_mul_self
#print axioms Work.SSGRoute.ArchDictionary.ss2SeamCoeffLoc_apply_val_can
#print axioms Work.SSGRoute.ArchDictionary.ss2SeamUnitsCan_localUnits_apply

end Work.SSGRoute.ArchDictionary

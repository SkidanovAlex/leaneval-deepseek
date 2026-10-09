import Mathlib
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.Work.SSGRoute.PT.e1a_can_aux
import Submission.Work.AbsoluteKummer.Functoriality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END


/-!
# Naturality of `e1aCoeffH2` in the coefficient `E`

`Work.SSGRoute.ExtChain.e1aCoeffH2` is the map `H²(Γ, Hom_ℤ(E',Ωˣ)) →+ H²(Γ,E)` obtained by
applying `mapH2` to the inverse of the chosen coefficient identification
`e1aCoeffNat : E ≃+ Hom_ℤ(E',Ωˣ)`, where `E' = DualMod p (E ⊗ T)` and `Γ = Gal(Ω/k)`
(`Work.SSGRoute.ExtChain.ChainGamma`).

The identification is a member of the *natural* family of
`Work.SSGRoute.PT.e1a_coeff_iso_natural`: for an equivariant `f : E₁ → E₂` with transpose
`F : (E₂)' ⟶ (E₁)'` one has

`Ψ_{E₂} (f e) = (Ψ_{E₁} e).comp F.hom.toAddMonoidHom`   (`e1aCoeffNat_natural_aux`),

and hence, in inverse form,

`Ψ_{E₂}⁻¹ (n.comp F.hom) = f (Ψ_{E₁}⁻¹ n)`   (`e1aCoeffNat_symm_natural_aux`).

The main theorem `e1aCoeffH2_natural` is the resulting `H²`-level naturality square, which is the
coefficient square of the naturality of the chain `e1aChain` of `ChainGamma`.
-/

namespace Work.SSGRoute.ExtChain

set_option maxHeartbeats 10000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

/-- **Naturality of the chosen coefficient identification.**  The chosen member `e1aCoeffNat` of
the natural family `Work.SSGRoute.PT.e1a_coeff_iso_natural` is natural in the coefficient: for an
equivariant `f : E₁ → E₂` whose transpose is `F`,
`Ψ_{E₂} (f e) = (Ψ_{E₁} e).comp F.hom.toAddMonoidHom`. -/
theorem e1aCoeffNat_natural_aux (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
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
    (e : E₁) :
    Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E₂ (f e)
      = (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E₁ e).comp
          (Rep.Hom.hom F).toAddMonoidHom :=
  (Classical.choose_spec
      (Work.SSGRoute.PT.e1a_coeff_iso_natural p k Ω K ζ hζ hζK T hT)).2
    (E₁ := E₁) (E₂ := E₂) (f := f) (hf := hf) (F := F) (hF := hF) (e := e)

/-- **Naturality of the inverse of the chosen coefficient identification.**  For
`n : Hom_ℤ((E₁)',Ωˣ)`, `Ψ_{E₂}⁻¹ (n.comp F.hom) = f (Ψ_{E₁}⁻¹ n)`. -/
theorem e1aCoeffNat_symm_natural_aux (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
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
    (n : Work.SSGRoute.homCoind k Ω K
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T)))) :
    (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E₂).symm
        (Work.SSGRoute.precompAddHom (Rep.Hom.hom F).toAddMonoidHom n)
      = f ((Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E₁).symm n) := by
  apply (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E₂).injective
  rw [AddEquiv.apply_symm_apply]
  rw [e1aCoeffNat_natural_aux p k Ω K ζ hζ hζK T hT E₁ E₂ f hf F hF
    ((Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E₁).symm n)]
  rw [AddEquiv.apply_symm_apply]
  rfl

/-- The quotient map `H2π` of the continuous second cohomology is surjective. -/
theorem h2π_surjective_aux {G : Type*} [TopologicalSpace G] [Group G] {M : Type*}
    [AddCommGroup M] [DistribMulAction G M] :
    Function.Surjective (Work.AbsoluteKummer.H2π G M) := by
  intro x
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G M).comap (Work.AbsoluteKummer.Z2 G M).subtype) x
  exact ⟨c, hc⟩

theorem e1aCoeffH2_natural (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
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
    (hg : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom F).toAddMonoidHom))
    (y : Work.AbsoluteKummer.H2 (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.homCoind k Ω K
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T))))) :
    Work.SSGRoute.ExtChain.e1aCoeffH2 p k Ω K ζ hζ hζK T hT E₂
        (Work.AbsoluteKummer.mapH2
          (Work.SSGRoute.precompAddHom (Rep.Hom.hom F).toAddMonoidHom) hg y)
      = Work.SSGRoute.PT.e1aH2Map p k Ω K E₁ E₂ f hf
          (Work.SSGRoute.ExtChain.e1aCoeffH2 p k Ω K ζ hζ hζK T hT E₁ y) := by
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E₁ := DistribMulAction.compHom E₁ (SSGRoute.res k K)
  letI : DistribMulAction (Ω ≃ₐ[k] Ω) E₂ := DistribMulAction.compHom E₂ (SSGRoute.res k K)
  -- The two definitional unfoldings of the packaged maps.
  have hL : Work.SSGRoute.ExtChain.e1aCoeffH2 p k Ω K ζ hζ hζK T hT E₂
        (Work.AbsoluteKummer.mapH2
          (Work.SSGRoute.precompAddHom (Rep.Hom.hom F).toAddMonoidHom) hg y)
      = Work.AbsoluteKummer.mapH2
          ((Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E₂).symm.toAddMonoidHom)
          (fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant
            p k Ω K ζ hζ hζK T hT E₂ σ n)
          (Work.AbsoluteKummer.mapH2
            (Work.SSGRoute.precompAddHom (Rep.Hom.hom F).toAddMonoidHom) hg y) := rfl
  have hR : Work.SSGRoute.PT.e1aH2Map p k Ω K E₁ E₂ f hf
        (Work.SSGRoute.ExtChain.e1aCoeffH2 p k Ω K ζ hζ hζK T hT E₁ y)
      = Work.AbsoluteKummer.mapH2 f.toAddMonoidHom
          (fun σ m => hf (SSGRoute.res k K σ) m)
          (Work.AbsoluteKummer.mapH2
            ((Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E₁).symm.toAddMonoidHom)
            (fun σ n => Work.SSGRoute.ExtChain.e1aCoeffNat_symm_equivariant
              p k Ω K ζ hζ hζK T hT E₁ σ n)
            y) := rfl
  rw [hL, hR]
  -- Compare the two maps on classes of continuous `2`-cocycles.
  obtain ⟨c, hc⟩ := h2π_surjective_aux (G := Ω ≃ₐ[k] Ω)
    (M := Work.SSGRoute.homCoind k Ω K
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T)))) y
  rw [← hc]
  first
    | simp only [Work.AbsoluteKummer.mapH2_H2π]
    | rw [Work.AbsoluteKummer.mapH2_H2π, Work.AbsoluteKummer.mapH2_H2π,
          Work.AbsoluteKummer.mapH2_H2π, Work.AbsoluteKummer.mapH2_H2π]
    | rw [Work.AbsoluteKummer.mapH2_H2π, Work.AbsoluteKummer.mapH2_H2π]
  refine congrArg (fun z : Work.AbsoluteKummer.Z2 (Ω ≃ₐ[k] Ω) E₂ =>
    Work.AbsoluteKummer.H2π (Ω ≃ₐ[k] Ω) E₂ z) ?_
  apply Subtype.ext
  funext q
  try simp only [Work.AbsoluteKummer.mapZ2_apply]
  exact e1aCoeffNat_symm_natural_aux p k Ω K ζ hζ hζK T hT E₁ E₂ f hf F hF
    ((c : (Ω ≃ₐ[k] Ω) × (Ω ≃ₐ[k] Ω) → Work.SSGRoute.homCoind k Ω K
      (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₁ T)))) q)

end

end Work.SSGRoute.ExtChain

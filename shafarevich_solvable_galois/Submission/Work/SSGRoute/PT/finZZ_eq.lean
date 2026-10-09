import Mathlib
import Submission.Work.SSGRoute.PT.finHalfData
import Submission.Work.SSGRoute.PT.finZH_levelChange
import Submission.Work.SSGRoute.extHMap_gammaHom_eq
import Submission.Work.SSGRoute.gammaHom_natural_coeff
import Submission.Work.SSGRoute.levelPair_comp_extHMap
import Submission.Work.SSGRoute.levelPair_baseChange_key
import Submission.Work.SSGRoute.baseChangeDefs

namespace Work.SSGRoute.PT

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct
open SSGRoute.PTExt CategoryTheory

section RepAux

variable {G H : Type} [Group G] [Group H]

/-- `Rep.resMap` acts on carriers by the underlying map (coercion form). -/
lemma resMap_hom_apply_coe {X Y : Rep.{0} Coeff G} (f : H →* G) (p : X ⟶ Y) (x : X.V) :
    (Rep.Hom.hom (Rep.resMap f p)) x = (Rep.Hom.hom p) x := rfl

/-- The transport `eqToHom` between two restrictions of the same representation is the identity on
carriers. -/
lemma eqToHom_res_hom_self (f₁ f₂ : H →* G) (X : Rep.{0} Coeff G)
    (h : Rep.res f₁ X = Rep.res f₂ X) (x : (Rep.res f₁ X).V) :
    (Rep.Hom.hom (eqToHom h)) x = x := by
  rw [Work.SSGRoute.Y3Test.eqToHom_hom_eq_self h x rfl (Subsingleton.elim _ _)]

/-- v4.35 port helper: a morphism out of `Rep.res f₁ X` equals `eqToHom h ≫ g ≫ k` as soon as they
agree pointwise (proved once generically, so the `eqToHom`/`IntertwiningMap` unfolding is cheap). -/
lemma eq_eqToHom_comp2_of_apply (f₁ f₂ : H →* G) (X : Rep.{0} Coeff G)
    (h : Rep.res f₁ X = Rep.res f₂ X) {Z W : Rep.{0} Coeff H} (g : Rep.res f₂ X ⟶ Z) (k : Z ⟶ W)
    (φ : Rep.res f₁ X ⟶ W)
    (hφ : ∀ x : X.V, (Rep.Hom.hom φ) x = (Rep.Hom.hom k) ((Rep.Hom.hom g) x)) :
    φ = eqToHom h ≫ g ≫ k := by
  apply Rep.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  change (Rep.Hom.hom φ) x = (Rep.Hom.hom k) ((Rep.Hom.hom g) ((Rep.Hom.hom (eqToHom h)) x))
  rw [eqToHom_res_hom_self]
  exact hφ x

end RepAux

section FinZIAux

variable {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K L L' : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
  [NumberField L] [FiniteDimensional k L] [IsGalois k L]
  [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
  (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
  [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
  [Algebra ↥K ↥L'] [IsScalarTower k ↥K ↥L'] [IsScalarTower ↥K ↥L' Ω]
  [Algebra ↥L ↥L'] [IsScalarTower k ↥L ↥L'] [IsScalarTower ↥L ↥L' Ω]
  [IsScalarTower ↥K ↥L ↥L']
  (hKL : K ≤ L) (hKL' : K ≤ L') (hLL : L ≤ L')

/-- **(H1)** The comparison of the local-units maps at two levels, in the transported form needed
by `levelPair_transport'`: `finZI` at the upper level equals the composite of `finZI` at the lower
level with the intermediate map `finMU`, after transporting along the place-glue comparison `hZF`.
The content is the pointwise identity `finZI_apply`. -/
theorem finZI_eq_of_hZF
    (hw' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L A hA)))
    (hZF : finZF hKL' A hA = (finZF hKL A hA).comp
      (decompKRestrict k (↥L) (↥L') (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
        (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw')) :
    finZI hKL' A hA
      = eqToHom (congrArg (fun t => Rep.res t
            (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
              (NK.GlobalCFT.Place.ofFinite (finQ K A hA)))) hZF)
        ≫ (Rep.resMap (decompKRestrict k (↥L) (↥L')
              (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
              (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw')
            (finZI hKL A hA) ≫ finMU (K := K) A hA hLL) := by
  refine eq_eqToHom_comp2_of_apply _ _ _ _ _ _ _ (fun x => ?_)
  rw [resMap_hom_apply_coe]
  exact finZI_apply (K := K) (L := L) (L' := L') A hA hKL hKL' hLL (Additive.toMul x)

end FinZIAux

theorem finZZ_eq {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K L L' : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    [NumberField L'] [FiniteDimensional k L'] [IsGalois k L']
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    [Algebra ↥K ↥L'] [IsScalarTower k ↥K ↥L'] [IsScalarTower ↥K ↥L' Ω]
    [Algebra ↥L ↥L'] [IsScalarTower k ↥L ↥L'] [IsScalarTower ↥L ↥L' Ω]
    [IsScalarTower ↥K ↥L ↥L']
    (p : ℕ) [Fact p.Prime] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (hKL : K ≤ L) (hKL' : K ≤ L') (hLL : L ≤ L')
    (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (b₀' : (↥L' ≃ₐ[k] ↥L') → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ))
    (hb₀' : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀' (AlgEquiv.restrictNormalHom L' σ)) :
    Work.SSGRoute.PT.finZZ p K ζ hζ hζK T hT M L' hKL' A hA a b hb b₀' hb₀'
      = SSGRoute.PTExt.extHMap
          (SSGRoute.decompKRestrict k (↥L) (↥L')
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L' A hA))
            (NK.GlobalCFT.Place.liesOver_ofFinite (Work.SSGRoute.PT.finQW_liesOver A hA hLL)))
        (Work.SSGRoute.PT.finMU (K := K) A hA hLL)
        (Work.SSGRoute.PT.finZZ p K ζ hζ hζK T hT M L hKL A hA a b hb b₀ hb₀) := by
  have hw' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite (finQW L' A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L A hA)) :=
    NK.GlobalCFT.Place.liesOver_ofFinite (finQW_liesOver A hA hLL)
  let ρ := decompKRestrict k (↥L) (↥L')
      (NK.GlobalCFT.Place.ofFinite (finQW L A hA))
      (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)) hw'
  have hZF : finZF hKL' A hA = (finZF hKL A hA).comp ρ := finZF_eq A hA hKL hKL' hLL
  let A0 : Rep.{0} Coeff ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))) :=
    SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))
  let M0 : Rep.{0} Coeff ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))) :=
    Rep.res (decompK (k := k) (NK.GlobalCFT.Place.ofFinite (finQ K A hA))).subtype
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)))
  simp only [finZZ]
  rw [← Work.SSGRoute.levelPair_comp_extHMap (f₁ := finZF hKL A hA) (g := ρ)
    (ι₀ := finZI hKL A hA) (ι₁ := finMU (K := K) A hA hLL)
    (y := (finZB p K ζ hζ hζK T hT M A hA) a)
    (h := finZH p K T M L hKL A hA b hb b₀ hb₀)]
  refine Work.SSGRoute.Y3Key.levelPair_transport'
    (f₁ := finZF hKL' A hA) (f₂ := (finZF hKL A hA).comp ρ)
    (A := A0) (M := M0)
    (B' := SSGRoute.PTExt.localUnitsK (k := k) (K := ↥L')
      (NK.GlobalCFT.Place.ofFinite (finQW L' A hA)))
    (x := (finZB p K ζ hζ hζK T hT M A hA) a)
    (ρA := eqToHom (congrArg (fun t => Rep.res t A0) hZF))
    (ρM := eqToHom (congrArg (fun t => Rep.res t M0) hZF))
    (σM := eqToHom (congrArg (fun t => Rep.res t M0) hZF.symm))
    (ι₁ := finZI hKL' A hA)
    (ι₂ := Rep.resMap ρ (finZI hKL A hA) ≫ finMU (K := K) A hA hLL)
    (h₁ := finZH p K T M L' hKL' A hA b hb b₀' hb₀')
    (h₂ := extHMap ρ (𝟙 _) (finZH p K T M L hKL A hA b hb b₀ hb₀))
    (hρσM := ?_) (hι := ?_) (hh := ?_) (hx := ?_)
  · rw [CategoryTheory.eqToHom_trans]
    exact CategoryTheory.eqToHom_refl _ _
  · exact finZI_eq_of_hZF A hA hKL hKL' hLL hw' hZF
  · exact Work.SSGRoute.PT.finZH_levelChange A hA p T M hKL hKL' hLL b hb b₀ b₀' hb₀ hb₀' hw' hZF
  · exact Work.SSGRoute.Y3Key.extRes_transport' (A := A0) (M := M0) (r := 1)
      (x := (finZB p K ζ hζ hζK T hT M A hA) a) hZF.symm

end Work.SSGRoute.PT

import Mathlib
import Submission.Work.SSGRoute.PT.g1plus_finHalf
import Submission.Work.SSGRoute.PT.place_glue_level
import Submission.Work.SSGRoute.PT.factorised_isCrossedHom
import Submission.Work.SSGRoute.ExtH1Iso
import Submission.Work.SSGRoute.augSES_shortExact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option linter.unusedVariables false

namespace Work.SSGRoute.PT

/-- **The level class `[b]_L` of the finite-place half of `G1⁺`** (the `hval` of
`Work.SSGRoute.PT.finAtLevel`): given the factorised level-`L` cocycle `b₀` on `decompK w` — a
crossed homomorphism for the `Gal(K/k)`-action pulled back along `galRes ↾ D_w` — its class in
`H¹(D_w, M'(1))`, the second factor of `levelPair`.

The class is `ExtH1.gammaZ1` (the degree-one bridge `H¹ ≅ Ext¹`) applied to the `1`-cocycle
`g ↦ b₀ (g : ↥L ≃ₐ[k] ↥L)`; the `Rep` bookkeeping is *definitional*, because
`Rep.res f (Rep.res (decompK q).subtype (modRep Gal M))` is `modRep ↥(decompK w) M` for the action
pulled back along `(decompK q).subtype.comp f`. -/
noncomputable def levelClass
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (hKL : K ≤ L) [FiniteDimensional k L] [IsGalois k L]
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (f : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) →*
      ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
    (hf : ∀ σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      ((f σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) :
          ↥K ≃ₐ[k] ↥K) = SSGRoute.PTExt.galRes k (↥K) (↥L) (σ : ↥L ≃ₐ[k] ↥L))
    (M T : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hcrossed : ∀ g h : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      b₀ (↑(g * h) : ↥L ≃ₐ[k] ↥L)
        = b₀ (g : ↥L ≃ₐ[k] ↥L) +
          (SSGRoute.PTExt.galRes k (↥K) (↥L) (g : ↥L ≃ₐ[k] ↥L)) •
            b₀ (h : ↥L ≃ₐ[k] ↥L)) :
    extH (Rep.res f
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
        (modRep (↥K ≃ₐ[k] ↥K)
          (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))))) 1 := by
  classical
  -- the action of `D_w = decompK w` on the coefficient, pulled back along the place glue
  let φ₀ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) →*
      (↥K ≃ₐ[k] ↥K) :=
    (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype.comp f
  letI : DistribMulAction ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
      (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) :=
    DistribMulAction.compHom _ φ₀
  -- `b₀` restricted to `D_w` is a `1`-cocycle
  have hmem : (fun g : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) =>
      b₀ (g : ↥L ≃ₐ[k] ↥L)) ∈
      Work.GroupCohomology.Z1 ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
        (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) := by
    rw [Work.GroupCohomology.mem_Z1_iff]
    intro g h
    show b₀ (↑(g * h)) =
      (((f g : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) :
        ↥K ≃ₐ[k] ↥K) • b₀ (h : ↥L ≃ₐ[k] ↥L)) + b₀ (g : ↥L ≃ₐ[k] ↥L)
    rw [hcrossed g h, hf g, add_comm]
  -- the class, via the degree-one bridge `H¹(D_w, M'(1)) ≅ Ext¹_{D_w}(ℤ, M'(1))`
  exact Work.SSGRoute.ExtH1.gammaZ1
    ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
    (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (Work.SSGRoute.augSES_shortExact _) ⟨_, hmem⟩

/-- **The level class `[b]_L` from the factorisation data** (`b`, `hb`, `b₀`, `hb₀` and the place
glue at the level `L`): the crossed-homomorphism property of `b₀|D_w` is
`PT.factorised_isCrossedHom`. -/
noncomputable def levelClass_of_cocycle
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω]
    (K L : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (hKL : K ≤ L) [FiniteDimensional k L] [IsGalois k L]
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K, x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hAw : ∀ y : NumberField.RingOfIntegers L, y ∈ w.asIdeal ↔ A.valuation (((y : L) : Ω)) < 1)
    (hglue : (SSGRoute.decomp k A).map (SSGRoute.res k L) =
      SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w))
    (f : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)) →*
      ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)))
    (hf : ∀ σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w)),
      ((f σ : ↥(SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q))) :
          ↥K ≃ₐ[k] ↥K) = SSGRoute.PTExt.galRes k (↥K) (↥L) (σ : ↥L ≃ₐ[k] ↥L))
    (M T : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (b₀ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)) :
    extH (Rep.res f
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
        (modRep (↥K ≃ₐ[k] ↥K)
          (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))))) 1 :=
  levelClass p k Ω K L hKL q w f hf M T b₀
    (factorised_isCrossedHom p k Ω K L hKL A hA q hAq w hAw hglue
      (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) b hb b₀ hb₀)

/-- **A sorry-free replacement for `Work.SSGRoute.PT.finAtLevel`** (the value of the finite-place
half of `G1⁺` at a specified admissible level `L` and a specified factorisation `b₀`), with the
same signature: the three `sorry`s of the original are the two conjuncts of the proved
`PT.place_glue_level` and the class `levelClass_of_cocycle`. -/
noncomputable def finAtLevelFix
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
        K ≤ L → extH (classesK k L) 2 → ZMod p)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L)
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (b₀ : ((↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)))
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ)) : ZMod p := by
  classical
  -- ## the place of `K` under `A`, and the local dictionary `βl` at the base level `K`
  have hq := exists_place_under_isFinPlace k Ω K A hA
  let q := hq.choose
  have hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1 := hq.choose_spec.1
  have hβl := local_ext_h1_bridge p k Ω K ζ hζ hζK T hT M A hA q hAq
  let βl := hβl.choose
  -- ## the `k`-algebra tower `K → L` induced by the inclusion of intermediate fields
  letI : Algebra ↥K ↥L := (IntermediateField.inclusion hKL).toAlgebra
  haveI : IsScalarTower k ↥K ↥L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ↥K ↥L Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- ## the place `w` of `L` under `A`, the place glue and the localisation of units `ι`
  have hw := exists_place_under_isFinPlace k Ω L A hA
  let w := hw.choose
  have hAw : ∀ y : NumberField.RingOfIntegers L,
      y ∈ w.asIdeal ↔ A.valuation (((y : L) : Ω)) < 1 := hw.choose_spec.1
  have hglueL : (SSGRoute.decomp k A).map (SSGRoute.res k L) =
      SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofFinite w) := hw.choose_spec.2
  -- ### the lying-over relation and the restriction map `f` (`PT.place_glue_level`, proved)
  obtain ⟨hLies, hexf⟩ := place_glue_level k Ω K L hKL A hA q hAq w hAw
  let f := hexf.choose
  have hf := hexf.choose_spec
  have hιdata := localUnitsMap_exists k ↥K ↥L
    (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite w) hLies f hf
  let ι := hιdata.choose
  -- ### the class `[b]_L` (`PT.factorised_isCrossedHom` + `ExtH1.gammaZ1`)
  have hval : extH (Rep.res f
      (Rep.res (decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
        (modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))))) 1 :=
    levelClass_of_cocycle p k Ω K L hKL A hA q hAq w hAw hglueL f hf M T b hb b₀ hb₀
  -- ## the value
  let z : extH (localUnitsK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite w)) 2 :=
    levelPair f ι (βl a) hval
  exact χ L hKL (iota (k := k) (L := ↥L) (NK.GlobalCFT.Place.ofFinite w) z)

/-- **A sorry-free replacement for `Work.SSGRoute.PT.finAtValue`** (the value of the finite-place
half of `G1⁺` with the level and the factorisation taken from
`PT.exists_level_factors_locConstOnTwo`), with the same signature and the same body as the
original. -/
noncomputable def finAtValueFix
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L],
        K ≤ L → extH (classesK k L) 2 → ZMod p)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (ha : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) a)
    (hb2 : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b) : ZMod p := by
  classical
  have hL := exists_level_factors_locConstOnTwo k Ω K (SSGRoute.decomp k A) a b ha hb2
  let L := hL.choose
  have hLfin : FiniteDimensional k L := hL.choose_spec.choose
  have hLnorm : Normal k L := hL.choose_spec.choose_spec.choose
  letI : FiniteDimensional k L := hLfin
  letI : Normal k L := hLnorm
  letI : IsGalois k L := inferInstance
  letI : NumberField L := inferInstance
  have hKL : K ≤ L := hL.choose_spec.choose_spec.choose_spec.1
  have hb₀spec := hL.choose_spec.choose_spec.choose_spec.2
  let b₀ : ((↥L ≃ₐ[k] ↥L) → Work.SSGRoute.DualMod p (M ⊗[ZMod p] T)) :=
    hb₀spec.choose_spec.choose
  have hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = b₀ (AlgEquiv.restrictNormalHom L σ) :=
    hb₀spec.choose_spec.choose_spec.2
  exact finAtLevelFix p k Ω K ζ hζ hζK T hT χ M A hA L hKL a b hb b₀ hb₀

end Work.SSGRoute.PT

/-! ## Axiom audit -/

#print axioms Work.SSGRoute.PT.levelClass
#print axioms Work.SSGRoute.PT.levelClass_of_cocycle
#print axioms Work.SSGRoute.PT.finAtLevelFix
#print axioms Work.SSGRoute.PT.finAtValueFix

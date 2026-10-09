import Mathlib
import Submission.Work.SSGRoute.PT.vfShared
import Submission.Work.SSGRoute.PT.finHalfData
import Submission.Work.SSGRoute.E7cOmega.zfun_pairing_extLoc
import Submission.Work.SSGRoute.PT.finZH_levelChange_fix
import Submission.Work.SSGRoute.extHMap_gammaHom_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

open scoped TensorProduct Pointwise
open SSGRoute.PTExt CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **Transport of `localUnitsMapAt` along a propositional equality of the place-glue hom.**

The chosen local units map `localUnitsMapAt k K L w w' hw' f hf` is a `Classical.choose`, so an
equality `f₁ = f₂` of the place glues only relates the two choices through the `eqToHom` of the two
`Rep.res` spellings.  The proof is `subst` on the equality of the homs, after which the transport is
`eqToHom rfl = 𝟙` and the two choices differ only in a proof argument (proof irrelevance). -/
private theorem vfLocal_localUnitsMapAt_transport {k K L : Type} [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K] [Field L]
    [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional k L]
    [IsGalois k L]
    (w : NK.GlobalCFT.Place K) (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f₁ f₂ : ↥(SSGRoute.PTExt.decompK (k := k) w') →* ↥(SSGRoute.PTExt.decompK (k := k) w))
    (hf : f₁ = f₂)
    (hf₁ : ∀ σ : ↥(SSGRoute.PTExt.decompK (k := k) w'),
      ((f₁ σ : ↥(SSGRoute.PTExt.decompK (k := k) w)) : K ≃ₐ[k] K)
        = SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L))
    (hf₂ : ∀ σ : ↥(SSGRoute.PTExt.decompK (k := k) w'),
      ((f₂ σ : ↥(SSGRoute.PTExt.decompK (k := k) w)) : K ≃ₐ[k] K)
        = SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L)) :
    Work.SSGRoute.PT.localUnitsMapAt k K L w w' hw' f₁ hf₁
      = CategoryTheory.CategoryStruct.comp
          (CategoryTheory.eqToHom (congrArg (fun t => Rep.res t
            (SSGRoute.PTExt.localUnitsK (k := k) (K := K) w)) hf))
          (Work.SSGRoute.PT.localUnitsMapAt k K L w w' hw' f₂ hf₂) := by
  subst hf
  rw [CategoryTheory.eqToHom_refl]
  simp only [CategoryTheory.Category.id_comp]

/-- **The opaque `finZI` in the transparent `localUnitsMap` spelling.**

`finZI hKL A hA` is `localUnitsMapAt` (the `Classical.choose` of `localUnitsMap_exists`) at the
opaque place glue `finZF hKL A hA`, and `Work.SSGRoute.localUnitsMap` is the same `Classical.choose`
at the transparent `decompKRestrict`; the two are related by the `eqToHom` of the propositional
equality `Work.SSGRoute.PT.vf_finZF_eq`. -/
private theorem vfLocal_finZI_eq (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Work.SSGRoute.PT.finZI hKL A hA
      = CategoryTheory.CategoryStruct.comp
          (CategoryTheory.eqToHom (congrArg (fun t => Rep.res t
            (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
              (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))))
          (Work.SSGRoute.PT.vf_finZF_eq k Ω K L hKL A hA)))
          (Work.SSGRoute.localUnitsMap k (↥K) (↥L)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
            (NK.GlobalCFT.Place.liesOver_ofFinite
              (Work.SSGRoute.PT.asIdeal_liesOver_of_valuation_lt_one K L A
              (Work.SSGRoute.PT.finQ K A hA) (fun x => Work.SSGRoute.PT.finQ_spec K A hA x)
              (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y)))) := by
  exact vfLocal_localUnitsMapAt_transport
    (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
    (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
    (NK.GlobalCFT.Place.liesOver_ofFinite
      (Work.SSGRoute.PT.asIdeal_liesOver_of_valuation_lt_one K L A
        (Work.SSGRoute.PT.finQ K A hA) (fun x => Work.SSGRoute.PT.finQ_spec K A hA x)
        (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y)))
    (Work.SSGRoute.PT.finZF hKL A hA)
    (Work.SSGRoute.decompKRestrict k ↥K ↥L
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
      (NK.GlobalCFT.Place.liesOver_ofFinite
        (Work.SSGRoute.PT.asIdeal_liesOver_of_valuation_lt_one K L A
          (Work.SSGRoute.PT.finQ K A hA) (fun x => Work.SSGRoute.PT.finQ_spec K A hA x)
          (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y))))
    (Work.SSGRoute.PT.vf_finZF_eq k Ω K L hKL A hA)
    (Work.SSGRoute.PT.finZF_spec hKL A hA)
    (Work.SSGRoute.decompKRestrict_coe k ↥K ↥L
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
      (NK.GlobalCFT.Place.liesOver_ofFinite
        (Work.SSGRoute.PT.asIdeal_liesOver_of_valuation_lt_one K L A
          (Work.SSGRoute.PT.finQ K A hA) (fun x => Work.SSGRoute.PT.finQ_spec K A hA x)
          (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y))))

/-- **The local comparison of the two spellings of the value formula.**

`Z` is the idèle class obtained from `X` by pushing along the canonical idèle map
`idleRepMap k ↥K ↥L`, `h` is a class at the level `L` which is the class of the level-`L` cocycle
`ψ` (`hclass`), `b = ψ ∘ res k L` is its globally defined cocycle representative, and `βla` is the
local component of `X` at the place `finQ K A` of `↥K` (`hXa`).  Then the local piece of
`yonedaPair (extLoc w Z) (extHRestrict D_w h)` at the place `w = ofFinite (finQW L A)` of `↥L` is
the `finZF`/`finZI`/`finZH`-spelled `levelPair` that the hypothesis `hpair` of the abstract
dictionary produces.

The two sides live in the same type `extH (localUnitsK w) 2` (the intermediate coefficient
representations differ only by the *spelling* of the place-glue hom) and are equal because both are
the pairing of the localisation of `X` at `u = ofFinite (finQ K A)` with the restriction of `h`.

RECIPE (all ingredients are on disk).
* `Work.SSGRoute.PT.finZF` is the `Classical.choose` of `place_glue_level`; it is *propositionally*
  equal to the transparent `Work.SSGRoute.decompKRestrict` (`Work.SSGRoute.PT.vf_finZF_eq` in
  `Submission/Work/SSGRoute/PT/vfShared.lean`).  All differences between the two sides come from
  this one equality: introduce the two homs with `set`/`let`, `subst` their equality inside an
  auxiliary lemma *whose arguments are the homs* (the pattern of
  `Work.SSGRoute.PT.gammaZ1_levelChange_aux` in
  `Submission/Work/SSGRoute/PT/finZH_levelChange_fix.lean` and of
  `Work.SSGRoute.PT.gammaZ1_eqToHom_transport` in `PT/gammaZ1_transport.lean`), using
  `set_option backward.isDefEq.respectTransparency false`.
* The localisation of the pushed class: `Work.SSGRoute.E7cOmega.extLoc_push_ideleMap`
  (`PT/zfun_pairing_extLoc.lean`) computes `extLoc w Z` as
  `(extRes (decompKRestrict …) (extLoc u X)).comp (mk₀ (localUnitsMap k ↥K ↥L u w hw)) …`; combine
  with `hXa` and with `Work.SSGRoute.PT.vf_finZF_eq`.
* `finZI` and `localUnitsMap` are two `Classical.choose`s satisfying the same computation rule on
  `Additive.ofMul` (`Work.SSGRoute.PT.localUnitsMapAt_spec`, `Work.SSGRoute.localUnitsMap_spec`);
  they are equal after transporting the source representation (`Rep.hom_ext` +
  `Representation.IntertwiningMap.ext` + `LinearMap.ext`, as in
  `Work.SSGRoute.localUnitsMap_ext`).
* The class `finZH` is `gammaZ1` of the cocycle `ψ ∘ D_w.subtype` (its defining body
  `PT.finLevelClass`, exposed by `simp only [Work.SSGRoute.PT.finZH, Work.SSGRoute.PT.finLevelClass]`),
  and `extHRestrict (decompK w) h` is `gammaZ1` of the *same* cocycle for the action pulled back
  along `galRes ∘ D_w.subtype` (this is `Work.SSGRoute.extHMap_gammaHom_eq` applied to
  `r := (decompK w).subtype` and `hclass`); the two differ only by the (propositionally equal)
  action instance, so `gammaZ1_levelChange_aux` transports one to the other across the `Rep`-iso of
  the coefficient representations. -/
theorem vf_local_compare
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (X : CategoryTheory.Abelian.Ext
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))
      (SSGRoute.PTExt.idelesK k ↥K) 1)
    (βla : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))
      (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) 1)
    (hXa : SSGRoute.PTExt.extLoc (k := k) (K := ↥K)
      (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) X = βla)
    (h : SSGRoute.PTExt.extH
      (Rep.res (SSGRoute.PTExt.galRes k (↥K) (↥L))
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))) 1)
    (ψ : (↥L ≃ₐ[k] ↥L) → Work.SSGRoute.PT.VFcoef p M T)
    (hψ : ∀ g hh : ↥L ≃ₐ[k] ↥L,
      ψ (g * hh) = SSGRoute.PTExt.galRes k (↥K) (↥L) g • ψ hh + ψ g)
    (hclass : h = Work.SSGRoute.PT.levelClassOf (p := p) (k := k) (Ω := Ω) (K := K) (L := L)
      (T := T) (M := M) ψ hψ)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.PT.VFcoef p M T)
    (hbψ : ∀ σ : Ω ≃ₐ[k] Ω, b σ = ψ (SSGRoute.res k L σ))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
    (hb₀ : ∀ σ ∈ SSGRoute.decomp k A, b σ = ψ (AlgEquiv.restrictNormalHom L σ)) :
    SSGRoute.PTExt.yonedaPair
        (SSGRoute.PTExt.extLoc (k := k) (K := ↥L)
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))
          ((SSGRoute.PTExt.extRes (SSGRoute.PTExt.galRes k (↥K) (↥L)) X).comp
            (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k (↥K) (↥L)))
            (add_zero 1)))
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k)
          (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))) h)
      = SSGRoute.PTExt.levelPair (Work.SSGRoute.PT.finZF hKL A hA)
          (Work.SSGRoute.PT.finZI hKL A hA) βla
          (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb ψ hb₀) := by
  classical
  -- **step A**: the localisation of the pushed class (`extLoc_push_ideleMap` + `hXa`)
  have hloc : (SSGRoute.PTExt.extLoc (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) ((SSGRoute.PTExt.extRes (SSGRoute.PTExt.galRes k (↥K) (↥L)) X).comp (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k (↥K) (↥L))) (add_zero 1))) = (SSGRoute.PTExt.extRes (Work.SSGRoute.decompKRestrict k ↥K ↥L (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) (NK.GlobalCFT.Place.liesOver_ofFinite (Work.SSGRoute.PT.asIdeal_liesOver_of_valuation_lt_one K L A (Work.SSGRoute.PT.finQ K A hA) (fun x => Work.SSGRoute.PT.finQ_spec K A hA x) (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y)))) βla).comp
      (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.localUnitsMap k (↥K) (↥L) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) (NK.GlobalCFT.Place.liesOver_ofFinite (Work.SSGRoute.PT.asIdeal_liesOver_of_valuation_lt_one K L A (Work.SSGRoute.PT.finQ K A hA) (fun x => Work.SSGRoute.PT.finQ_spec K A hA x) (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y))))) (add_zero 1) := by
    rw [Work.SSGRoute.E7cOmega.extLoc_push_ideleMap (k := k) (K := ↥K) (L := ↥L) (z := X)
      (u := (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))) (w := (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))) (hw := (NK.GlobalCFT.Place.liesOver_ofFinite (Work.SSGRoute.PT.asIdeal_liesOver_of_valuation_lt_one K L A (Work.SSGRoute.PT.finQ K A hA) (fun x => Work.SSGRoute.PT.finQ_spec K A hA x) (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y)))) (ι := (Work.SSGRoute.localUnitsMap k (↥K) (↥L) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) (NK.GlobalCFT.Place.liesOver_ofFinite (Work.SSGRoute.PT.asIdeal_liesOver_of_valuation_lt_one K L A (Work.SSGRoute.PT.finQ K A hA) (fun x => Work.SSGRoute.PT.finQ_spec K A hA x) (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y)))))
      (hι := Work.SSGRoute.localUnitsMap_spec k (↥K) (↥L) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) (NK.GlobalCFT.Place.liesOver_ofFinite (Work.SSGRoute.PT.asIdeal_liesOver_of_valuation_lt_one K L A (Work.SSGRoute.PT.finQ K A hA) (fun x => Work.SSGRoute.PT.finQ_spec K A hA x) (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y))))]
    rw [hXa]
  -- the left hand side in the transparent `decompKRestrict`/`localUnitsMap` spelling
  have hstepA : SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) ((SSGRoute.PTExt.extRes (SSGRoute.PTExt.galRes k (↥K) (↥L)) X).comp (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.idleRepMap k (↥K) (↥L))) (add_zero 1))) (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))) h)
      = SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) (NK.GlobalCFT.Place.liesOver_ofFinite (Work.SSGRoute.PT.asIdeal_liesOver_of_valuation_lt_one K L A (Work.SSGRoute.PT.finQ K A hA) (fun x => Work.SSGRoute.PT.finQ_spec K A hA x) (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y)))) (Work.SSGRoute.localUnitsMap k (↥K) (↥L) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) (NK.GlobalCFT.Place.liesOver_ofFinite (Work.SSGRoute.PT.asIdeal_liesOver_of_valuation_lt_one K L A (Work.SSGRoute.PT.finQ K A hA) (fun x => Work.SSGRoute.PT.finQ_spec K A hA x) (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y)))) βla (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))) h) := by
    rw [hloc]
    rfl
  -- **assembly**: transport the `levelPair` from the transparent to the opaque spelling
  have hh : SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))) h
      = (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb ψ hb₀).comp
        (CategoryTheory.Abelian.Ext.mk₀ (CategoryTheory.eqToHom (congrArg (fun t =>
          Rep.res t (Rep.res (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype
            (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T))))
          (Work.SSGRoute.PT.vf_finZF_eq k Ω K L hKL A hA))))
        (add_zero 1) := by
    let X := Work.SSGRoute.PT.VFcoef p M T
    let GalL := ↥L ≃ₐ[k] ↥L
    let GalK := ↥K ≃ₐ[k] ↥K
    let q : NK.GlobalCFT.Place ↥K := NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)
    let w : NK.GlobalCFT.Place ↥L := NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)
    let hw₀ : w.LiesOver q := NK.GlobalCFT.Place.liesOver_ofFinite
        (Work.SSGRoute.PT.asIdeal_liesOver_of_valuation_lt_one K L A (Work.SSGRoute.PT.finQ K A hA)
          (fun x => Work.SSGRoute.PT.finQ_spec K A hA x) (Work.SSGRoute.PT.finQW L A hA)
          (fun y => Work.SSGRoute.PT.finQW_spec L A hA y))
    let DW := ↥(SSGRoute.PTExt.decompK (k := k) (K := ↥L) w)
    let Dq := ↥(SSGRoute.PTExt.decompK (k := k) (K := ↥K) q)
    let subw : DW →* GalL := (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w).subtype
    let subq : Dq →* GalK := (SSGRoute.PTExt.decompK (k := k) (K := ↥K) q).subtype
    let dkr : DW →* Dq := Work.SSGRoute.decompKRestrict k ↥K ↥L q w hw₀
    let fZF : DW →* Dq := Work.SSGRoute.PT.finZF hKL A hA
    letI hActL : DistribMulAction GalL X := DistribMulAction.compHom X (SSGRoute.PTExt.galRes k (↥K) (↥L))
    haveI hCommZL : SMulCommClass GalL ℤ X :=
      ⟨fun g n m => map_zsmul (AddMonoidHom.mk' (fun m => g • m) (fun a b => smul_add g a b)) n m⟩
    haveI hCommCL : SMulCommClass GalL SSGRoute.PTExt.Coeff X :=
      ⟨fun g c m => smul_comm g c.down m⟩
    haveI hCommZK : SMulCommClass GalK ℤ X :=
      ⟨fun g n m => map_zsmul (AddMonoidHom.mk' (fun m => g • m) (fun a b => smul_add g a b)) n m⟩
    haveI hCommCK : SMulCommClass GalK SSGRoute.PTExt.Coeff X :=
      ⟨fun g c m => smul_comm g c.down m⟩
    letI act1 : DistribMulAction DW X := DistribMulAction.compHom X (subq.comp dkr)
    haveI hC1 : @SMulCommClass DW SSGRoute.PTExt.Coeff X act1.toSMul _ :=
      Work.SSGRoute.PT.smulCommClass_compHom_aux (X := X) (R := SSGRoute.PTExt.Coeff) (subq.comp dkr)
    letI act2 : DistribMulAction DW X := DistribMulAction.compHom X (subq.comp fZF)
    haveI hC2 : @SMulCommClass DW SSGRoute.PTExt.Coeff X act2.toSMul _ :=
      Work.SSGRoute.PT.smulCommClass_compHom_aux (X := X) (R := SSGRoute.PTExt.Coeff) (subq.comp fZF)
    have hf : dkr = fZF := (Work.SSGRoute.PT.vf_finZF_eq k Ω K L hKL A hA).symm
    have hres : Rep.res fZF (Rep.res subq (SSGRoute.PTExt.modRep GalK X))
        = Rep.res dkr (Rep.res subq (SSGRoute.PTExt.modRep GalK X)) :=
      (congrArg (fun t => Rep.res t (Rep.res subq (SSGRoute.PTExt.modRep GalK X))) hf).symm
    let hζ1 : @Work.GroupCohomology.Z1 DW X _ _ act1 :=
      ⟨fun σ => ψ (subw σ), by
        rw [Work.GroupCohomology.mem_Z1_iff, Work.GroupCohomology.IsCrossedHom]
        intro g hh
        show ψ (subw (g * hh)) = (subq (dkr g)) • ψ (subw hh) + ψ (subw g)
        rw [map_mul, hψ (subw g) (subw hh),
          show subq (dkr g) = SSGRoute.PTExt.galRes k (↥K) (↥L) (subw g) from
            Work.SSGRoute.decompKRestrict_coe k ↥K ↥L q w hw₀ g]⟩
    let hζ2 : @Work.GroupCohomology.Z1 DW X _ _ act2 :=
      ⟨fun σ => ψ (subw σ), by
        rw [Work.GroupCohomology.mem_Z1_iff, Work.GroupCohomology.IsCrossedHom]
        intro g hh
        show ψ (subw (g * hh)) = (subq (fZF g)) • ψ (subw hh) + ψ (subw g)
        rw [map_mul, hψ (subw g) (subw hh),
          show subq (fZF g) = SSGRoute.PTExt.galRes k (↥K) (↥L) (subw g) from
            Work.SSGRoute.PT.finZF_spec hKL A hA g]⟩
    -- hL: the restriction of `h` to `D_w`, in the `gammaZ1` spelling
    have hL : SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w) h
        = (@Work.SSGRoute.ExtH1.gammaZ1 DW _ X _ act1 hC1
            (Work.SSGRoute.augSES_shortExact DW) hζ1) := by
      rw [hclass]
      simp only [SSGRoute.PT.levelClassOf, SSGRoute.PTExt.extHRestrict]
      conv_lhs =>
        change SSGRoute.PTExt.extHMap (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w).subtype
          (𝟙 (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w).subtype
            (SSGRoute.PTExt.modRep GalL X)))
          ((Work.SSGRoute.ExtH1.gammaHom GalL X (Work.SSGRoute.augSES_shortExact GalL)
            ((Work.GroupCohomology.H1π GalL X) ⟨ψ, hψ⟩)))
      rw [Work.SSGRoute.extHMap_gammaHom_eq
        (r := (SSGRoute.PTExt.decompK (k := k) (K := ↥L) w).subtype)]
      rw [Work.SSGRoute.ExtH1.gammaHom_H1π]
    -- hR: the level class `finZH`, in the `gammaZ1` spelling
    have hR : (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb ψ hb₀)
        = (@Work.SSGRoute.ExtH1.gammaZ1 DW _ X _ act2 hC2
            (Work.SSGRoute.augSES_shortExact DW) hζ2) := by
      simp only [finZH, finLevelClass, Work.SSGRoute.ExtH1.gammaHom_H1π]
      congr 1
    rw [hL, hR]
    exact @Work.SSGRoute.PT.gammaZ1_levelChange_aux DW GalK Dq _ _ _ X _ _ hCommCK
      subq dkr fZF hf hres hζ1 hζ2 (fun _ => rfl) hC1 hC2

  have htrans := Work.SSGRoute.Y3Key.levelPair_transport'
    (x := βla)
    (f₁ := (Work.SSGRoute.PT.finZF hKL A hA)) (f₂ := (Work.SSGRoute.decompKRestrict k ↥K ↥L (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) (NK.GlobalCFT.Place.liesOver_ofFinite (Work.SSGRoute.PT.asIdeal_liesOver_of_valuation_lt_one K L A (Work.SSGRoute.PT.finQ K A hA) (fun x => Work.SSGRoute.PT.finQ_spec K A hA x) (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y)))))
    (A := (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)))) (M := (Rep.res ((SSGRoute.PTExt.decompK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype) (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))) (B' := (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))))
    (ρA := CategoryTheory.eqToHom (congrArg (fun t => Rep.res t (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)))) (Work.SSGRoute.PT.vf_finZF_eq k Ω K L hKL A hA)))
    (ρM := CategoryTheory.eqToHom (congrArg (fun t => Rep.res t (Rep.res ((SSGRoute.PTExt.decompK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype) (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))) (Work.SSGRoute.PT.vf_finZF_eq k Ω K L hKL A hA)))
    (σM := CategoryTheory.eqToHom (congrArg (fun t => Rep.res t (Rep.res ((SSGRoute.PTExt.decompK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype) (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))) ((Work.SSGRoute.PT.vf_finZF_eq k Ω K L hKL A hA)).symm))
    (ι₁ := (Work.SSGRoute.PT.finZI hKL A hA)) (ι₂ := (Work.SSGRoute.localUnitsMap k (↥K) (↥L) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) (NK.GlobalCFT.Place.liesOver_ofFinite (Work.SSGRoute.PT.asIdeal_liesOver_of_valuation_lt_one K L A (Work.SSGRoute.PT.finQ K A hA) (fun x => Work.SSGRoute.PT.finQ_spec K A hA x) (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y)))))
    (h₁ := (Work.SSGRoute.PT.finZH p K T M L hKL A hA b hb ψ hb₀)) (h₂ := (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA))) h))
    (hρσM := by
      rw [CategoryTheory.eqToHom_trans]
      exact CategoryTheory.eqToHom_refl _ _)
    (hι := vfLocal_finZI_eq p k Ω K T M L hKL A hA)
    (hh := hh)
    (hx := Work.SSGRoute.Y3Key.extRes_transport' (A := (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)))) (M := (Rep.res ((SSGRoute.PTExt.decompK (k := k) (K := ↥K) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA))).subtype) (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (Work.SSGRoute.PT.VFcoef p M T)))) (r := 1)
      (x := βla) (f₁ := (Work.SSGRoute.PT.finZF hKL A hA)) (f₂ := (Work.SSGRoute.decompKRestrict k ↥K ↥L (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQ K A hA)) (NK.GlobalCFT.Place.ofFinite (Work.SSGRoute.PT.finQW L A hA)) (NK.GlobalCFT.Place.liesOver_ofFinite (Work.SSGRoute.PT.asIdeal_liesOver_of_valuation_lt_one K L A (Work.SSGRoute.PT.finQ K A hA) (fun x => Work.SSGRoute.PT.finQ_spec K A hA x) (Work.SSGRoute.PT.finQW L A hA) (fun y => Work.SSGRoute.PT.finQW_spec L A hA y))))) ((Work.SSGRoute.PT.vf_finZF_eq k Ω K L hKL A hA)).symm)
  rw [hstepA]
  exact htrans.symm

end Work.SSGRoute.PT

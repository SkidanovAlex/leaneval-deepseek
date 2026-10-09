import Mathlib
import Submission.Work.SSGRoute.E1aClean.phiUnrU1
import Submission.Work.SSGRoute.E1aClean.phiUnrHelpers
import Submission.Work.SSGRoute.E1aClean.decompDatum
import Submission.Work.SSGRoute.E1aClean.LeadPhiUnr.henselUnit_pow_mul_localUnits_of_inertiaFixedRoot
import Submission.Work.SSGRoute.E1aClean.LeadPhiUnr.decompFieldHenselEmb_units_mem_localUnits_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E1aClean.LeadPhiUnr

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open CategoryTheory SSGRoute.PTExt
open Work.SSGRoute.ExtChain.E1cGeneric

attribute [local instance 10000] Rep.hV1 Rep.hV2

noncomputable section

/-- The `p`-fold multiple of the identity of the free cover is killed by the cover morphism, as soon
as the target is `p`-torsion. -/
theorem e1cU4_pzsmul_id_comp_freeCover_eq_zero {G : Type} [Group G] (R : Rep.{0} Coeff G) (p : ℕ)
    (hR : ∀ r : R.V, (p : ℤ) • r = 0) :
    ((p : ℤ) • 𝟙 (Rep.free Coeff G R.V)) ≫ Work.SSGRoute.freeCover R = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  rw [Rep.hom_comp, Rep.zsmul_hom, Rep.hom_id, Rep.zero_hom]
  simp only [Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
    Representation.IntertwiningMap.zero_toLinearMap, LinearMap.zero_apply]
  change (Work.SSGRoute.freeCover R).hom.toLinearMap
    (((p : ℤ) • (LinearMap.id : ↑(Rep.free Coeff G ↑R) →ₗ[Coeff] ↑(Rep.free Coeff G ↑R))) x) = 0
  rw [LinearMap.smul_apply, LinearMap.id_apply, map_zsmul]
  exact hR _

/-- In `Coeff = ULift ℤ`, a nonzero multiple is zero only for zero. -/
theorem e1cU4_coeff_zsmul_eq_zero {p : ℕ} (hp : p ≠ 0) {x : Coeff} (h : (p : ℤ) • x = 0) :
    x = 0 := by
  have h2 : (p : ℤ) * x.down = 0 := by simpa using congrArg ULift.down h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (by exact_mod_cast hp)
  · exact ULift.ext h3

theorem e1cHensel_comp_val_eq_zero_of_unramified (p : ℕ) [Fact p.Prime]
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K))
    (hAq : ∀ x : NumberField.RingOfIntegers ↥K,
      x ∈ q.asIdeal ↔ A.valuation (((x : ↥K) : Ω)) < 1)
    (hp : ¬ A.valuation (p : Ω) < 1)
    [CharZero ↥(decompField k Ω A)] [IsAlgClosure ↥(decompField k Ω A) Ω]
    [FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    [IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    (φ : ↥(henselOverDecomp k Ω K A) →+*
        NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite q))
    (hφ : ∀ x : ↥K, φ ⟨(x : Ω), le_henselField k Ω K A x.2⟩ =
        algebraMap ↥K (NK.GlobalCFT.Place.localField ↥K (NK.GlobalCFT.Place.ofFinite q)) x)
    (hφint : ∀ x : (↥(henselOverDecomp k Ω K A))ˣ,
        Units.map φ.toMonoidHom x ∈ NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite q)
          ↔ A.valuation (((x : ↥(henselOverDecomp k Ω K A)) : Ω)) = 1)
    (hφgal : ∀ (g : ↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)]
          ↥(henselOverDecomp k Ω K A)) (x : (↥(henselOverDecomp k Ω K A))ˣ),
        NK.HassePrinciple.valUnitsAddHom ↥K q
            (Additive.ofMul (Units.map φ.toMonoidHom (Units.map (g : _ →+* _).toMonoidHom x)))
          = NK.HassePrinciple.valUnitsAddHom ↥K q (Additive.ofMul (Units.map φ.toMonoidHom x)))
    (μ : SSGRoute.PTExt.unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A) ⟶
        SSGRoute.PTExt.unitRep (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)]
          ↥(henselOverDecomp k Ω K A)))
    (hμ : ∀ x : (↥(henselOverDecomp k Ω K A))ˣ,
        μ.hom (Additive.ofMul x) =
          NK.HassePrinciple.valUnitsAddHom ↥K q (Additive.ofMul (Units.map φ.toMonoidHom x)))
    (R₂ : Rep.{0} SSGRoute.PTExt.Coeff (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)]
        ↥(henselOverDecomp k Ω K A)))
    [Module.Finite ℤ R₂.V] (hR₂ : ∀ r : R₂.V, (p : ℤ) • r = 0)
    (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
      (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A) R₂)))
    (hc : ∀ g : Ω ≃ₐ[↥(decompField k Ω A)] Ω,
      SSGRoute.IsInertia k A (AlgEquiv.restrictScalars k g) → c.1 g = 0) :
    ((Work.SSGRoute.ExtChain.E1cGeneric.e1cEquiv (k := ↥(decompField k Ω A)) (Ω := Ω)
        (K := henselOverDecomp k Ω K A) R₂).symm
        (Work.AbsoluteKummer.H1π (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
          (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A) R₂) c)).comp
      (CategoryTheory.Abelian.Ext.mk₀ μ) (add_zero 1) = 0 := by
  classical
  have hpt : (p : ℤ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  -- ## Step 1: the lift `ñ` and the `Ext⁰`-class `yE`
  let ñ : E1cN R₂ := liftOf R₂ c
  have hñ : ∀ g : Ω ≃ₐ[↥(decompField k Ω A)] Ω,
      iotaH R₂ (c.1 g) = (Work.GroupCohomology.d0 _ (E1cN R₂)) ñ g := by
    intro g
    have h := congrFun (liftOf_spec R₂ c) g
    rw [Work.AbsoluteKummer.mapZ1_apply] at h
    exact h.symm
  have hmem : piH R₂ ñ ∈ Work.AbsoluteKummer.H0 (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
      (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A)
        (E1cR1 R₂)) :=
    piH_mem_of_d0_eq R₂ c ñ (by
      funext g
      rw [Work.AbsoluteKummer.mapZ1_apply]
      exact (hñ g).symm)
  let yE : Abelian.Ext (E1cR1 R₂)
      (unitsK ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)) 0 :=
    (PsiE (E1cR1 R₂)).symm ⟨piH R₂ ñ, hmem⟩
  have hPsi : PsiEMap (E1cR1 R₂) yE = ⟨piH R₂ ñ, hmem⟩ := AddEquiv.apply_symm_apply _ _
  have hPsi' : (↑(PsiEMap (E1cR1 R₂) yE) : Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω
        (henselOverDecomp k Ω K A) (E1cR1 R₂)) = piH R₂ ñ := by
    rw [hPsi]
  have hmap : e1cMap R₂ (PhiE R₂ yE) =
      Work.AbsoluteKummer.H1π (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
        (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A) R₂) c :=
    e1cMap_eq_H1π_of_cocycle_lift R₂ c ñ (fun g => hñ g) yE (by rw [hPsi'])
  -- the dictionary value of `PhiE yE`
  have hX : (e1cEquiv (k := ↥(decompField k Ω A)) (Ω := Ω)
        (K := henselOverDecomp k Ω K A) R₂) (PhiE R₂ yE) =
      Work.AbsoluteKummer.H1π (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
        (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A) R₂) c := by
    have hEqv : ∀ z : Abelian.Ext R₂ (unitsK ↥(decompField k Ω A)
        ↥(henselOverDecomp k Ω K A)) 1,
        (e1cEquiv (k := ↥(decompField k Ω A)) (Ω := Ω) (K := henselOverDecomp k Ω K A) R₂) z
          = e1cMap R₂ z := fun z => rfl
    rw [hEqv]
    exact hmap
  -- ## Step 2: the `p`-multiplication `Φ : F ⟶ R₁`
  let G' : Type := ↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)
  have hzero : ((p : ℤ) • 𝟙 (E1cF R₂)) ≫ Work.SSGRoute.freeCover R₂ = 0 :=
    e1cU4_pzsmul_id_comp_freeCover_eq_zero R₂ p hR₂
  let Φ : E1cF R₂ ⟶ E1cR1 R₂ :=
    Limits.kernel.lift (Work.SSGRoute.freeCover R₂) ((p : ℤ) • 𝟙 (E1cF R₂)) hzero
  have hΦ : Φ ≫ Limits.kernel.ι (Work.SSGRoute.freeCover R₂) = (p : ℤ) • 𝟙 (E1cF R₂) :=
    Limits.kernel.lift_ι (Work.SSGRoute.freeCover R₂) ((p : ℤ) • 𝟙 (E1cF R₂)) hzero
  have hκΦ : Limits.kernel.ι (Work.SSGRoute.freeCover R₂) ≫ Φ =
      (p : ℤ) • 𝟙 (E1cR1 R₂) := by
    apply (cancel_mono (Limits.kernel.ι (Work.SSGRoute.freeCover R₂))).mp
    rw [Category.assoc, hΦ, Preadditive.comp_zsmul, Category.comp_id, Preadditive.zsmul_comp,
      Category.id_comp]
  -- the underlying value of `Φ` on the `s`-th basis vector
  have hkappa_gen : ∀ s : R₂.V,
      kappa R₂ (Φ.hom (Finsupp.single s (MonoidAlgebra.single (1 : G') 1)))
        = (p : ℤ) • (Finsupp.single s (MonoidAlgebra.single (1 : G') 1)) := by
    intro s
    have h : (Φ ≫ Limits.kernel.ι (Work.SSGRoute.freeCover R₂))
        (Finsupp.single s (MonoidAlgebra.single (1 : G') 1))
        = ((p : ℤ) • 𝟙 (E1cF R₂)) (Finsupp.single s (MonoidAlgebra.single (1 : G') 1)) := by
      rw [hΦ]
    rw [Rep.comp_apply] at h
    rw [show (ConcreteCategory.hom ((p : ℤ) • 𝟙 (E1cF R₂)))
          (Finsupp.single s (MonoidAlgebra.single (1 : G') 1))
        = (p : ℤ) • (Finsupp.single s (MonoidAlgebra.single (1 : G') 1)) from by
      rw [show (ConcreteCategory.hom ((p : ℤ) • 𝟙 (E1cF R₂)))
            (Finsupp.single s (MonoidAlgebra.single (1 : G') 1))
          = (p : ℤ) • ((𝟙 (E1cF R₂)) (Finsupp.single s (MonoidAlgebra.single (1 : G') 1)))
          from rfl,
        Rep.id_apply]] at h
    simpa [kappa] using h
  -- ## Step 3: the coefficient map `h'`
  have hdiv : ∀ s : R₂.V, ∃ cs : Coeff,
      (p : ℤ) • cs = μ.hom (Additive.ofMul (Additive.toMul ((Abelian.Ext.addEquiv₀ yE).hom
        (Φ.hom (Finsupp.single s (MonoidAlgebra.single (1 : G') 1)))))) := by
    intro s
    -- the `K^h`-unit cut out by `yE` at the `s`-th basis vector
    let u : (↥(henselOverDecomp k Ω K A))ˣ :=
      Additive.toMul ((Abelian.Ext.addEquiv₀ yE).hom
        (Φ.hom (Finsupp.single s (MonoidAlgebra.single (1 : G') 1))))
    -- the coboundary relation: the `Ω`-value of `u` is the `p`-th power of `ñ` at the basis vector
    have hkey : ∀ r : (E1cR1 R₂).V,
        Additive.ofMul (Units.map (algebraMap ↥(henselOverDecomp k Ω K A) Ω).toMonoidWithZeroHom
            (Additive.toMul ((Abelian.Ext.addEquiv₀ yE).hom r))) = ñ (kappa R₂ r) := by
      intro r
      have h1 : Additive.ofMul (Units.map (algebraMap ↥(henselOverDecomp k Ω K A)
            Ω).toMonoidWithZeroHom
            (Additive.toMul ((Abelian.Ext.addEquiv₀ yE).hom r)))
          = (↑(PsiEMap (E1cR1 R₂) yE) : Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω
              (henselOverDecomp k Ω K A) (E1cR1 R₂)) r := by
        rw [← Work.SSGRoute.toCoindH0_apply (E1cR1 R₂) (Abelian.Ext.addEquiv₀ yE) r]
        rfl
      rw [h1, hPsi', piH_apply]
      rfl
    have hy : (((Additive.toMul (ñ (Finsupp.single s (MonoidAlgebra.single (1 : G') 1)))) : Ωˣ) : Ω) ^ p
        = ((u : ↥(henselOverDecomp k Ω K A)) : Ω) := by
      have h := hkey (Φ.hom (Finsupp.single s (MonoidAlgebra.single (1 : G') 1)))
      rw [hkappa_gen s, map_zsmul] at h
      rw [show (p : ℤ) • (ñ (Finsupp.single s (MonoidAlgebra.single (1 : G') 1)))
          = Additive.ofMul ((Additive.toMul (ñ (Finsupp.single s (MonoidAlgebra.single
              (1 : G') 1))) : Ωˣ) ^ p) by
        rw [ofMul_pow]; simp] at h
      have h3 := Additive.ofMul.injective h
      have h4 := congrArg (fun z : Ωˣ => (z : Ω)) h3
      rw [Units.coe_map, Units.val_pow_eq_pow_val] at h4
      exact h4.symm
    -- inertia elements of `G_K` fix the root
    have hI : ∀ σ : Ω ≃ₐ[k] Ω, σ ∈ K.fixingSubgroup → SSGRoute.IsInertia k A σ →
        σ (((Additive.toMul (ñ (Finsupp.single s (MonoidAlgebra.single (1 : G') 1)))) : Ωˣ) : Ω)
          = (((Additive.toMul (ñ (Finsupp.single s (MonoidAlgebra.single (1 : G') 1)))) : Ωˣ) : Ω) := by
      intro σ hσK hσI
      -- σ fixes the decomposition field
      have hfix : ∀ c : ↥(decompField k Ω A), σ (c : Ω) = (c : Ω) := by
        intro c
        exact (IntermediateField.mem_fixedField_iff (SSGRoute.decomp k A) (c : Ω)).mp c.2 σ hσI.1
      -- σ as an element of `Gal(Ω/k^h)`
      let σ' : Ω ≃ₐ[↥(decompField k Ω A)] Ω :=
        { toFun := σ
          invFun := σ.symm
          left_inv := σ.left_inv
          right_inv := σ.right_inv
          map_mul' := σ.map_mul
          map_add' := σ.map_add
          commutes' := hfix }
      have hrestrict : AlgEquiv.restrictScalars k σ' = σ := rfl
      have hcσ' : c.1 σ' = 0 := by
        apply hc σ'
        rw [hrestrict]
        exact hσI
      have hd0 : (Work.GroupCohomology.d0 _ (E1cN R₂)) ñ σ' = 0 := by
        rw [← hñ σ', hcσ', map_zero]
      have hsub := hd0
      rw [Work.GroupCohomology.d0_apply] at hsub
      have hinv := sub_eq_zero.mp hsub
      -- σ fixes `K^h` pointwise
      have hres : SSGRoute.res (↥(decompField k Ω A))
          (henselOverDecomp k Ω K A) σ' = 1 := by
        apply AlgEquiv.ext
        intro x
        have hx : (x : Ω) ∈ IntermediateField.fixedField
            (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker) := henselOverDecomp_coe k Ω K A x
        have hσK' : σ ∈ (SSGRoute.res k K).ker := by
          rw [IntermediateField.restrictNormalHom_ker K]
          exact hσK
        have hfixx : σ (x : Ω) = (x : Ω) :=
          (IntermediateField.mem_fixedField_iff _ _).mp hx σ ⟨hσI.1, hσK'⟩
        rw [AlgEquiv.one_apply]
        apply Subtype.ext
        rw [AlgEquiv.restrictNormalHom_apply]
        exact hfixx
      -- evaluate the invariant relation at the basis vector
      have hev := congrArg (fun z : E1cN R₂ =>
        z (Finsupp.single s (MonoidAlgebra.single (1 : G') 1))) hinv
      rw [Work.SSGRoute.homCoind.smul_apply, hres, inv_one, map_one] at hev
      simp only [Module.End.one_apply] at hev
      have h4 := congrArg (fun z : Additive Ωˣ => ((Additive.toMul z : Ωˣ) : Ω)) hev
      exact h4
    obtain ⟨b, w, hw, hbw⟩ :=
      henselUnit_pow_mul_localUnits_of_inertiaFixedRoot p k Ω K ζ hζ hζK A hA q hAq hp φ hφ
        hφint u (((Additive.toMul (ñ (Finsupp.single s (MonoidAlgebra.single (1 : G') 1)))) : Ωˣ) : Ω)
        hy hI
    refine ⟨NK.HassePrinciple.valUnitsAddHom ↥K q (Additive.ofMul b), ?_⟩
    show (p : ℤ) • (NK.HassePrinciple.valUnitsAddHom ↥K q (Additive.ofMul b)) = μ.hom (Additive.ofMul u)
    rw [hμ u, hbw,
      show Additive.ofMul (b ^ p * w) = (p : ℤ) • Additive.ofMul b + Additive.ofMul w by
        rw [ofMul_mul, show b ^ p = b ^ (p : ℤ) from (zpow_natCast b p).symm,
          ofMul_zpow],
      map_add, map_zsmul, NK.HassePrinciple.valUnitsAddHom_incl_eq_zero q ⟨w, hw⟩, add_zero]
  choose cse hcse using hdiv
  let h' : E1cF R₂ ⟶ SSGRoute.PTExt.unitRep G' :=
    Rep.freeLift (k := Coeff) (G := G') (SSGRoute.PTExt.unitRep G') (fun s => cse s)
  have hgen_h' : ∀ s : R₂.V,
      (Rep.Hom.hom h') (Finsupp.single s (MonoidAlgebra.single (1 : G') 1)) = cse s := by
    intro s
    show Representation.freeLift (SSGRoute.PTExt.unitRep G').ρ (fun s => cse s)
        (Finsupp.single s (MonoidAlgebra.single (1 : G') 1)) = cse s
    rw [Representation.freeLift_single_single]
    simp
  -- ## Step 4: `Φ ≫ yE ≫ μ = p • h'` and `hfac`
  have hpm : Φ ≫ Abelian.Ext.addEquiv₀ yE ≫ μ = (p : ℤ) • h' := by
    apply Rep.free_ext (k := Coeff) (G := G') (A := SSGRoute.PTExt.unitRep G')
    intro s
    rw [show (Rep.Hom.hom ((p : ℤ) • h')) (Finsupp.single s (MonoidAlgebra.single (1 : G') 1))
        = (p : ℤ) • ((Rep.Hom.hom h') (Finsupp.single s (MonoidAlgebra.single (1 : G') 1)))
        from rfl]
    rw [hgen_h']
    show (Rep.Hom.hom μ) ((Rep.Hom.hom (Abelian.Ext.addEquiv₀ yE)) ((Rep.Hom.hom Φ)
        (Finsupp.single s (MonoidAlgebra.single (1 : G') 1)))) = (p : ℤ) • cse s
    exact (hcse s).symm
  have hfac0 : (p : ℤ) • (Abelian.Ext.addEquiv₀ yE ≫ μ)
      = Limits.kernel.ι (Work.SSGRoute.freeCover R₂) ≫ (Φ ≫ Abelian.Ext.addEquiv₀ yE ≫ μ) := by
    rw [← Category.assoc, hκΦ, Preadditive.zsmul_comp, Category.id_comp]
  have hfac : Abelian.Ext.addEquiv₀ yE ≫ μ =
      Limits.kernel.ι (Work.SSGRoute.freeCover R₂) ≫ h' := by
    have h1 : (p : ℤ) • (Abelian.Ext.addEquiv₀ yE ≫ μ)
        = (p : ℤ) • (Limits.kernel.ι (Work.SSGRoute.freeCover R₂) ≫ h') := by
      rw [hfac0, hpm, Preadditive.comp_zsmul]
    have h2 : ∀ r : (E1cR1 R₂).V,
        (Abelian.Ext.addEquiv₀ yE ≫ μ) r
          = (Limits.kernel.ι (Work.SSGRoute.freeCover R₂) ≫ h') r := by
      intro r
      have h3 : (p : ℤ) • ((Abelian.Ext.addEquiv₀ yE ≫ μ) r)
          = (p : ℤ) • ((Limits.kernel.ι (Work.SSGRoute.freeCover R₂) ≫ h') r) := by
        have h := congrArg (fun g : E1cR1 R₂ ⟶ SSGRoute.PTExt.unitRep G' => g r) h1
        rw [show ((p : ℤ) • (Abelian.Ext.addEquiv₀ yE ≫ μ)) r
              = (p : ℤ) • ((Abelian.Ext.addEquiv₀ yE ≫ μ) r) from rfl,
            show ((p : ℤ) • (Limits.kernel.ι (Work.SSGRoute.freeCover R₂) ≫ h')) r
              = (p : ℤ) • ((Limits.kernel.ι (Work.SSGRoute.freeCover R₂) ≫ h') r) from rfl] at h
        exact h
      have h4 : ULift.down ((Abelian.Ext.addEquiv₀ yE ≫ μ) r)
          = ULift.down ((Limits.kernel.ι (Work.SSGRoute.freeCover R₂) ≫ h') r) := by
        refine mul_left_cancel₀ hpt ?_
        simpa using congrArg ULift.down h3
      exact ULift.ext h4
    exact Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext h2))
  -- ## Step 5: conclude with (U1)
  rw [← show (PhiE R₂ yE) = (e1cEquiv (k := ↥(decompField k Ω A)) (Ω := Ω)
      (K := henselOverDecomp k Ω K A) R₂).symm
      (Work.AbsoluteKummer.H1π (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
        (Work.SSGRoute.homCoind ↥(decompField k Ω A) Ω (henselOverDecomp k Ω K A) R₂) c) from
    (AddEquiv.eq_symm_apply _).mpr hX]
  exact PhiE_comp_mk0_eq_zero_of_factor (k := ↥(decompField k Ω A)) (Ω := Ω)
    (K := henselOverDecomp k Ω K A) R₂ μ yE h' hfac

end

end Work.SSGRoute.E1aClean.LeadPhiUnr

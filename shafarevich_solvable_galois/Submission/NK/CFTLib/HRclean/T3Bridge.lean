import Mathlib
import Submission.NK.CFTLib.HRclean.ARLClean
import Submission.NK.CFTLib.HRclean.chebTransferCopy
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.CFTLib.HRclean.locUnitsInflationCopy
import Submission.NK.HassePrinciple.subsingleton_groupCohomology_one_unitsRep
import Submission.NK.CFTLib.Existence.unitsRep_fixedPoints_eq_range_algebraMap
import Submission.NK.CFTLib.HR.TransferAux.Setup
import Submission.Commons.RepresentationTheory.GroupCohomology.range_infNatTrans_eq_ker_resNatTrans_of_subsingleton
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open CategoryTheory

namespace NK.CFTLib.HRclean.T3

open NK.CFTLib.HR.TransferAux

/-- The units representation `Eˣ` of `Gal(E/K)`, with the coefficient ring `ULift ℤ` and all
universes pinned, written so that the underlying type reduces. -/
noncomputable abbrev urep (K E : Type) [Field K] [Field E] [Algebra K E] :
    Rep.{0, 0, 0} NK.HassePrinciple.CoeffInt (E ≃ₐ[K] E) :=
  Rep.of (Representation.ofDistribMulAction NK.HassePrinciple.CoeffInt (E ≃ₐ[K] E) (Additive Eˣ))

/-- The action of the Galois group on the units representation, in multiplicative form. -/
lemma urep_rho_ofMul {K L : Type} [Field K] [Field L] [Algebra K L]
    (g : L ≃ₐ[K] L) (u : Lˣ) :
    (urep K L).ρ g (Additive.ofMul u) = Additive.ofMul (g • u) := rfl

variable {K M E : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field E]
  [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E]
  [FiniteDimensional K M] [FiniteDimensional K E] [IsGalois K M] [IsGalois K E] [IsGalois M E]

/-- `rN K M E` is the fixing subgroup of the image of `M` in `E`. -/
lemma mem_rN_iff (σ : E ≃ₐ[K] E) :
    σ ∈ rN K M E ↔ ∀ m : M, σ (algebraMap M E m) = algebraMap M E m :=
  NK.CFTLib.HRclean.ARL.mem_rn_iff (K := K) (M := M) (E := E) σ

/-- The canonical `K`-algebra isomorphism `Gal(E/M) ≃* ker (Gal(E/K) →* Gal(M/K))`. -/
noncomputable def galEquivRhn :
    (E ≃ₐ[M] E) ≃* ↥(rN K M E) where
  toFun τ := ⟨AlgEquiv.restrictScalars K τ, by
    rw [mem_rN_iff]
    intro m
    exact τ.commutes m⟩
  invFun s := AlgEquiv.ofRingEquiv (f := (s.1).toRingEquiv)
    (fun m => (mem_rN_iff s.1).mp s.2 m)
  left_inv τ := AlgEquiv.ext fun x => rfl
  right_inv s := Subtype.ext (AlgEquiv.ext fun x => rfl)
  map_mul' a b := Subtype.ext (AlgEquiv.ext fun x => rfl)

@[simp]
lemma galEquivRhn_apply_coe (τ : E ≃ₐ[M] E) :
    ((galEquivRhn (K := K) (M := M) (E := E) τ : ↥(rN K M E)) : E ≃ₐ[K] E)
      = AlgEquiv.restrictScalars K τ := rfl

/-- Hilbert 90 for the kernel subgroup: `H¹(Gal(E/M), Eˣ) = 0`. -/
theorem subsingleton_H1_res_rn :
    Subsingleton (groupCohomology (Rep.res (rN K M E).subtype (urep K E)) 1) := by
  haveI hME : Subsingleton (groupCohomology (urep M E) 1) :=
    NK.HassePrinciple.subsingleton_groupCohomology_one_unitsRep (K := M) (L := E)
  have h₁ : groupCohomology
      (Rep.res (galEquivRhn (K := K) (M := M) (E := E)).symm (urep M E)) 1 ≅
      groupCohomology (urep M E) 1 :=
    groupCohomology.mapIso (galEquivRhn (K := K) (M := M) (E := E)).symm
      (LinearEquiv.refl NK.HassePrinciple.CoeffInt.{0} (urep M E).V)
      (by intro g; rfl) 1
  exact ⟨fun a b => (Iso.toLinearEquiv h₁).injective (Subsingleton.elim _ _)⟩

/-- The elementwise Galois descent for the units: the `Gal(E/M)`-invariants of `Eˣ` are the
units of `M`. -/
lemma units_mem_invariants_iff (u : Eˣ) :
    (∀ h : ↥(rN K M E),
        (urep K E).ρ (h : E ≃ₐ[K] E) (Additive.ofMul u) = Additive.ofMul u) ↔
      ∃ v : Mˣ, Units.map (algebraMap M E).toMonoidHom v = u :=
  NK.CFTLib.Existence.unitsRep_fixedPoints_eq_range_algebraMap.{0} (K := K) (M := M) (E := E)
    (rN K M E) (fun σ => mem_rN_iff σ) u

/-- The action of an element of the Galois group on the units representation, explicitly. -/
lemma unitsRep_rho_ofMul (g : E ≃ₐ[K] E) (u : Eˣ) :
    (urep K E).ρ g (Additive.ofMul u) = Additive.ofMul (g • u) :=
  urep_rho_ofMul (K := K) (L := E) g u

/-- The action of an element of the Galois group on a unit coming from `M`. -/
lemma smul_units_map (σ : E ≃ₐ[K] E) (v : Mˣ)
    (hσ : ∀ m : M, σ (algebraMap M E m) = algebraMap M E m) :
    σ • Units.map (algebraMap M E).toMonoidHom v = Units.map (algebraMap M E).toMonoidHom v := by
  apply Units.ext
  show ((σ • Units.map (algebraMap M E).toMonoidHom v : Eˣ) : E)
      = ((Units.map (algebraMap M E).toMonoidHom v : Eˣ) : E)
  rw [show ((σ • Units.map (algebraMap M E).toMonoidHom v : Eˣ) : E)
      = σ ((Units.map (algebraMap M E).toMonoidHom v : Eˣ) : E) from by simp]
  rw [Units.coe_map]
  exact hσ _

/-- The underlying element of the invariants is fixed. -/
lemma unitsInclAddToAdd_mem_invariants (v : Additive Mˣ) :
    (Units.map (algebraMap M E).toMonoidHom).toAdditive v ∈
      Representation.invariants ((urep K E).ρ.comp (rN K M E).subtype) := by
  rw [Representation.mem_invariants]
  intro h
  change (urep K E).ρ (h : E ≃ₐ[K] E)
      (Additive.ofMul (Units.map (algebraMap M E).toMonoidHom (Additive.toMul v)))
    = Additive.ofMul (Units.map (algebraMap M E).toMonoidHom (Additive.toMul v))
  rw [unitsRep_rho_ofMul]
  exact congrArg Additive.ofMul
    (smul_units_map (h : E ≃ₐ[K] E) (Additive.toMul v) ((mem_rN_iff (h : E ≃ₐ[K] E)).1 h.2))

/-- The additive monoid hom `Mˣ → (Eˣ)^{Gal(E/M)}` of the Galois descent. -/
noncomputable def unitsInvAddHom :
    Additive Mˣ →+ Representation.invariants ((urep K E).ρ.comp (rN K M E).subtype) where
  toFun v := ⟨(Units.map (algebraMap M E).toMonoidHom).toAdditive v,
    unitsInclAddToAdd_mem_invariants v⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a b := Subtype.ext (map_add _ a b)

/-- The additive monoid hom of the Galois descent is bijective. -/
lemma unitsInvAddHom_bijective :
    Function.Bijective (unitsInvAddHom (K := K) (M := M) (E := E)) := by
  constructor
  · intro a b h
    have h' : (Units.map (algebraMap M E).toMonoidHom).toAdditive a
        = (Units.map (algebraMap M E).toMonoidHom).toAdditive b := congrArg Subtype.val h
    have h1 : Additive.ofMul (Units.map (algebraMap M E).toMonoidHom (Additive.toMul a))
        = Additive.ofMul (Units.map (algebraMap M E).toMonoidHom (Additive.toMul b)) := by
      simpa using h'
    have h2 : Units.map (algebraMap M E).toMonoidHom (Additive.toMul a)
        = Units.map (algebraMap M E).toMonoidHom (Additive.toMul b) := Additive.ofMul.injective h1
    exact Additive.ofMul.injective
      (Units.map_injective (f := (algebraMap M E).toMonoidHom) (RingHom.injective _) h2)
  · intro x
    have hx' : ∀ h : ↥(rN K M E),
        (urep K E).ρ (h : E ≃ₐ[K] E) (Additive.ofMul (Additive.toMul x.val))
          = Additive.ofMul (Additive.toMul x.val) := by
      intro h
      simpa using (x.2 h : ((urep K E).ρ.comp (rN K M E).subtype) h x.val = x.val)
    obtain ⟨v, hv⟩ := (units_mem_invariants_iff (Additive.toMul x.val)).1 hx'
    refine ⟨Additive.ofMul v, Subtype.ext ?_⟩
    change (Units.map (algebraMap M E).toMonoidHom).toAdditive (Additive.ofMul v) = x.val
    rw [show (Units.map (algebraMap M E).toMonoidHom).toAdditive (Additive.ofMul v)
        = Additive.ofMul (Units.map (algebraMap M E).toMonoidHom v) from rfl, hv]
    rfl

/-- The linear map underlying the Galois descent `Mˣ → (Eˣ)^{Gal(E/M)}`. -/
noncomputable def unitsInvLinearMap :
    Additive Mˣ →ₗ[NK.HassePrinciple.CoeffInt.{0}]
      Representation.invariants ((urep K E).ρ.comp (rN K M E).subtype) where
  toFun := (unitsInvAddHom (K := K) (M := M) (E := E)).toFun
  map_add' := (unitsInvAddHom (K := K) (M := M) (E := E)).map_add'
  map_smul' c x := by
    apply Subtype.ext
    change (Units.map (algebraMap M E).toMonoidHom).toAdditive (c • x)
      = c • (Units.map (algebraMap M E).toMonoidHom).toAdditive x
    rw [ULift.smul_def, ULift.smul_def]
    exact (Units.map (algebraMap M E).toMonoidHom).toAdditive.map_zsmul c.down x

/-- The `CoeffInt`-linear equivalence `Mˣ ≅ (Eˣ)^{Gal(E/M)}` of the Galois descent. -/
noncomputable def unitsInvLinearEquiv :
    Additive Mˣ ≃ₗ[NK.HassePrinciple.CoeffInt.{0}]
      Representation.invariants ((urep K E).ρ.comp (rN K M E).subtype) :=
  LinearEquiv.ofBijective (unitsInvLinearMap (K := K) (M := M) (E := E))
    (unitsInvAddHom_bijective (K := K) (M := M) (E := E))

/-- The units inclusion commutes with the Galois action: for `σ : Gal(E/K)`,
`σ • (units map) = (units map) (σ|_M • ·)`. -/
lemma units_map_smul_restrict (σ : E ≃ₐ[K] E) (w : Mˣ) :
    σ • (Units.map (algebraMap M E).toMonoidHom w)
      = Units.map (algebraMap M E).toMonoidHom ((σ.restrictNormal M) • w) := by
  apply Units.ext
  simp only [AlgEquiv.smul_units_def, Units.coe_map]
  exact (AlgEquiv.restrictNormal_commutes σ M (w : M)).symm

/-- Reducing a representative of `Gal(E/K) ⧸ Gal(E/M)` along `rQuot`. -/
lemma restrictNormalHom_of_mk'_eq (g : M ≃ₐ[K] M) (g' : E ≃ₐ[K] E)
    (hg' : QuotientGroup.mk' (rN K M E) g' = (rQuot K M E).symm g) :
    AlgEquiv.restrictNormalHom (K₁ := E) (E := M) g' = g := by
  have h1 : (rQuot K M E) (QuotientGroup.mk' (rN K M E) g')
      = AlgEquiv.restrictNormalHom (K₁ := E) (E := M) g' := by
    have h := congrArg (fun f => f g') (rQuot_comp_mk' (K := K) (M := M) (E := E))
    simpa using h
  rw [← h1, hg', MulEquiv.apply_symm_apply]

/-- The value of the descent equivalence. -/
lemma unitsInvLinearEquiv_apply_val (v : Additive Mˣ) :
    (unitsInvLinearEquiv (K := K) (M := M) (E := E) v).1
      = (Units.map (algebraMap M E).toMonoidHom).toAdditive v := rfl

/-- The equivariance of the Galois descent. -/
lemma unitsDescent_equivariance (g : M ≃ₐ[K] M) (v : Additive Mˣ) :
    unitsInvLinearEquiv (K := K) (M := M) (E := E) ((urep K M).ρ g v)
      = ((urep K E).quotientToInvariants (rN K M E)).ρ ((rQuot K M E).symm g)
          (unitsInvLinearEquiv (K := K) (M := M) (E := E) v) := by
  obtain ⟨g', hg'⟩ := QuotientGroup.mk'_surjective (rN K M E) ((rQuot K M E).symm g)
  have hg'' : AlgEquiv.restrictNormalHom (K₁ := E) (E := M) g' = g :=
    restrictNormalHom_of_mk'_eq g g' hg'
  have hQ := Commons.RepresentationTheory.GroupCohomology.quotientToInvariants_rho_apply
    (S := rN K M E) (A := urep K E) g' (unitsInvLinearEquiv (K := K) (M := M) (E := E) v)
  apply Subtype.ext
  rw [← hg']
  rw [hQ, unitsInvLinearEquiv_apply_val, unitsInvLinearEquiv_apply_val]
  rw [show (urep K M).ρ g v = Additive.ofMul (g • Additive.toMul v) from rfl]
  rw [show (Units.map (algebraMap M E).toMonoidHom).toAdditive
        (Additive.ofMul (g • Additive.toMul v))
      = Additive.ofMul (Units.map (algebraMap M E).toMonoidHom (g • Additive.toMul v)) from rfl]
  rw [show (Units.map (algebraMap M E).toMonoidHom).toAdditive v
      = Additive.ofMul (Units.map (algebraMap M E).toMonoidHom (Additive.toMul v)) from rfl]
  change Additive.ofMul ((Units.map (algebraMap M E).toMonoidHom) (g • Additive.toMul v))
      = Additive.ofMul (g' • (Units.map (algebraMap M E).toMonoidHom (Additive.toMul v)))
  rw [units_map_smul_restrict]
  rw [show (g'.restrictNormal M) = g from hg'']

/-! ## The descent isomorphism of level cohomology -/

/-- The descent isomorphism `H²(Gal(M/K), Mˣ) ≅ H²(Gal(E/K) ⧸ Gal(E/M), (Eˣ)^{Gal(E/M)})`. -/
noncomputable def unitsDescentIso :
    groupCohomology (urep K M) 2 ≅
      groupCohomology ((urep K E).quotientToInvariants (rN K M E)) 2 :=
  groupCohomology.mapIso ((rQuot K M E).symm)
    (unitsInvLinearEquiv (K := K) (M := M) (E := E))
    (fun g => by
      apply LinearMap.ext
      intro v
      exact unitsDescent_equivariance (K := K) (M := M) (E := E) g v) 2

/-- The restriction isomorphism `H²(Gal(E/M), Eˣ) ≅ H²(ker (Gal(E/K) →* Gal(M/K)), Eˣ)` along the
canonical identification `Gal(E/M) ≃* ker (Gal(E/K) →* Gal(M/K))`. -/
noncomputable def resIso :
    groupCohomology (urep M E) 2 ≅
      groupCohomology (Rep.res (rN K M E).subtype (urep K E)) 2 :=
  groupCohomology.mapIso (galEquivRhn (K := K) (M := M) (E := E))
    (LinearEquiv.refl _ _) (fun g => by
      apply LinearMap.ext
      intro v
      show (urep M E).ρ g v
        = (urep K E).ρ (NK.CFTLib.HRclean.ARL.inclMK (K := K) (M := M) (E := E) g) v
      rfl) 2

/-- The restriction is the inverse of the quotient isomorphism. -/
lemma inclMK_comp_galEquivRhn_symm :
    (NK.CFTLib.HRclean.ARL.inclMK (K := K) (M := M) (E := E)).comp
        (galEquivRhn (K := K) (M := M) (E := E)).symm
      = (rN K M E).subtype := by
  ext s
  exact rfl

/-- The quotient inverse of the restriction: `rQuot.symm ∘ restrictNormalHom = mk'`. -/
lemma rQuot_symm_comp_restrictNormalHom :
    (rQuot K M E).symm.toMonoidHom.comp (AlgEquiv.restrictNormalHom (K₁ := E) (E := M))
      = QuotientGroup.mk' (rN K M E) := by
  ext σ
  show (rQuot K M E).symm (AlgEquiv.restrictNormalHom (K₁ := E) (E := M) σ)
    = QuotientGroup.mk' (rN K M E) σ
  have h := congrArg (fun f => f σ) (rQuot_comp_mk' (K := K) (M := M) (E := E))
  rw [show AlgEquiv.restrictNormalHom (K₁ := E) (E := M) σ
      = (rQuot K M E) (QuotientGroup.mk' (rN K M E) σ) from h.symm]
  exact MulEquiv.symm_apply_apply (rQuot K M E) (QuotientGroup.mk' (rN K M E) σ)

/-- **Restriction comparison.** -/
theorem resToGal_comp_resIso_hom :
    (NK.CFTLib.HRclean.Cheb.resToGal K M E) ≫ (resIso (K := K) (M := M) (E := E)).hom =
      (groupCohomology.resNatTrans NK.HassePrinciple.CoeffInt.{0} (G := rN K M E)
        (H := E ≃ₐ[K] E) (rN K M E).subtype 2).app (urep K E) := by
  rw [NK.CFTLib.HRclean.Cheb.resToGal, groupCohomology.resNatTrans_app, resIso,
    groupCohomology.mapIso_hom]
  rw [← groupCohomology.map_comp]
  apply groupCohomology.map_congr
    (NK.CFTLib.HRclean.T3.inclMK_comp_galEquivRhn_symm (K := K) (M := M) (E := E))
  rw [Rep.hom_comp_toLinearMap, Rep.resMap_hom_toLinearMap]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, Rep.hom_id, Rep.hom_ofHom]
  rfl

/-- **Inflation comparison.** -/
theorem unitsDescentIso_inv_comp_inflation :
    (unitsDescentIso (K := K) (M := M) (E := E)).inv
        ≫ (NK.CFTLib.HRclean.ARL.inflation (K := K) (L := M) (E := E)) =
      (groupCohomology.infNatTrans NK.HassePrinciple.CoeffInt.{0} (rN K M E) 2).app
        (urep K E) := by
  rw [unitsDescentIso, groupCohomology.mapIso_inv]
  rw [NK.CFTLib.HRclean.DescentInf.inflation_eq_unitsLevelMapTower (K := K) (L := M) (E := E),
    NK.NUV2.LC.unitsLevelMapTower]
  rw [← groupCohomology.map_comp]
  rw [show (groupCohomology.infNatTrans NK.HassePrinciple.CoeffInt.{0} (rN K M E) 2).app
        (urep K E)
      = groupCohomology.map (QuotientGroup.mk' (rN K M E))
          (Rep.ofHom ((urep K E).ρ.quotientToInvariants_lift (rN K M E))) 2 from rfl]
  apply groupCohomology.map_congr
    (NK.CFTLib.HRclean.T3.rQuot_symm_comp_restrictNormalHom (K := K) (M := M) (E := E))
  rw [Rep.hom_comp_toLinearMap, Rep.resMap_hom_toLinearMap]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, Rep.hom_ofHom]
  change (Units.map (algebraMap M E).toMonoidHom).toAdditive
      ((unitsInvLinearEquiv (K := K) (M := M) (E := E)).symm x)
    = (Submodule.subtype
        (Representation.invariants ((urep K E).ρ.comp (rN K M E).subtype))) x
  rw [← unitsInvLinearEquiv_apply_val (K := K) (M := M) (E := E)
    ((unitsInvLinearEquiv (K := K) (M := M) (E := E)).symm x)]
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- **The descent (re-gluing) step of the Brauer transfer.**

For a tower `K ⊆ M ⊆ E` of finite Galois extensions of number fields, a class
`α ∈ H²(Gal(E/K), Eˣ)` in the kernel of the restriction
`resToGal : H²(Gal(E/K), Eˣ) → H²(Gal(E/M), Eˣ)` comes from the level `M/K`: there is
`β ∈ H²(Gal(M/K), Mˣ)` with `inflation β = α`.

This is the inclusion `ker(res) ⊆ range(inf)` of the inflation–restriction exactness in degree `2`
for the normal subgroup `H = Gal(E/M) ≤ Gal(E/K)` with coefficients `Eˣ` in the coefficient ring
`ULift ℤ`, combined with the identification of the source `H²(G/H, (Eˣ)^H)` with
`H²(Gal(M/K), Mˣ)` (Galois descent for the units of the fixed field). -/
theorem exists_inflation_eq_of_resToGal_eq_zero {K M E : Type} [Field K] [NumberField K]
    [Field M] [NumberField M] [Field E] [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E]
    [IsScalarTower K M E] [FiniteDimensional K M] [FiniteDimensional K E] [IsGalois K M]
    [IsGalois K E] [IsGalois M E]
    (α : groupCohomology (NK.HassePrinciple.unitsRep K E) 2)
    (h : (NK.CFTLib.HRclean.Cheb.resToGal K M E).hom α = 0) :
    ∃ β : groupCohomology (NK.HassePrinciple.unitsRep K M) 2,
      (NK.CFTLib.HRclean.ARL.inflation (K := K) (L := M) (E := E)).hom β = α := by
  have hS1 : Subsingleton (groupCohomology
      (Rep.res (rN K M E).subtype (urep K E)) 1) :=
    subsingleton_H1_res_rn (K := K) (M := M) (E := E)
  have hrange := Commons.RepresentationTheory.GroupCohomology.range_infNatTrans_eq_ker_resNatTrans_of_subsingleton
    (k := NK.HassePrinciple.CoeffInt.{0}) (G := E ≃ₐ[K] E) (rN K M E) (urep K E)
    (r := 2) (by norm_num) (fun j hj hjr => by
      have hj1 : j = 1 := by omega
      subst hj1
      exact hS1)
  have hker : ((groupCohomology.resNatTrans NK.HassePrinciple.CoeffInt.{0} (G := rN K M E)
        (H := E ≃ₐ[K] E) (rN K M E).subtype 2).app (urep K E)).hom α = 0 := by
    have hc := congrArg (fun f => f.hom α) (resToGal_comp_resIso_hom (K := K) (M := M) (E := E))
    simp only [ConcreteCategory.comp_apply, h, map_zero] at hc
    exact hc.symm
  have hmem : α ∈ LinearMap.range (((groupCohomology.infNatTrans NK.HassePrinciple.CoeffInt.{0}
      (rN K M E) 2).app (urep K E))).hom := by
    rw [hrange]
    exact hker
  obtain ⟨γ, hγ⟩ := hmem
  refine ⟨(unitsDescentIso (K := K) (M := M) (E := E)).inv.hom γ, ?_⟩
  have hBapp : (NK.CFTLib.HRclean.ARL.inflation (K := K) (L := M) (E := E)).hom
      ((unitsDescentIso (K := K) (M := M) (E := E)).inv.hom γ)
      = ((groupCohomology.infNatTrans NK.HassePrinciple.CoeffInt.{0} (rN K M E) 2).app
          (urep K E)).hom γ := by
    have hc := congrArg (fun f => f.hom γ)
      (unitsDescentIso_inv_comp_inflation (K := K) (M := M) (E := E))
    simp only [ConcreteCategory.comp_apply] at hc
    exact hc
  exact hBapp.trans hγ

end NK.CFTLib.HRclean.T3

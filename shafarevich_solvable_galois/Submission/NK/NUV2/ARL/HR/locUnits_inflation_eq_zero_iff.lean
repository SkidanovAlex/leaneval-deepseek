import Mathlib
import Submission.NK.NUV2.ARL.HR.TransferSupport
import Submission.NK.CFTLib.IdeleHasse.Descent.transferCore
import Submission.NK.GlobalCFTdeep.HasseNormTheorem
import Submission.NK.HassePrinciple.localRingEquiv_localAlgebraMapUnits_of_restrict
import Submission.NK.HassePrinciple.liesOver_smul_of_restrict
import Submission.NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique
import Submission.NK.CFTLib.Existence.normIdeleHom_coset_aux
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The localisation of the inflation: `loc_ŵ(inf β) = 0 ↔ loc_w β = 0`

For a tower `K ⊆ M ⊆ E` of Galois number fields, a place `w` of `M` and a place `ŵ` of `E` over
`w`, and a class `β ∈ H²(Gal(M/K), Mˣ)`, the localisation at `ŵ` of the inflation of `β` vanishes
if and only if the localisation of `β` at `w` vanishes.
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open NK.GlobalCFT CategoryTheory

namespace NK.NUV2.ARL.HR

variable {K M E : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E]
  [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E]
  [FiniteDimensional K M] [FiniteDimensional K E] [IsGalois K M] [IsGalois K E] [IsGalois M E]

/-! ## Casting `localAlgebraMapUnits` at both places -/

/-- Transporting `localAlgebraMapUnits` along equalities of the big place and of the small place. -/
lemma localAlgebraMapUnits_cast_tower'' {a a' : NK.GlobalCFT.Place E} {b b' : NK.GlobalCFT.Place M}
    (h1 : a = a') (h2 : b = b') (Ha : NK.GlobalCFT.Place.LiesOver a b)
    (H : NK.GlobalCFT.Place.LiesOver a' b') (x : (NK.GlobalCFT.Place.localField M b)ˣ) :
    h1 ▸ (NK.GlobalCFT.Place.localAlgebraMapUnits a b Ha x)
      = NK.GlobalCFT.Place.localAlgebraMapUnits a' b' H (h2 ▸ x) := by
  cases h1
  exact NK.HassePrinciple.localAlgebraMapUnits_cast _ h2 Ha H x

/-! ## The restriction of decomposition groups -/

/-- **The restriction map on decomposition groups**: an automorphism of `E` over `K` fixing the
place `ŵ` restricts to an automorphism of `M` over `K` fixing the place `w` below it. -/
noncomputable def stabRestrict (w : NK.GlobalCFT.Place M) (ŵ : NK.GlobalCFT.Place E)
    (hw : NK.GlobalCFT.Place.LiesOver ŵ w) :
    MulAction.stabilizer Gal(E/K) ŵ →* MulAction.stabilizer Gal(M/K) w where
  toFun σ := ⟨restrictHom (K := K) (L := M) (E := E) σ.1, by
    rw [MulAction.mem_stabilizer_iff]
    have h1 := NK.HassePrinciple.liesOver_smul_of_restrict (K := K) (F := M) (L := E) σ.1
      (restrictHom (K := K) (L := M) (E := E) σ.1) (fun y => restrictHom_apply_coe σ.1 y) hw
    rw [MulAction.mem_stabilizer_iff.mp σ.2] at h1
    exact NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique h1 hw⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' σ τ := Subtype.ext (map_mul _ σ.1 τ.1)

@[simp] theorem stabRestrict_coe (w : NK.GlobalCFT.Place M) (ŵ : NK.GlobalCFT.Place E)
    (hw : NK.GlobalCFT.Place.LiesOver ŵ w) (σ : MulAction.stabilizer Gal(E/K) ŵ) :
    ((stabRestrict (K := K) (M := M) (E := E) w ŵ hw σ : MulAction.stabilizer Gal(M/K) w) :
        Gal(M/K)) = restrictHom (K := K) (L := M) (E := E) σ.1 := rfl

theorem stabRestrict_comp_subtype (w : NK.GlobalCFT.Place M) (ŵ : NK.GlobalCFT.Place E)
    (hw : NK.GlobalCFT.Place.LiesOver ŵ w) :
    (MulAction.stabilizer Gal(M/K) w).subtype.comp (stabRestrict (K := K) (M := M) (E := E) w ŵ hw)
      = (restrictHom (K := K) (L := M) (E := E)).comp
          (MulAction.stabilizer Gal(E/K) ŵ).subtype :=
  MonoidHom.ext fun _ => rfl

/-! ## The equivariance of the local coefficient map -/

theorem localUnitsEquiv_localCoeff (w : NK.GlobalCFT.Place M) (ŵ : NK.GlobalCFT.Place E)
    (hw : NK.GlobalCFT.Place.LiesOver ŵ w)
    (σ : MulAction.stabilizer Gal(E/K) ŵ) (u : (NK.GlobalCFT.Place.localField M w)ˣ) :
    NK.GlobalCFT.Place.localAlgebraMapUnits ŵ w hw
        (NK.HassePrinciple.localUnitsEquiv w
          (stabRestrict (K := K) (M := M) (E := E) w ŵ hw σ) u)
      = NK.HassePrinciple.localUnitsEquiv ŵ σ
          (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ w hw u) := by
  have hσ : σ.1 • ŵ = ŵ := MulAction.mem_stabilizer_iff.mp σ.2
  have hσ' : (restrictHom (K := K) (L := M) (E := E) σ.1) • w = w :=
    MulAction.mem_stabilizer_iff.mp
      (stabRestrict (K := K) (M := M) (E := E) w ŵ hw σ).2
  have hlies : (σ.1 • ŵ).LiesOver ((restrictHom (K := K) (L := M) (E := E) σ.1) • w) :=
    NK.HassePrinciple.liesOver_smul_of_restrict (K := K) (F := M) (L := E) σ.1
      (restrictHom (K := K) (L := M) (E := E) σ.1) (fun y => restrictHom_apply_coe σ.1 y) hw
  have hL : NK.HassePrinciple.localUnitsEquiv w
        (stabRestrict (K := K) (M := M) (E := E) w ŵ hw σ) u
      = hσ' ▸ (Units.map (NK.GlobalCFT.Place.localRingEquiv
          (restrictHom (K := K) (L := M) (E := E) σ.1) w).toMonoidHom u) := by
    apply Units.ext
    rw [NK.HassePrinciple.coe_localUnitsEquiv]
    rw [show (NK.HassePrinciple.localAutHom w)
        (stabRestrict (K := K) (M := M) (E := E) w ŵ hw σ)
          = NK.HassePrinciple.localAut w
              (stabRestrict (K := K) (M := M) (E := E) w ŵ hw σ) from rfl]
    rw [NK.HassePrinciple.localAut_apply,
      NK.HassePrinciple.units_val_cast, NK.HassePrinciple.ringEquiv_cast_apply_eq]
    rfl
  have hR : NK.HassePrinciple.localUnitsEquiv ŵ σ
        (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ w hw u)
      = hσ ▸ (Units.map (NK.GlobalCFT.Place.localRingEquiv σ.1 ŵ).toMonoidHom
          (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ w hw u)) := by
    apply Units.ext
    rw [NK.HassePrinciple.coe_localUnitsEquiv]
    rw [show (NK.HassePrinciple.localAutHom ŵ) σ
        = NK.HassePrinciple.localAut ŵ σ from rfl]
    rw [NK.HassePrinciple.localAut_apply,
      NK.HassePrinciple.units_val_cast, NK.HassePrinciple.ringEquiv_cast_apply_eq]
    rfl
  have key := NK.HassePrinciple.localRingEquiv_localAlgebraMapUnits_of_restrict
    (K := K) (F := M) (L := E) σ.1 (restrictHom (K := K) (L := M) (E := E) σ.1)
    (fun y => restrictHom_apply_coe σ.1 y) hw hlies u
  rw [hL, hR, key, ← localAlgebraMapUnits_cast_tower'' hσ hσ' hlies hw
    (x := Units.map (NK.GlobalCFT.Place.localRingEquiv
      (restrictHom (K := K) (L := M) (E := E) σ.1) w).toMonoidHom u)]

/-! ## The local coefficient map -/

/-- The local units map `M_wˣ →* E_ŵˣ` as a morphism of `Γ_ŵ`-representations, where `M_wˣ` carries
the `Γ_ŵ`-action through `stabRestrict`. -/
noncomputable def localCoeff (w : NK.GlobalCFT.Place M) (ŵ : NK.GlobalCFT.Place E)
    (hw : NK.GlobalCFT.Place.LiesOver ŵ w) :
    Rep.res (stabRestrict (K := K) (M := M) (E := E) w ŵ hw)
        (NK.HassePrinciple.localUnitsRep K M w) ⟶
      NK.HassePrinciple.localUnitsRep K E ŵ :=
  Rep.ofHom
    { toFun := ⇑(NK.GlobalCFT.Place.localAlgebraMapUnits ŵ w hw).toAdditive
      map_add' := fun x y =>
        map_add (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ w hw).toAdditive x y
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        exact AddMonoidHom.map_zsmul
          (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ w hw).toAdditive z x
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ w hw
            (NK.HassePrinciple.localUnitsEquiv w
              (stabRestrict (K := K) (M := M) (E := E) w ŵ hw σ) (Additive.toMul x)))
          = Additive.ofMul (NK.HassePrinciple.localUnitsEquiv ŵ σ
              (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ w hw (Additive.toMul x)))
        congr 1
        exact localUnitsEquiv_localCoeff (K := K) (M := M) (E := E) w ŵ hw σ (Additive.toMul x) }

@[simp] theorem localCoeff_ofMul (w : NK.GlobalCFT.Place M) (ŵ : NK.GlobalCFT.Place E)
    (hw : NK.GlobalCFT.Place.LiesOver ŵ w) (u : (NK.GlobalCFT.Place.localField M w)ˣ) :
    (localCoeff (K := K) (M := M) (E := E) w ŵ hw).hom (Additive.ofMul u)
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits ŵ w hw u) := rfl

/-! ## The local level map -/

/-- **The local level map** `H²(Γ_w, M_wˣ) → H²(Γ_ŵ, E_ŵˣ)`: the restriction of the decomposition
groups `Γ_ŵ → Γ_w` together with the local coefficient map `M_wˣ → E_ŵˣ`. -/
noncomputable def localLevelMap (w : NK.GlobalCFT.Place M) (ŵ : NK.GlobalCFT.Place E)
    (hw : NK.GlobalCFT.Place.LiesOver ŵ w) :
    groupCohomology (NK.HassePrinciple.localUnitsRep K M w) 2 ⟶
      groupCohomology (NK.HassePrinciple.localUnitsRep K E ŵ) 2 :=
  groupCohomology.map (stabRestrict (K := K) (M := M) (E := E) w ŵ hw)
    (localCoeff (K := K) (M := M) (E := E) w ŵ hw) 2

/-! ## The naturality square -/

section Square

variable (w : NK.GlobalCFT.Place M) (ŵ : NK.GlobalCFT.Place E)
  (hw : NK.GlobalCFT.Place.LiesOver ŵ w)

theorem unitsInclRep_ofMul (u : Mˣ) :
    (unitsInclRep (K := K) (L := M) (E := E)).hom (Additive.ofMul u)
      = Additive.ofMul (Units.map (algebraMap M E).toMonoidHom u) := rfl

/-- **The naturality square**: the localisation at `ŵ` of the inflation of a class over the level
`M` is the local level map applied to the localisation of the class at `w`. -/
theorem locUnits_inflation_eq :
    (NK.NUV2.ARL.HR.inflation (K := K) (L := M) (E := E)) ≫
        (NK.HassePrinciple.locUnits K E ŵ)
      = (NK.HassePrinciple.locUnits K M w) ≫
        (localLevelMap (K := K) (M := M) (E := E) w ŵ hw) := by
  simp only [NK.HassePrinciple.locUnits, NK.NUV2.ARL.HR.inflation, localLevelMap,
    groupCohomology.resNatTrans_app]
  rw [NK.NUV2.LC.RouteB.map_id_comp_apply]
  rw [NK.NUV2.LC.RouteB.map_id_comp_apply]
  rw [← groupCohomology.map_comp (f := restrictHom (K := K) (L := M) (E := E))
        (g := (MulAction.stabilizer Gal(E/K) ŵ).subtype)
        (unitsInclRep (K := K) (L := M) (E := E))
        (NK.HassePrinciple.unitsToLocalUnits K E ŵ)]
  rw [← groupCohomology.map_comp
        (f := (MulAction.stabilizer Gal(M/K) w).subtype)
        (g := stabRestrict (K := K) (M := M) (E := E) w ŵ hw)
        (NK.HassePrinciple.unitsToLocalUnits K M w)
        (localCoeff (K := K) (M := M) (E := E) w ŵ hw)]
  refine groupCohomology.map_congr
    (G := MulAction.stabilizer Gal(E/K) ŵ) (H := Gal(M/K))
    (A := NK.HassePrinciple.unitsRep K M)
    (B := NK.HassePrinciple.localUnitsRep K E ŵ)
    (f := (restrictHom (K := K) (L := M) (E := E)).comp
      (MulAction.stabilizer Gal(E/K) ŵ).subtype)
    (g := (MulAction.stabilizer Gal(M/K) w).subtype.comp
      (stabRestrict (K := K) (M := M) (E := E) w ŵ hw))
    (stabRestrict_comp_subtype (K := K) (M := M) (E := E) w ŵ hw).symm ?_ 2
  ext x
  conv_lhs => rw [← ofMul_toMul x]
  conv_rhs => rw [← ofMul_toMul x]
  simp only [Rep.hom_comp_toLinearMap, Rep.resMap_hom_toLinearMap, LinearMap.comp_apply,
    LinearMap.id_apply, Rep.hom_id, Representation.IntertwiningMap.toLinearMap_apply,
    Representation.IntertwiningMap.id_apply,
    NK.NUV2.LC.RouteB.unitsToLocalUnits_hom_ofMul, unitsInclRep_ofMul, localCoeff_ofMul]
  have hcomp := NK.CFTLib.Existence.localAlgebraMapUnits_comp_units_algebraMap
    (K := K) (E := M) (L := E) ŵ w hw
  exact (DFunLike.congr_fun hcomp (Additive.toMul x)).symm

end Square

end NK.NUV2.ARL.HR

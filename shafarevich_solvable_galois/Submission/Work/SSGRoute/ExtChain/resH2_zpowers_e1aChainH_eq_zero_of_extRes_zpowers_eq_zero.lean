import Mathlib
import Submission.Work.SSGRoute.ExtChain.ChainGamma
import Submission.Work.SSGRoute.PT.e1a_can_chain
import Submission.Work.SSGRoute.PT.resH2
import Submission.Work.SSGRoute.PT.e1a_shift
import Submission.Work.SSGRoute.ExtChain.homCoindFreeT_H1_subgroup
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ExtChain.deltaH2_restriction
import Submission.Work.SSGRoute.E1cGeneric.Canonical
import Submission.Work.SSGRoute.ExtChain.ext_shift_natural_res
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1

set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
variable {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]

/-! ## Auxiliary: the additive map `Kˣ →+ Ωˣ` on the `Additive` carriers -/

/-- The additive map on the `Additive`-wrapped carriers induced by `(↥K)ˣ → Ωˣ`. -/
def unitsAddToOmega : (unitsK k K).V →+ Additive Ωˣ where
  toFun u := Additive.ofMul (unitsMapK (Additive.toMul u))
  map_zero' := by rw [Work.SSGRoute.toMul_zero_K, map_one, ofMul_one]
  map_add' a b := by rw [Work.SSGRoute.toMul_add_K, map_mul, ofMul_mul]

theorem unitsAddToOmega_apply (u : (unitsK k K).V) :
    unitsAddToOmega (k := k) (Ω := Ω) (K := K) u
      = Additive.ofMul (unitsMapK (Additive.toMul u)) := rfl

/-- The `Γ`-action on the `Ωˣ`-valued module is the `K`-Galois action on the `Kˣ`-valued one. -/
theorem smul_unitsAddToOmega (σ : Ω ≃ₐ[k] Ω) (u : (unitsK k K).V) :
    σ • (unitsAddToOmega (k := k) (Ω := Ω) (K := K) u)
      = unitsAddToOmega (k := k) (Ω := Ω) (K := K)
          ((unitsK k K).ρ (SSGRoute.res k K σ) u) := by
  rw [unitsAddToOmega_apply, unitsAddToOmega_apply, Work.SSGRoute.toMul_rho_unitsK]
  rw [show σ • (Additive.ofMul (unitsMapK (Additive.toMul u)))
        = Additive.ofMul (unitsMapΩ σ (unitsMapK (Additive.toMul u))) from rfl,
    Work.SSGRoute.unitsMapΩ_unitsMapK]

/-- The conjugation action on `Hom_ℤ(F,Ωˣ)` in the shape of `homCoind.smul_apply`. -/
theorem smul_conj_homCoindFreeT (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (σ : Ω ≃ₐ[k] Ω)
    (Φ : E1cN (k := k) (Ω := Ω) (K := K) R) (v : (E1cF R).V) :
    ((homCoind.instDistribMulActionAlgEquiv (E1cF R)).smul σ Φ) v
      = homCoind.smulHom (k := k) (Ω := Ω) σ
          (Φ ((E1cF R).ρ (SSGRoute.res k K σ)⁻¹ v)) := rfl

/-! ## Auxiliary: `Ext.mk₀` is the inverse of `Ext.addEquiv₀` -/

theorem addEquiv₀_mk₀ {C : Type*} [Category* C] [Abelian C] [HasExt C] {X Y : C}
    (f : X ⟶ Y) : Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ f) = f := by
  show Abelian.Ext.homEquiv₀ (Abelian.Ext.mk₀ f) = f
  rw [← Abelian.Ext.homEquiv₀_symm_apply f]
  exact Equiv.apply_symm_apply _ _

/-! ## Auxiliary: restriction of the syzygy shift -/

/-- **If the restriction of the syzygy-shift of `z` to a subgroup vanishes, then so does the
restriction of `z`.** -/
theorem extRes_eq_zero_of_extRes_shift_eq_zero {G : Type} [Group G] (D : Subgroup G)
    (S : ShortComplex (Rep.{0} Coeff G)) (hS : S.ShortExact)
    [Projective S.X₂] (Y : Rep.{0} Coeff G) (z : Abelian.Ext.{0} S.X₁ Y 1)
    (h : SSGRoute.PTExt.extRes D.subtype
      (Work.SSGRoute.PT.e1aShiftEquiv S hS Y 1 (le_refl 1) z) = 0) :
    SSGRoute.PTExt.extRes D.subtype z = 0 := by
  let F : Rep.{0} Coeff G ⥤ Rep.{0} Coeff ↥D := Rep.resFunctor D.subtype
  haveI : Projective (S.map F).X₂ := Functor.projective_obj F S.X₂
  have hSD : (S.map F).ShortExact := hS.map_of_exact F
  have hnat : ∀ (hh : 1 + 1 = 1 + 1),
      (hS.extClass.comp z hh).mapExactFunctor F = hSD.extClass.comp (z.mapExactFunctor F) hh :=
    fun hh => Work.SSGRoute.ExtChain.bijective_extClass_precomp_map F hS Y (le_refl 1) hh z
  have h1 : ∀ (hh : 1 + 1 = 1 + 1), (hS.extClass.comp z hh).mapExactFunctor F = 0 := by
    intro hh
    have h' := h
    rw [show Work.SSGRoute.PT.e1aShiftEquiv S hS Y 1 (le_refl 1) z
        = hS.extClass.comp z hh from
      Work.SSGRoute.PT.e1aShiftEquiv_apply hS Y 1 (le_refl 1) z] at h'
    exact h'
  have h2 : (Work.SSGRoute.PT.e1aShiftEquiv (S.map F) hSD (F.obj Y) 1 (le_refl 1))
      (z.mapExactFunctor F) = 0 := by
    rw [Work.SSGRoute.PT.e1aShiftEquiv_apply hSD (F.obj Y) 1 (le_refl 1)
      (z.mapExactFunctor F)]
    exact ((hnat (by omega : 1 + 1 = 1 + 1)).symm).trans (h1 (by omega : 1 + 1 = 1 + 1))
  have hgoal : z.mapExactFunctor F = 0 :=
    (Work.SSGRoute.PT.e1aShiftEquiv (S.map F) hSD (F.obj Y) 1 (le_refl 1)).injective
      (h2.trans ((Work.SSGRoute.PT.e1aShiftEquiv (S.map F) hSD (F.obj Y) 1
        (le_refl 1)).map_zero).symm)
  exact hgoal

/-! ## Auxiliary: `PhiE` is natural in the group -/

/-- `PhiE` commutes with restriction to a subgroup. -/
theorem extRes_PhiE (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (D : Subgroup (K ≃ₐ[k] K))
    (w : CategoryTheory.Abelian.Ext.{0} (E1cR1 R) (unitsK k K) 0) :
    SSGRoute.PTExt.extRes D.subtype (PhiE (k := k) (Ω := Ω) (K := K) R w)
      = Abelian.Ext.mapExactFunctor (Rep.resFunctor D.subtype)
          ((freeCoverSES_shortExact R).extClass.comp w (by norm_num : 1 + 0 = 1)) := rfl

/-! ## Auxiliary: applying a restricted morphism at a canonical syzygy generator -/

/-- The restricted kernel inclusion evaluates at a syzygy point through `kappa`. -/
theorem resMap_kernel_apply (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (D : Subgroup (K ≃ₐ[k] K)) (x : (E1cR1 R).V) :
    Rep.Hom.hom ((Rep.resFunctor D.subtype).map (Limits.kernel.ι (freeCover R))) x
      = kappa (k := k) (Ω := Ω) (K := K) R x := rfl

/-- The restriction of a class-morphism evaluates through the unrestricted one. -/
theorem resMap_addEquiv₀_apply (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (D : Subgroup (K ≃ₐ[k] K))
    (w : CategoryTheory.Abelian.Ext.{0} (E1cR1 R) (unitsK k K) 0) (x : (E1cR1 R).V) :
    Rep.Hom.hom ((Rep.resFunctor D.subtype).map (Abelian.Ext.addEquiv₀ w)) x
      = Rep.Hom.hom (Abelian.Ext.addEquiv₀ w) x := rfl

/-! ## Auxiliary: the equivariant lift of a `PhiE`-generator -/

/-- **If the restriction of the `PhiE`-generator of `w` to a subgroup `D` vanishes, then `w`
extends to a `D`-equivariant `Kˣ`-valued map on the canonical cover of `R`.** -/
theorem exists_lift_of_extRes_PhiE_eq_zero (R : Rep.{0} Coeff (K ≃ₐ[k] K))
    (D : Subgroup (K ≃ₐ[k] K))
    (w : CategoryTheory.Abelian.Ext.{0} (E1cR1 R) (unitsK k K) 0)
    (h : SSGRoute.PTExt.extRes D.subtype (PhiE (k := k) (Ω := Ω) (K := K) R w) = 0) :
    ∃ Φ : Rep.res D.subtype (E1cF R) ⟶ Rep.res D.subtype (unitsK k K),
      ∀ x : (E1cR1 R).V,
        Rep.Hom.hom Φ (kappa R x) = Rep.Hom.hom (Abelian.Ext.addEquiv₀ w) x := by
  classical
  haveI : Fintype (K ≃ₐ[k] K) := inferInstance
  let F : Rep.{0} Coeff (K ≃ₐ[k] K) ⥤ Rep.{0} Coeff ↥D := Rep.resFunctor D.subtype
  haveI : Projective ((freeCoverSES R).map F).X₂ :=
    Functor.projective_obj F (freeCoverSES R).X₂
  have hSD : ((freeCoverSES R).map F).ShortExact :=
    (freeCoverSES_shortExact R).map_of_exact F
  have h0 : Abelian.Ext.mapExactFunctor F
      ((freeCoverSES_shortExact R).extClass.comp w (by norm_num : 1 + 0 = 1)) = 0 := by
    rw [show ((freeCoverSES_shortExact R).extClass.comp w (by norm_num : 1 + 0 = 1))
        = ((freeCoverSES_shortExact R).extClass.precomp (unitsK k K)
            (by norm_num : 1 + 0 = 1)) w from rfl]
    exact h
  have hnat : ∀ (hh : 1 + 0 = 1),
      Abelian.Ext.mapExactFunctor F ((freeCoverSES_shortExact R).extClass.comp w hh)
        = hSD.extClass.comp (Abelian.Ext.mapExactFunctor F w) hh := by
    intro hh
    rw [Abelian.Ext.mapExactFunctor_comp F (freeCoverSES_shortExact R).extClass w hh,
      Abelian.Ext.mapExactFunctor_extClass F (freeCoverSES_shortExact R)]
    try rfl
  have h1 : hSD.extClass.comp (Abelian.Ext.mapExactFunctor F w)
      (by norm_num : 1 + 0 = 1) = 0 := by
    rw [← hnat (by norm_num : 1 + 0 = 1)]
    exact h0
  obtain ⟨Φ₀, hΦ₀⟩ := Abelian.Ext.contravariant_sequence_exact₁ hSD
    (F.obj (unitsK k K)) (Abelian.Ext.mapExactFunctor F w) (n₁ := 1)
    (by norm_num : 1 + 0 = 1) h1
  -- Work with an explicitly typed copy of `Φ₀`, so that all the goals below are stated in the
  -- reducible `F.map`-flavour (rather than in the `(freeCoverSES R).map F`-flavour).
  let Φ₁ : Abelian.Ext (F.obj (E1cF R)) (F.obj (unitsK k K)) 0 := Φ₀
  have hΦ₁ : (Abelian.Ext.mk₀ (F.map (Limits.kernel.ι (freeCover R)))).comp Φ₁ (zero_add 0)
      = Abelian.Ext.mapExactFunctor F w := hΦ₀
  refine ⟨Abelian.Ext.addEquiv₀ Φ₁, fun x => ?_⟩
  have hv₂ : Abelian.Ext.addEquiv₀ (Abelian.Ext.mapExactFunctor F w)
      = F.map (Abelian.Ext.addEquiv₀ w) := by
    have h1' : Abelian.Ext.mapExactFunctor F w
        = Abelian.Ext.mapExactFunctor F (Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ w)) := by
      rw [Abelian.Ext.mk₀_addEquiv₀_apply w]
    rw [h1', Abelian.Ext.mapExactFunctor_mk₀]
    simp only [addEquiv₀_mk₀]
  have hm : F.map (Limits.kernel.ι (freeCover R)) ≫ Abelian.Ext.addEquiv₀ Φ₁
      = F.map (Abelian.Ext.addEquiv₀ w) := by
    have hstep : (Abelian.Ext.mk₀ (F.map (Limits.kernel.ι (freeCover R)))).comp Φ₁
          (zero_add 0)
        = (Abelian.Ext.mk₀ (F.map (Limits.kernel.ι (freeCover R)))).comp
            (Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ Φ₁)) (zero_add 0) := by
      rw [Abelian.Ext.mk₀_addEquiv₀_apply Φ₁]
    have hA2 : Abelian.Ext.mk₀ (F.map (Limits.kernel.ι (freeCover R))
          ≫ Abelian.Ext.addEquiv₀ Φ₁) = Abelian.Ext.mapExactFunctor F w := by
      rw [← hΦ₁, hstep, Abelian.Ext.mk₀_comp_mk₀]
    rw [← addEquiv₀_mk₀ (F.map (Limits.kernel.ι (freeCover R)) ≫ Abelian.Ext.addEquiv₀ Φ₁),
      hA2, hv₂]
  have h2 : Rep.Hom.hom (F.map (Limits.kernel.ι (freeCover R))
        ≫ Abelian.Ext.addEquiv₀ Φ₁) x
      = Rep.Hom.hom (F.map (Abelian.Ext.addEquiv₀ w)) x :=
    congrArg (fun φ : Rep.res D.subtype (E1cR1 R) ⟶ Rep.res D.subtype (unitsK k K) =>
      Rep.Hom.hom φ x) hm
  rw [Rep.comp_apply] at h2
  rw [show Rep.Hom.hom (F.map (Limits.kernel.ι (freeCover R))) x
      = kappa (k := k) (Ω := Ω) (K := K) R x from rfl] at h2
  rw [show Rep.Hom.hom (F.map (Abelian.Ext.addEquiv₀ w)) x
      = Rep.Hom.hom (Abelian.Ext.addEquiv₀ w) x from rfl] at h2
  exact h2

/-! ## Auxiliary: the conjugation action, seen through the `DistribMulAction` field

The `Γ`-module `E1cN R = Hom_ℤ(ℤ[G]^ι, Ωˣ)` is an abbreviation of `M.V →+ Additive Ωˣ`, so type
class search prefers Mathlib's *pointwise* action on `AddMonoidHom` over the conjugation action
(cf. `ExtChain/ChainGamma.lean`, `PT/homCoind_SES.lean`).  We therefore write the action as the
explicit field `(homCoind.instDistribMulActionAlgEquiv _).smul` and prove the handful of
computation rules in that shape. -/

/-- Additivity of an explicit `DistribMulAction` on a difference. -/
theorem dma_smul_sub {Γ A : Type} [Group Γ] [AddGroup A] (dma : DistribMulAction Γ A) (γ : Γ)
    (a b : A) : dma.smul γ (a - b) = dma.smul γ a - dma.smul γ b := by
  rw [show dma.smul γ (a - b) = γ • (a - b) from rfl,
    show dma.smul γ a = γ • a from rfl, show dma.smul γ b = γ • b from rfl]
  exact smul_sub γ a b

/-- Additivity of an explicit `DistribMulAction` on a sum. -/
theorem dma_smul_add {Γ A : Type} [Group Γ] [AddGroup A] (dma : DistribMulAction Γ A) (γ : Γ)
    (a b : A) : dma.smul γ (a + b) = dma.smul γ a + dma.smul γ b := by
  rw [show dma.smul γ (a + b) = γ • (a + b) from rfl,
    show dma.smul γ a = γ • a from rfl, show dma.smul γ b = γ • b from rfl]
  exact smul_add γ a b

/-- On `homCoind k Ω K R` the ambient action *is* the conjugation action. -/
theorem smul_homCoind_eq_algEquiv (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (γ : Ω ≃ₐ[k] Ω)
    (m : homCoind k Ω K R) :
    (γ • m : homCoind k Ω K R) = (homCoind.instDistribMulActionAlgEquiv R).smul γ m := by
  ext x
  simp only [homCoind.smul_apply]
  rfl

/-- `iotaH` is equivariant for the conjugation action, in the explicit-`.smul` shape. -/
theorem iotaH_algEquiv_smul (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (γ : Ω ≃ₐ[k] Ω)
    (m : homCoind k Ω K R) :
    iotaH (k := k) (Ω := Ω) (K := K) R ((homCoind.instDistribMulActionAlgEquiv R).smul γ m)
      = (homCoind.instDistribMulActionAlgEquiv (E1cF R)).smul γ
          (iotaH (k := k) (Ω := Ω) (K := K) R m) := by
  rw [← smul_homCoind_eq_algEquiv (k := k) (Ω := Ω) (K := K) R γ m]
  exact iotaH_equivariant (k := k) (Ω := Ω) (K := K) R γ m

/-- The coboundary of the subgroup `↥⟨σ⟩`, in the explicit-`.smul` shape. -/
theorem d0_zpowers_apply (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (σ : Ω ≃ₐ[k] Ω)
    (m : homCoind k Ω K R) (hh : ↥(Subgroup.zpowers σ)) :
    (Work.GroupCohomology.d0 (↥(Subgroup.zpowers σ)) (homCoind k Ω K R) m) hh
      = (homCoind.instDistribMulActionAlgEquiv R).smul (hh : Ω ≃ₐ[k] Ω) m - m := by
  rw [Work.GroupCohomology.d0_apply, Subgroup.smul_def,
    smul_homCoind_eq_algEquiv (k := k) (Ω := Ω) (K := K) R (hh : Ω ≃ₐ[k] Ω) m]

/-- A `Γ`-invariant element of `E1cN R` is fixed by the explicit conjugation action. -/
theorem algEquiv_smul_eq_of_mem_H0 (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (γ : Ω ≃ₐ[k] Ω)
    (z : E1cN (k := k) (Ω := Ω) (K := K) R)
    (hz : z ∈ Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω)
      (E1cN (k := k) (Ω := Ω) (K := K) R)) :
    (homCoind.instDistribMulActionAlgEquiv (E1cF R)).smul γ z = z :=
  (Work.GroupCohomology.mem_invariants (Ω ≃ₐ[k] Ω)
    (E1cN (k := k) (Ω := Ω) (K := K) R) z).mp hz γ

/-- An element of `E1cN R` fixed by the subgroup `↥⟨σ⟩` is fixed by the explicit action of `σ`. -/
theorem algEquiv_smul_eq_of_mem_H0_zpowers (R : Rep.{0} Coeff (K ≃ₐ[k] K)) (σ : Ω ≃ₐ[k] Ω)
    (z : E1cN (k := k) (Ω := Ω) (K := K) R)
    (hz : z ∈ Work.AbsoluteKummer.H0 (Subgroup.zpowers σ)
      (E1cN (k := k) (Ω := Ω) (K := K) R))
    (hh : ↥(Subgroup.zpowers σ)) :
    (homCoind.instDistribMulActionAlgEquiv (E1cF R)).smul (hh : Ω ≃ₐ[k] Ω) z = z := by
  have h := (Work.GroupCohomology.mem_invariants (↥(Subgroup.zpowers σ))
    (E1cN (k := k) (Ω := Ω) (K := K) R) z).mp hz hh
  rw [Subgroup.smul_def] at h
  exact h

/-- **The involution-level `B¹` computation.**  If `m` is a lift of `liftOf c - z' - Φ` where
`z'` is a `Γ`-invariant and `Φ` a `↥⟨σ⟩`-invariant element of `Hom_ℤ(ℤ[G]^ι, Ωˣ)`, then the
restriction of the cocycle `c` to `↥⟨σ⟩` is a coboundary. -/
theorem resZ1_zpowers_mem_B1 (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (σ : Ω ≃ₐ[k] Ω)
    (c : ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (homCoind k Ω K R)))
    (Φ : E1cN (k := k) (Ω := Ω) (K := K) R)
    (hΦinv : Φ ∈ Work.AbsoluteKummer.H0 (Subgroup.zpowers σ)
      (E1cN (k := k) (Ω := Ω) (K := K) R))
    (z' : ↥(Work.AbsoluteKummer.H0 (Ω ≃ₐ[k] Ω)
      (E1cN (k := k) (Ω := Ω) (K := K) R)))
    (m : homCoind k Ω K R)
    (hm : iotaH (k := k) (Ω := Ω) (K := K) R m
      = liftOf (k := k) (Ω := Ω) (K := K) R c - z'.1 - Φ) :
    ((Work.SSGRoute.PT.H2Fin.resZ1 (Subgroup.zpowers σ) (homCoind k Ω K R) c :
        Work.AbsoluteKummer.Z1 (↥(Subgroup.zpowers σ)) (homCoind k Ω K R)) :
      (↥(Subgroup.zpowers σ)) → homCoind k Ω K R)
      ∈ Work.AbsoluteKummer.B1 (↥(Subgroup.zpowers σ)) (homCoind k Ω K R) := by
  rw [Work.AbsoluteKummer.mem_B1_iff]
  refine ⟨m, ?_⟩
  funext hh
  apply iotaH_injective (k := k) (Ω := Ω) (K := K) R
  have h1 : iotaH (k := k) (Ω := Ω) (K := K) R
      ((Work.GroupCohomology.d0 (↥(Subgroup.zpowers σ)) (homCoind k Ω K R) m) hh)
      = (homCoind.instDistribMulActionAlgEquiv (E1cF R)).smul (hh : Ω ≃ₐ[k] Ω)
          (iotaH (k := k) (Ω := Ω) (K := K) R m)
        - iotaH (k := k) (Ω := Ω) (K := K) R m := by
    rw [d0_zpowers_apply (k := k) (Ω := Ω) (K := K) R σ m hh, map_sub]
    congr 1
    exact iotaH_algEquiv_smul (k := k) (Ω := Ω) (K := K) R (hh : Ω ≃ₐ[k] Ω) m
  rw [h1]
  have h2 : iotaH (k := k) (Ω := Ω) (K := K) R
      ((Work.SSGRoute.PT.H2Fin.resZ1 (Subgroup.zpowers σ) (homCoind k Ω K R) c :
          (↥(Subgroup.zpowers σ)) → homCoind k Ω K R) hh)
      = (homCoind.instDistribMulActionAlgEquiv (E1cF R)).smul (hh : Ω ≃ₐ[k] Ω)
          (liftOf (k := k) (Ω := Ω) (K := K) R c)
        - liftOf (k := k) (Ω := Ω) (K := K) R c := by
    rw [show ((Work.SSGRoute.PT.H2Fin.resZ1 (Subgroup.zpowers σ) (homCoind k Ω K R) c :
        Work.AbsoluteKummer.Z1 (↥(Subgroup.zpowers σ)) (homCoind k Ω K R)) :
          (↥(Subgroup.zpowers σ)) → homCoind k Ω K R) hh
        = (c : (Ω ≃ₐ[k] Ω) → homCoind k Ω K R) (hh : Ω ≃ₐ[k] Ω) from rfl]
    have hmap : iotaH (k := k) (Ω := Ω) (K := K) R
        ((c : (Ω ≃ₐ[k] Ω) → homCoind k Ω K R) (hh : Ω ≃ₐ[k] Ω))
        = ((Work.AbsoluteKummer.mapZ1 (iotaH (k := k) (Ω := Ω) (K := K) R)
            (iotaH_equivariant (k := k) (Ω := Ω) (K := K) R) c :
          ↥(Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (E1cN (k := k) (Ω := Ω) (K := K) R))) :
            (Ω ≃ₐ[k] Ω) → E1cN (k := k) (Ω := Ω) (K := K) R)
          (hh : Ω ≃ₐ[k] Ω) :=
      (Work.AbsoluteKummer.mapZ1_apply (iotaH (k := k) (Ω := Ω) (K := K) R)
        (iotaH_equivariant (k := k) (Ω := Ω) (K := K) R) c (hh : Ω ≃ₐ[k] Ω)).symm
    have hspec := congrFun (liftOf_spec (k := k) (Ω := Ω) (K := K) R c) (hh : Ω ≃ₐ[k] Ω)
    rw [Work.GroupCohomology.d0_apply] at hspec
    exact hmap.trans hspec.symm
  rw [h2]
  rw [hm]
  rw [show liftOf (k := k) (Ω := Ω) (K := K) R c - z'.1 - Φ
      = liftOf (k := k) (Ω := Ω) (K := K) R c - (z'.1 + Φ) from by abel]
  rw [dma_smul_sub (homCoind.instDistribMulActionAlgEquiv (E1cF R)) (hh : Ω ≃ₐ[k] Ω)
      (liftOf (k := k) (Ω := Ω) (K := K) R c) (z'.1 + Φ),
    dma_smul_add (homCoind.instDistribMulActionAlgEquiv (E1cF R)) (hh : Ω ≃ₐ[k] Ω) z'.1 Φ,
    algEquiv_smul_eq_of_mem_H0 (k := k) (Ω := Ω) (K := K) R (hh : Ω ≃ₐ[k] Ω) z'.1 z'.2,
    algEquiv_smul_eq_of_mem_H0_zpowers (k := k) (Ω := Ω) (K := K) R σ Φ hΦinv hh]
  abel

/-! ## The involution restriction square of the `E1c` dictionary -/

/-- **The involution restriction square, on the `E1c` dictionary.**  If the restriction of the
`PhiE`-generator of `w` to `H̄ = ⟨res k K σ⟩` vanishes, then the restriction of the `E1c` class of
that generator to `H = ⟨σ⟩` vanishes. -/
theorem resH1_zpowers_e1cMap_eq_zero_of_extRes_eq_zero
    (R : Rep.{0} Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1)
    (w : CategoryTheory.Abelian.Ext.{0} (E1cR1 R) (unitsK k K) 0)
    (h : SSGRoute.PTExt.extRes (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
          (PhiE (k := k) (Ω := Ω) (K := K) R w) = 0) :
    Work.SSGRoute.PT.H2Fin.resH1 (Subgroup.zpowers σ) (homCoind k Ω K R)
      (e1cMap (k := k) (Ω := Ω) (K := K) R
        (PhiE (k := k) (Ω := Ω) (K := K) R w)) = 0 := by
  classical
  haveI : Fintype (K ≃ₐ[k] K) := inferInstance
  -- ### the `H̄`-equivariant `Kˣ`-valued lift of `w`
  obtain ⟨Ψ, hΨ⟩ := exists_lift_of_extRes_PhiE_eq_zero (k := k) (Ω := Ω) (K := K) R
    (Subgroup.zpowers (SSGRoute.res k K σ)) w h
  -- ### the `Ωˣ`-valued lift
  let Φ : E1cN (k := k) (Ω := Ω) (K := K) R :=
    (unitsAddToOmega (k := k) (Ω := Ω) (K := K)).comp (Rep.Hom.hom Ψ).toAddMonoidHom
  have hΦκ : ∀ x : (E1cR1 R).V,
      Φ (kappa R x)
        = (PsiEMap (k := k) (Ω := Ω) (K := K)
            (E1cR1 R) w).1 x := by
    intro x
    show unitsAddToOmega (k := k) (Ω := Ω) (K := K) (Rep.Hom.hom Ψ (kappa R x)) = _
    rw [PsiEMap_apply_toCoindH0, Work.SSGRoute.toCoindH0_apply,
      unitsAddToOmega_apply, hΨ x]
  -- ### `Φ` is `H`-invariant
  have hΦstable : (homCoind.instDistribMulActionAlgEquiv (E1cF R)).smul σ Φ = Φ := by
    apply AddMonoidHom.ext
    intro v
    rw [smul_conj_homCoindFreeT]
    have key : ∀ u : (E1cF R).V,
        Φ ((E1cF R).ρ (SSGRoute.res k K σ) u)
          = homCoind.smulHom (k := k) (Ω := Ω) σ (Φ u) := by
      intro u
      have heq := Rep.hom_comm_apply Ψ
        (⟨SSGRoute.res k K σ, Subgroup.mem_zpowers (SSGRoute.res k K σ)⟩ :
          ↥(Subgroup.zpowers (SSGRoute.res k K σ))) u
      have heq' : Rep.Hom.hom Ψ ((E1cF R).ρ (SSGRoute.res k K σ) u)
          = (unitsK k K).ρ (SSGRoute.res k K σ) (Rep.Hom.hom Ψ u) := heq
      show unitsAddToOmega (k := k) (Ω := Ω) (K := K) (Rep.Hom.hom Ψ ((E1cF R).ρ (SSGRoute.res k K σ) u)) = _
      rw [heq', Work.SSGRoute.homCoind.smulHom_apply]
      exact (smul_unitsAddToOmega (k := k) (Ω := Ω) (K := K) σ (Rep.Hom.hom Ψ u)).symm
    rw [← key ((E1cF R).ρ (SSGRoute.res k K σ)⁻¹ v)]
    congr 1
    first
      | (rw [← Module.End.mul_apply, mul_inv_cancel, Module.End.one_apply])
      | (rw [← Module.End.mul_apply,
            ← map_mul (E1cF R).ρ (SSGRoute.res k K σ) ((SSGRoute.res k K σ)⁻¹),
            mul_inv_cancel, map_one, Module.End.one_apply])
  have hΦinv : Φ ∈ Work.AbsoluteKummer.H0 (Subgroup.zpowers σ)
      (E1cN (k := k) (Ω := Ω) (K := K) R) := by
    rw [Work.GroupCohomology.mem_invariants]
    intro hh
    change (homCoind.instDistribMulActionAlgEquiv (E1cF R)).smul
      (hh : Ω ≃ₐ[k] Ω) Φ = Φ
    have hmem : (hh : Ω ≃ₐ[k] Ω) ∈ MulAction.stabilizer (Ω ≃ₐ[k] Ω) Φ :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr hΦstable) hh.2
    rw [MulAction.mem_stabilizer_iff] at hmem
    exact hmem
  have hpiΦ : piH (k := k) (Ω := Ω) (K := K) R Φ
      = (PsiEMap (k := k) (Ω := Ω) (K := K)
          (E1cR1 R) w).1 := by
    apply AddMonoidHom.ext
    intro x
    rw [show (piH (k := k) (Ω := Ω) (K := K) R Φ) x
        = Φ (kappa R x) from rfl]
    exact hΦκ x
  -- ### the `β`-characterisation of the class
  have hbeta : betaH (k := k) (Ω := Ω) (K := K) R
      (e1cMap (k := k) (Ω := Ω) (K := K) R
        (PhiE (k := k) (Ω := Ω) (K := K) R w))
      = QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
          (PsiEMap (k := k) (Ω := Ω) (K := K)
            (E1cR1 R) w) := by
    rw [← betaEquiv_apply, e1cMap_Phi, AddEquiv.apply_symm_apply]
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B1 (Ω ≃ₐ[k] Ω) (homCoind k Ω K R)).comap
      (Work.AbsoluteKummer.Z1 (Ω ≃ₐ[k] Ω) (homCoind k Ω K R)).subtype)
    (e1cMap (k := k) (Ω := Ω) (K := K) R
      (PhiE (k := k) (Ω := Ω) (K := K) R w))
  have hbc : QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
        (betaRaw (k := k) (Ω := Ω) (K := K) R c)
      = QuotientAddGroup.mk' (piH0 (k := k) (Ω := Ω) (K := K) R).range
          (PsiEMap (k := k) (Ω := Ω) (K := K)
            (E1cR1 R) w) := by
    rw [← hbeta, ← hc, betaH_mk]
  have hmem : (betaRaw (k := k) (Ω := Ω) (K := K) R c)
      - (PsiEMap (k := k) (Ω := Ω) (K := K) (E1cR1 R) w)
      ∈ (piH0 (k := k) (Ω := Ω) (K := K) R).range :=
    QuotientAddGroup.eq_iff_sub_mem.mp hbc
  obtain ⟨z', hz'⟩ := AddMonoidHom.mem_range.mp hmem
  have hz'' : piH (k := k) (Ω := Ω) (K := K) R z'.1
      = piH (k := k) (Ω := Ω) (K := K) R
          (liftOf (k := k) (Ω := Ω) (K := K) R c)
        - (PsiEMap (k := k) (Ω := Ω) (K := K)
            (E1cR1 R) w).1 := by
    have hzv := congrArg Subtype.val hz'
    simpa [piH0, Work.GroupCohomology.mapH0, betaRaw] using hzv
  -- ### the connecting element and the coboundary
  have hker : liftOf (k := k) (Ω := Ω) (K := K) R c - z'.1 - Φ
      ∈ (piH (k := k) (Ω := Ω) (K := K) R).ker := by
    rw [AddMonoidHom.mem_ker, map_sub, map_sub, hz'', hpiΦ]
    abel
  have hker' : liftOf (k := k) (Ω := Ω) (K := K) R c - z'.1 - Φ
      ∈ (iotaH (k := k) (Ω := Ω) (K := K) R).range := by
    rw [iotaH_range_eq_piH_ker]
    exact hker
  obtain ⟨m, hm⟩ := AddMonoidHom.mem_range.mp hker'
  have hz'inv : z'.1 + Φ ∈ Work.AbsoluteKummer.H0 (Subgroup.zpowers σ)
      (E1cN (k := k) (Ω := Ω) (K := K) R) := by
    refine AddSubgroup.add_mem _ ?_ hΦinv
    rw [Work.GroupCohomology.mem_invariants]
    intro hh
    rw [Subgroup.smul_def]
    exact (Work.GroupCohomology.mem_invariants (Ω ≃ₐ[k] Ω)
      (E1cN (k := k) (Ω := Ω) (K := K) R) z'.1).mp z'.2
      (hh : Ω ≃ₐ[k] Ω)
  -- ### `resZ1 c` is a coboundary
  have hB1 : ((Work.SSGRoute.PT.H2Fin.resZ1 (Subgroup.zpowers σ) (homCoind k Ω K R) c :
        Work.AbsoluteKummer.Z1 (↥(Subgroup.zpowers σ)) (homCoind k Ω K R)) :
          (↥(Subgroup.zpowers σ)) → homCoind k Ω K R)
      ∈ Work.AbsoluteKummer.B1 (↥(Subgroup.zpowers σ)) (homCoind k Ω K R) :=
    resZ1_zpowers_mem_B1 (k := k) (Ω := Ω) (K := K) R σ c Φ hΦinv z' m hm
  -- ### conclude
  rw [show e1cMap (k := k) (Ω := Ω) (K := K) R
        (PhiE (k := k) (Ω := Ω) (K := K) R w)
      = Work.AbsoluteKummer.H1π (Ω ≃ₐ[k] Ω) (homCoind k Ω K R) c from hc.symm]
  rw [Work.SSGRoute.PT.H2Fin.resH1_H1π, Work.AbsoluteKummer.H1π_eq_zero_iff]
  exact hB1

/-- **The restriction square of the canonical chain at an involution.**

`e1aChainH N : Ext²_G(N, Kˣ) →+ H²(Γ, Hom_ℤ(N, Ωˣ))` is the canonical `Hom`-side chain
`δ ∘ e1cMap ∘ (syzygy shift)⁻¹`, with `Γ = Ω ≃ₐ[k] Ω`.  If `σ ∈ Γ` is an involution whose
restriction `σ̄ = res k K σ` to `K` is non-trivial, then `⟨σ⟩ ∩ Gal(Ω/K) = 1`, so `⟨σ⟩ ≅ ⟨σ̄⟩` and
the inflation–restriction description of the chain says that the restriction of the chain class to
`⟨σ⟩` is the inflation of the coefficient-image of the restriction of `y` to `⟨σ̄⟩`; the coefficient
module `Hom_ℤ(N, Ωˣ) = Hom(N, μ_p)` agrees with `Hom_ℤ(N, Kˣ) = (Hom_ℤ(N,Ωˣ))^{G_K}`, so the
coefficient change is an isomorphism on the coefficients.  This is the `H²`-restriction square of
the `E1c`/chain dictionary at the involution: the "involution level-change square" that
`ExtChain/NOTE_himgExtDeltaInput_inf_session.md` §3 lists as the missing input of the `himg` node
(the case `D ∩ Gal(Ω/K) = 1`, where the coefficient-field mismatch of
`ExtChain/NOTE_himg_status_session11.md` §2 is *absent*, so the square is expected to hold).
The reduction `ExtChain.resH1_zpowers_e1cMap_eq_zero_of_resH2_e1aChainH_eq_zero`
(`ExtChain/himgIdelesInput_inf.lean`, sorry-free) consumes this statement directly. -/
theorem resH2_zpowers_e1aChainH_eq_zero_of_extRes_zpowers_eq_zero {k : Type} [Field k]
    [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) (hnt : SSGRoute.res k K σ ≠ 1)
    (y : CategoryTheory.Abelian.Ext.{0} N (SSGRoute.PTExt.unitsK k K) 2)
    (hy : SSGRoute.PTExt.extRes (Subgroup.zpowers (SSGRoute.res k K σ)).subtype y = 0) :
    Work.SSGRoute.PT.resH2 (Subgroup.zpowers σ)
      (Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) N y) = 0 := by
  haveI hRfin : Module.Finite ℤ (Limits.kernel (freeCover N)).V := freeCoverSES_finite N
  -- the syzygy shift inverse restricts to zero
  have hz : SSGRoute.PTExt.extRes (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
      ((e1aSyzShift (k := k) (K := K) N).symm y) = 0 := by
    haveI : Projective ((freeCoverSES N).X₂) :=
      Rep.free_projective (k := Coeff) (G := K ≃ₐ[k] K) (α := N.V)
    refine extRes_eq_zero_of_extRes_shift_eq_zero
      (Subgroup.zpowers (SSGRoute.res k K σ)) (freeCoverSES N)
      (freeCoverSES_shortExact N) (unitsK k K) ((e1aSyzShift (k := k) (K := K) N).symm y) ?_
    show SSGRoute.PTExt.extRes (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
        (Work.SSGRoute.PT.e1aShiftEquiv (freeCoverSES N) (freeCoverSES_shortExact N)
          (unitsK k K) 1 (le_refl 1) ((e1aSyzShift (k := k) (K := K) N).symm y)) = 0
    rw [show Work.SSGRoute.PT.e1aShiftEquiv (freeCoverSES N) (freeCoverSES_shortExact N)
          (unitsK k K) 1 (le_refl 1) ((e1aSyzShift (k := k) (K := K) N).symm y) = y from
        AddEquiv.apply_symm_apply (e1aSyzShift (k := k) (K := K) N) y]
    exact hy
  -- a `PhiE`-generator of the class
  obtain ⟨w, hw⟩ := PhiE_surjective (k := k) (Ω := Ω) (K := K)
    (Limits.kernel (freeCover N)) ((e1aSyzShift (k := k) (K := K) N).symm y)
  have hzPhi : SSGRoute.PTExt.extRes (Subgroup.zpowers (SSGRoute.res k K σ)).subtype
      (PhiE (k := k) (Ω := Ω) (K := K)
        (Limits.kernel (freeCover N)) w) = 0 := by
    rw [hw]
    exact hz
  have hres1 := resH1_zpowers_e1cMap_eq_zero_of_extRes_eq_zero (k := k) (Ω := Ω) (K := K)
    (Limits.kernel (freeCover N)) σ hσ hnt w hzPhi
  -- the chain class
  have hchain : Work.SSGRoute.PT.e1aChainH (k := k) (Ω := Ω) (K := K) N y
      = e1aDelta (k := k) (Ω := Ω) (K := K) N
          (e1cMap (k := k) (Ω := Ω) (K := K) (Limits.kernel (freeCover N))
            (PhiE (k := k) (Ω := Ω) (K := K)
              (Limits.kernel (freeCover N)) w)) := by
    rw [Work.SSGRoute.PT.e1aChainH_apply]
    rw [show Work.SSGRoute.ExtChain.e1cEquiv (k := k) (Ω := Ω) (K := K)
          (Limits.kernel (freeCover N)) ((e1aSyzShift (k := k) (K := K) N).symm y)
        = e1cMap (k := k) (Ω := Ω) (K := K) (Limits.kernel (freeCover N))
            ((e1aSyzShift (k := k) (K := K) N).symm y) from rfl]
    rw [← hw]
  rw [hchain]
  rw [show e1aDelta (k := k) (Ω := Ω) (K := K) N
      = (e1aSES (k := k) (Ω := Ω) (K := K) N).deltaH2 from rfl]
  rw [deltaH2_restriction (e1aSES (k := k) (Ω := Ω) (K := K) N) (Subgroup.zpowers σ)
    (e1cMap (k := k) (Ω := Ω) (K := K) (Limits.kernel (freeCover N))
      (PhiE (k := k) (Ω := Ω) (K := K) (Limits.kernel (freeCover N)) w))]
  rw [hres1, map_zero]

end

end Work.SSGRoute.ExtChain

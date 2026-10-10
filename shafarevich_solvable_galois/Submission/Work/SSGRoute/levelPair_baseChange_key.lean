import Mathlib.Tactic.Have
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.baseChangeDefs

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute

open CategoryTheory SSGRoute.PTExt

namespace Y3Key

open CategoryTheory SSGRoute.PTExt

/-- Degree-`0`-on-the-left associativity of `Ext.comp`. -/
theorem comp_assoc_of_first_deg_zero {G : Type} [Group G] {X Y Z T : Rep Coeff G} {a₂ a₃ : ℕ}
    (α : Abelian.Ext X Y 0) (β : Abelian.Ext Y Z a₂) (γ : Abelian.Ext Z T a₃) :
    (α.comp β (zero_add a₂)).comp γ rfl = α.comp (β.comp γ rfl) (zero_add (a₂ + a₃)) :=
  Abelian.Ext.comp_assoc α β γ (zero_add a₂) rfl (by omega)

/-- Restriction-companion of the level pairing (re-proved here). -/
theorem levelPair_restrict' {G H H' : Type} [Group G] [Group H] [Group H']
    (f : H →* G) (g : H' →* H) {M A : Rep Coeff G} {B : Rep Coeff H}
    {B' : Rep Coeff H'} (ι : Rep.res f A ⟶ B) (ιg : Rep.res g B ⟶ B')
    (ι' : Rep.res (f.comp g) A ⟶ B') {r s : ℕ} (x : Abelian.Ext M A r)
    (h : extH (Rep.res f M) s) (hι : Rep.resMap g ι ≫ ιg = ι') :
    extHMap g ιg (levelPair f ι x h)
      = levelPair (f.comp g) ι' x (extHMap g (𝟙 (Rep.res g (Rep.res f M))) h) := by
  have hcomp : Abelian.Ext.mapExactFunctor (Rep.resFunctor g)
        (Abelian.Ext.mapExactFunctor (Rep.resFunctor f) x) =
      Abelian.Ext.mapExactFunctor (Rep.resFunctor (f.comp g)) x := by
    simpa only [extRes] using (Work.SSGRoute.SylowDesc.extRes_comp_aux f g x).symm
  have hh : extHMap g (𝟙 (Rep.res g (Rep.res f M))) h
      = (Abelian.Ext.mk₀ (unitRes g)).comp (extRes g h) (zero_add s) := by
    simp only [extHMap, Abelian.Ext.comp_mk₀_id]
  rw [hh]
  simp only [levelPair, extHMap, extRes, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀, hcomp, Abelian.Ext.mk₀_comp_mk₀, hι,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero,
    comp_assoc_of_first_deg_zero]

/-- Transport of `extRes` along an equality of group homomorphisms (re-proved here). -/
theorem extRes_transport' {G H : Type} [Group G] [Group H]
    {A M : Rep Coeff G} {r : ℕ} (x : Abelian.Ext M A r) {f₁ f₂ : H →* G} (hf : f₂ = f₁) :
    extRes f₂ x = ((Abelian.Ext.mk₀ (eqToHom (congrArg (fun t => Rep.res t M) hf))).comp
        (extRes f₁ x) (zero_add r)).comp
        (Abelian.Ext.mk₀ (eqToHom (congrArg (fun t => Rep.res t A) hf.symm))) (add_zero r) := by
  cases hf
  simp [CategoryTheory.eqToHom_refl, Abelian.Ext.mk₀_id_comp, Abelian.Ext.comp_mk₀_id]

/-- Comparison of the level pairing at two propositionally equal group homomorphisms
(re-proved here). -/
theorem levelPair_transport' {G H : Type} [Group G] [Group H]
    {A M : Rep Coeff G} {B' : Rep Coeff H} {r s : ℕ}
    {f₁ f₂ : H →* G} (x : Abelian.Ext M A r)
    (ρA : Rep.res f₁ A ⟶ Rep.res f₂ A) (ρM : Rep.res f₁ M ⟶ Rep.res f₂ M)
    (σM : Rep.res f₂ M ⟶ Rep.res f₁ M) (hρσM : ρM ≫ σM = 𝟙 _)
    (ι₁ : Rep.res f₁ A ⟶ B') (ι₂ : Rep.res f₂ A ⟶ B')
    (h₁ : extH (Rep.res f₁ M) s) (h₂ : extH (Rep.res f₂ M) s)
    (hι : ι₁ = ρA ≫ ι₂)
    (hh : h₂ = h₁.comp (Abelian.Ext.mk₀ ρM) (add_zero s))
    (hx : extRes f₂ x = ((Abelian.Ext.mk₀ σM).comp (extRes f₁ x) (zero_add r)).comp
        (Abelian.Ext.mk₀ ρA) (add_zero r)) :
    levelPair f₁ ι₁ x h₁ = levelPair f₂ ι₂ x h₂ := by
  subst hι
  subst hh
  simp only [levelPair]
  rw [hx]
  simp only [Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.mk₀_comp_mk₀_assoc,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero,
    hρσM, Abelian.Ext.mk₀_id_comp]

/-- The unit `ℤ → ℤ` post-composed with an `Ext`-class is the class itself. -/
theorem comp_mk0_unitRes {G H : Type} [Group G] [Group H] (f : H →* G) {B : Rep Coeff H} {n : ℕ}
    (α : Abelian.Ext (Rep.res f (unitRep G)) B n) :
    (Abelian.Ext.mk₀ (unitRes f)).comp α (zero_add n) = α := by
  have hf : unitRes f = 𝟙 (unitRep H) := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    rfl
  rw [hf]
  exact Abelian.Ext.mk₀_id_comp α

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false in
/-- `extHMap` along a group hom is `extRes` followed by the coefficient morphism. -/
theorem extHMap_eq_comp {G H : Type} [Group G] [Group H] (f : H →* G) {A : Rep Coeff G}
    {B : Rep Coeff H} (ι : Rep.res f A ⟶ B) {n : ℕ} (h : extH A n) :
    extHMap f ι h = (extRes f h).comp (Abelian.Ext.mk₀ ι) (add_zero n) := by
  simp only [extHMap]
  rw [comp_mk0_unitRes f]

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false in
/-- `levelPair` does not change when the `Ext`-class is transported along a composite of group
homs. -/
theorem levelPair_extRes_extRes {G G' G'' : Type} [Group G] [Group G'] [Group G'']
    (ψ : G' →* G) (φ : G'' →* G') {M A : Rep Coeff G} {B : Rep Coeff G''}
    (ι : Rep.res (ψ.comp φ) A ⟶ B) {r s : ℕ} (z : Abelian.Ext M A r)
    (h₂ : extH (Rep.res φ (Rep.res ψ M)) s) :
    levelPair φ ι (extRes ψ z) h₂ = levelPair (ψ.comp φ) ι z h₂ := by
  simp only [SSGRoute.PTExt.levelPair]
  exact congrArg (fun u => Abelian.Ext.comp h₂
    (Abelian.Ext.comp u (Abelian.Ext.mk₀ ι) (add_zero r)) rfl)
    (Work.SSGRoute.SylowDesc.extRes_comp_aux ψ φ z).symm

end Y3Key

/-- `eqToHom` along an equality of restriction maps acts as the identity on the underlying
module (build-speed helper: proved once by `subst`, instead of a `rfl` that makes the elaborator
and the kernel compare the two homomorphisms by unfolding). -/
theorem Y3Key.eqToHom_res_hom_apply {G H : Type} [Group G] [Group H] (A : Rep Coeff G)
    {f g : H →* G} (h : f = g) (y : (Rep.res f A).V) :
    (Rep.Hom.hom (eqToHom (congrArg (fun t => Rep.res t A) h))) y = y := by
  subst h
  rfl

theorem levelPair_baseChange_key (k k' K : Type) [Field k] [NumberField k] [Field k']
    [NumberField k'] [Field K] [NumberField K] [Algebra k K] [Algebra k' K] [Algebra k k']
    [IsScalarTower k k' K] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k' K]
    [IsGalois k' K]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L] [Algebra k' L] [IsScalarTower k' K L]
    [IsScalarTower k k' L] [FiniteDimensional k' L] [IsGalois k' L]
    (w : NK.GlobalCFT.Place K) (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (w' : NK.GlobalCFT.Place L)
    (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* SSGRoute.PTExt.decompK (k := k) w)
    (hf : ∀ σ, ((f σ : SSGRoute.PTExt.decompK (k := k) w) : K ≃ₐ[k] K)
      = SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L))
    (ι : Rep.res f (SSGRoute.PTExt.localUnitsK (k := k) w)
      ⟶ NK.HassePrinciple.localUnitsRep k L w')
    (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom (Additive.ofMul u) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
    (f' : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* SSGRoute.PTExt.decompK (k := k') w)
    (hf' : ∀ σ, ((f' σ : SSGRoute.PTExt.decompK (k := k') w) : K ≃ₐ[k'] K)
      = SSGRoute.PTExt.galRes k' K L (σ : L ≃ₐ[k'] L))
    (ι' : Rep.res f' (SSGRoute.PTExt.localUnitsK (k := k') w)
      ⟶ NK.HassePrinciple.localUnitsRep k' L w')
    (hι' : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι'.hom (Additive.ofMul u) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u))
    (z : CategoryTheory.Abelian.Ext
        (Rep.res (Work.SSGRoute.Y3Test.baseChangeSubgroup k k' K w).subtype
          (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M))
        (Rep.res (Work.SSGRoute.Y3Test.baseChangeSubgroup k k' K w).subtype
          (SSGRoute.PTExt.localUnitsK (k := k) w)) 1)
    (h : SSGRoute.PTExt.extH (Rep.res
        (f.subgroupComap (Work.SSGRoute.Y3Test.baseChangeSubgroup k k' K w))
        (Rep.res (Work.SSGRoute.Y3Test.baseChangeSubgroup k k' K w).subtype
          (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M))) 1) :
    SSGRoute.PTExt.levelPair f' ι' (Work.SSGRoute.Y3Test.eEdef k k' K w M z)
        (Work.SSGRoute.Y3Test.eHdef k k' K L w' w M f hf f' hf' h)
      = Work.SSGRoute.Y3Test.eBdef k k' K L w' w f hf f' hf'
          (SSGRoute.PTExt.levelPair
            (A := Rep.res (Work.SSGRoute.Y3Test.baseChangeSubgroup k k' K w).subtype
                (SSGRoute.PTExt.localUnitsK (k := k) w))
            (B := Rep.res
                ((Work.SSGRoute.Y3Test.baseChangeSubgroup k k' K w).comap f).subtype
                (NK.HassePrinciple.localUnitsRep k L w'))
            (f.subgroupComap (Work.SSGRoute.Y3Test.baseChangeSubgroup k k' K w))
            (Rep.resMap
              ((Work.SSGRoute.Y3Test.baseChangeSubgroup k k' K w).comap f).subtype ι) z h) := by
  rw [Work.SSGRoute.Y3Test.eEdef_apply, Work.SSGRoute.Y3Test.eHdef_apply,
    Work.SSGRoute.Y3Test.eBdef_apply]
  let Ssub : Subgroup (SSGRoute.PTExt.decompK (k := k) w) :=
    Work.SSGRoute.Y3Test.baseChangeSubgroup k k' K w
  let βT : SSGRoute.PTExt.decompK (k := k') w →* Ssub :=
    (Work.SSGRoute.Y3Test.baseChangeMulEquiv k k' K w).toMonoidHom
  let lamT : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* Subgroup.comap f Ssub :=
    (Work.SSGRoute.Y3Test.levelEquiv k k' K L w' w f hf f' hf').toMonoidHom
  let γ : Subgroup.comap f Ssub →* Ssub := f.subgroupComap Ssub
  let X : Rep SSGRoute.PTExt.Coeff Ssub :=
    Rep.res Ssub.subtype (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M)
  let Ak : Rep SSGRoute.PTExt.Coeff Ssub := Rep.res Ssub.subtype (SSGRoute.PTExt.localUnitsK (k := k) w)
  let Y : Rep SSGRoute.PTExt.Coeff (Subgroup.comap f Ssub) :=
    Rep.res (Subgroup.comap f Ssub).subtype (NK.HassePrinciple.localUnitsRep k L w')
  let ιg : Rep.res γ Ak ⟶ Y := Rep.resMap (Subgroup.comap f Ssub).subtype ι
  let iX : Rep.res lamT (Rep.res γ X) ≅
      Rep.res f' (Rep.res (SSGRoute.PTExt.decompK (k := k') w).subtype
        (Rep.res (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)) M)) :=
    eqToIso (Work.SSGRoute.Y3Test.res_beta_XS k k' K L w' w f hf f' hf' M)
  let iY : Rep.res lamT Y ≅ NK.HassePrinciple.localUnitsRep k' L w' :=
    eqToIso (Work.SSGRoute.Y3Test.res_beta_YS k k' K L w' w f hf f' hf')
  let t := levelPair γ ιg z h
  let h₂ : extH (Rep.res f' (Rep.res (SSGRoute.PTExt.decompK (k := k') w).subtype
      (Rep.res (AlgEquiv.restrictScalarsHom (R := k) (S := k') (A := K)) M))) 1 :=
    (extRes lamT h).comp (Abelian.Ext.mk₀ iX.hom) (add_zero 1)
  let f₁ : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* Ssub := γ.comp lamT
  let f₂ : MulAction.stabilizer (L ≃ₐ[k'] L) w' →* Ssub := βT.comp f'
  let hcomm : f₁ = f₂ := Work.SSGRoute.Y3Test.hcomm_aux k k' K L w' w f hf f' hf'
  let ρA : Rep.res f₁ Ak ⟶ Rep.res f₂ Ak := eqToHom (congrArg (fun t => Rep.res t Ak) hcomm)
  let ρM := eqToHom (Work.SSGRoute.Y3Test.res_beta_XS k k' K L w' w f hf f' hf' M)
  let σM : Rep.res f₂ X ⟶ Rep.res f₁ X := eqToHom (congrArg (fun t => Rep.res t X) hcomm.symm)
  let ι₁ : Rep.res f₁ Ak ⟶ NK.HassePrinciple.localUnitsRep k' L w' :=
    Rep.resMap lamT ιg ≫ iY.hom
  let Y' : Rep SSGRoute.PTExt.Coeff (MulAction.stabilizer (L ≃ₐ[k'] L) w') :=
    NK.HassePrinciple.localUnitsRep k' L w'
  have hA : (extRes lamT t).comp (Abelian.Ext.mk₀ iY.hom) (add_zero 2) = extHMap lamT iY.hom t :=
    (Y3Key.extHMap_eq_comp lamT iY.hom t).symm
  have hD : levelPair f' ι' (extRes βT z) h₂ = levelPair f₂ ι' z h₂ :=
    Y3Key.levelPair_extRes_extRes (G := Ssub) (G' := SSGRoute.PTExt.decompK (k := k') w)
      (G'' := MulAction.stabilizer (L ≃ₐ[k'] L) w')
      (M := X) (A := Ak) (B := Y') (r := 1) (s := 1) βT f' ι' z h₂
  have hB : extHMap lamT iY.hom t
      = levelPair (γ.comp lamT) (Rep.resMap lamT ιg ≫ iY.hom) z
          (extHMap lamT (𝟙 (Rep.res lamT (Rep.res γ X))) h) :=
    Y3Key.levelPair_restrict' (f := γ) (g := lamT) (ι := ιg) (ιg := iY.hom)
      (ι' := Rep.resMap lamT ιg ≫ iY.hom) (x := z) (h := h) rfl
  let h₁ : extH (Rep.res f₁ X) 1 := extHMap lamT (𝟙 (Rep.res lamT (Rep.res γ X))) h
  have hh₁ : h₁ = extRes lamT h := by
    rw [show h₁ = extHMap lamT (𝟙 (Rep.res lamT (Rep.res γ X))) h from rfl,
      Y3Key.extHMap_eq_comp lamT (𝟙 (Rep.res lamT (Rep.res γ X))) h,
      Abelian.Ext.comp_mk₀_id]
  have hh : h₂ = h₁.comp (Abelian.Ext.mk₀ ρM) (add_zero 1) := by
    rw [show h₂ = (extRes lamT h).comp (Abelian.Ext.mk₀ iX.hom) (add_zero 1) from rfl, hh₁]
    rfl
  have hρσM : ρM ≫ σM = 𝟙 (Rep.res f₁ X) := by
    rw [show ρM = eqToHom (Work.SSGRoute.Y3Test.res_beta_XS k k' K L w' w f hf f' hf' M) from rfl,
        show σM = eqToHom (congrArg (fun t => Rep.res t X) hcomm.symm) from rfl,
        CategoryTheory.eqToHom_trans]
    exact CategoryTheory.eqToHom_refl (Rep.res f₁ X) _
  have hx : extRes f₂ z = ((Abelian.Ext.mk₀ σM).comp (extRes f₁ z) (zero_add 1)).comp
      (Abelian.Ext.mk₀ ρA) (add_zero 1) :=
    Y3Key.extRes_transport' (M := X) (A := Ak) (r := 1) (f₁ := f₁) (f₂ := f₂) (x := z) hcomm.symm
  have hiY_c : ∀ y : (Rep.res lamT Y).V, iY.hom.hom.toLinearMap y = y := by
    intro y
    rw [show iY.hom = 𝟙 (Rep.res lamT Y) from rfl, Rep.hom_id]
    rfl
  have hρA_c : ∀ y : (Rep.res f₁ Ak).V, ρA.hom.toLinearMap y = y := by
    intro y
    exact Y3Key.eqToHom_res_hom_apply Ak hcomm y
  have hι_lin : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom.toLinearMap (Additive.ofMul u)
        = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u) := by
    intro u
    change (Rep.Hom.hom ι) (Additive.ofMul u) = _
    exact hι u
  have hι'_lin : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι'.hom.toLinearMap (Additive.ofMul u)
        = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' u) := by
    intro u
    change (Rep.Hom.hom ι') (Additive.ofMul u) = _
    exact hι' u
  have hιx : ι₁ = ρA ≫ ι' := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    change (Rep.resMap lamT ιg ≫ iY.hom).hom.toLinearMap (Additive.ofMul (Additive.toMul x))
        = (ρA ≫ ι').hom.toLinearMap (Additive.ofMul (Additive.toMul x))
    dsimp only [ιg]
    simp only [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
      Rep.resMap_hom_toLinearMap, hρA_c, hiY_c]
    exact (hι_lin (Additive.toMul x)).trans (hι'_lin (Additive.toMul x)).symm
  have hC : levelPair f₁ ι₁ z h₁ = levelPair f₂ ι' z h₂ :=
    Y3Key.levelPair_transport' (x := z) (f₁ := f₁) (f₂ := f₂) ρA ρM σM hρσM ι₁ ι' h₁ h₂ hιx hh hx
  exact hD.trans (hC.symm.trans (hB.symm.trans hA.symm))

end Work.SSGRoute

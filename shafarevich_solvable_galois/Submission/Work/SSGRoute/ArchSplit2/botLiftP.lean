import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.ExtChain.FreeCover
import Submission.Work.SSGRoute.ExtOneAux
import Submission.Work.SSGRoute.stdTensorComplex_projective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The "lift·`p`" functional at a split place

For a finite group `G`, a coefficient `L : Rep Coeff G` and a `G`-module `M` killed by a prime `p`,
the group `Ext¹_G(M, L)` is described as a cokernel via the canonical free presentation
`0 → R → F → M → 0` of `M` (`freeCoverSES`).  The *lift·p functional*
`Θ(ψ)(m) := σ (ψ (p · v))` (`v ∈ F` a lift of `m`, `σ` the sign functional on `L` with kernel `pL`)
descends to `Ext¹_G(M, L)` and, when `L` has the sign data of `ℝˣ`, is a bijection onto
`Hom_{ℤ/p}(M, ℤ/p)` which satisfies the "realization rule" for an arbitrary short exact presentation
of `M` and is natural in `M`.

This file builds the construction in a form independent of the arithmetic (the hypotheses on `L`
are collected in `LiftPData`), so that it can be instantiated at `L = K_wˣ ≅ ℝˣ`.
-/

namespace Work.SSGRoute.ArchSplit2

open CategoryTheory SSGRoute.PTExt

set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

attribute [local instance 10000] Rep.hV2 Rep.hV1

variable {G : Type} [Group G] [Fintype G]

/-! ## The canonical free presentation of a representation -/

/-- The canonical free cover `F = ℤ[G]^{(M)}` of `M`. -/
noncomputable abbrev Ftop (M : Rep.{0} Coeff G) : Rep.{0} Coeff G := Rep.free Coeff G M.V

/-- The canonical cover `F ⟶ M`. -/
noncomputable abbrev ctop (M : Rep.{0} Coeff G) : Ftop M ⟶ M := Work.SSGRoute.freeCover M

/-- The canonical syzygy `R = ker (F ⟶ M)`. -/
noncomputable abbrev Rtop (M : Rep.{0} Coeff G) : Rep.{0} Coeff G := Limits.kernel (ctop M)

/-- The inclusion `R ↪ F` of the canonical syzygy. -/
noncomputable abbrev jtop (M : Rep.{0} Coeff G) : Rtop M ⟶ Ftop M := Limits.kernel.ι (ctop M)

/-- The canonical generator of `F` over `m ∈ M`. -/
noncomputable abbrev gen (M : Rep.{0} Coeff G) (m : M.V) : (Ftop M).V :=
  Finsupp.single m (MonoidAlgebra.single 1 1)

section Basic

variable (M : Rep.{0} Coeff G)

theorem ctop_gen (m : M.V) : (Rep.Hom.hom (ctop M)).toLinearMap (gen M m) = m :=
  Work.SSGRoute.freeCover_apply_single M m

theorem ctop_jtop : jtop M ≫ ctop M = 0 := Limits.kernel.condition (ctop M)

theorem ctop_jtop_apply (y : (Rtop M).V) :
    (Rep.Hom.hom (ctop M)).toLinearMap ((Rep.Hom.hom (jtop M)).toLinearMap y) = 0 := by
  have h := congrArg (fun f : Rtop M ⟶ M => (Rep.Hom.hom f).toLinearMap y) (ctop_jtop M)
  rw [Rep.hom_comp] at h
  simp only [Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
    Representation.IntertwiningMap.zero_toLinearMap, LinearMap.zero_apply] at h
  exact h

end Basic

section DBL

variable (p : ℕ) (M : Rep.{0} Coeff G) (hM : ∀ m : M.V, p • m = 0)

include hM in
theorem ctop_nsmul_self : (p • 𝟙 (Ftop M)) ≫ ctop M = 0 := by
  apply Rep.hom_ext
  rw [Rep.hom_comp, Rep.zero_hom, Representation.IntertwiningMap.ext_iff]
  apply LinearMap.ext
  intro x
  simp only [Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
    Representation.IntertwiningMap.zero_toLinearMap, LinearMap.zero_apply]
  rw [Rep.nsmul_hom, Rep.hom_id]
  simp only [Pi.smul_apply]
  change (Rep.Hom.hom (ctop M)).toLinearMap (p • x) = 0
  rw [map_nsmul]
  exact hM _

/-- **The "multiplication by `p`" morphism** `F → R`, well defined because `p • m = 0` on `M`. -/
noncomputable def dbl : Ftop M ⟶ Rtop M :=
  Limits.kernel.lift (ctop M) (p • 𝟙 (Ftop M)) (ctop_nsmul_self p M hM)

theorem dbl_jtop : dbl p M hM ≫ jtop M = p • 𝟙 (Ftop M) :=
  Limits.kernel.lift_ι _ _ _

theorem jtop_dbl : jtop M ≫ dbl p M hM = p • 𝟙 (Rtop M) := by
  rw [← cancel_mono (jtop M)]
  rw [Category.assoc, dbl_jtop, Preadditive.comp_nsmul, Preadditive.nsmul_comp]
  simp

theorem nsmul_id_apply {A : Rep.{0} Coeff G} (n : ℕ) (y : A.V) :
    (Rep.Hom.hom (n • 𝟙 A)).toLinearMap y = n • y := by
  rw [Rep.nsmul_hom, Rep.hom_id]
  change (n • (LinearMap.id : A.V →ₗ[SSGRoute.PTExt.Coeff] A.V)) y = n • y
  rw [LinearMap.smul_apply, LinearMap.id_apply]

theorem dbl_jtop_apply (y : (Rtop M).V) :
    (Rep.Hom.hom (dbl p M hM)).toLinearMap ((Rep.Hom.hom (jtop M)).toLinearMap y) = p • y := by
  have h := congrArg (fun f : Rtop M ⟶ Rtop M => (Rep.Hom.hom f).toLinearMap y) (jtop_dbl p M hM)
  rw [Rep.hom_comp] at h
  simp only [Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply] at h
  rw [nsmul_id_apply (G := G) p y] at h
  exact h

theorem jtop_dbl_apply (x : (Ftop M).V) :
    (Rep.Hom.hom (jtop M)).toLinearMap ((Rep.Hom.hom (dbl p M hM)).toLinearMap x) = p • x := by
  have h := congrArg (fun f : Ftop M ⟶ Ftop M => (Rep.Hom.hom f).toLinearMap x) (dbl_jtop p M hM)
  rw [Rep.hom_comp] at h
  simp only [Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply] at h
  rw [nsmul_id_apply (G := G) p x] at h
  exact h


theorem dbl_injective (p : ℕ) (hp : p ≠ 0) (M : Rep.{0} Coeff G) (hM : ∀ m : M.V, p • m = 0) :
    Function.Injective (Rep.Hom.hom (dbl p M hM)).toLinearMap := by
  haveI : IsAddTorsionFree (Ftop M).V := IsAddTorsionFree.of_isTorsionFree ℤ (Ftop M).V
  intro x y hxy
  have h : p • x = p • y := by
    rw [← jtop_dbl_apply p M hM x, ← jtop_dbl_apply p M hM y, hxy]
  exact nsmul_right_injective hp h

end DBL

/-! ## The arithmetic data on the coefficient -/

/-- The data on a coefficient `L` needed to build the lift·`p` functional: a "sign" functional with
kernel `pL`, together with an injective section of it onto the `p`-torsion of `L`. -/
structure LiftPData (p : ℕ) (L : Rep.{0} Coeff G) where
  /-- the sign functional `L → ℤ/p`, with kernel `pL`. -/
  sgn : L.V →+ ZMod p
  /-- the section `ℤ/p → L`, onto `L[p]`. -/
  liftS : ZMod p →+ L.V
  hlift : ∀ c : ZMod p, sgn (liftS c) = c
  hinj : Function.Injective liftS
  hkrn : ∀ x : L.V, sgn x = 0 ↔ ∃ y : L.V, p • y = x
  htors : ∀ x : L.V, p • x = 0 → ∃ c : ZMod p, x = liftS c

section Sgn

variable {p : ℕ} {L : Rep.{0} Coeff G}

theorem LiftPData.sgn_nsmul_self (D : LiftPData p L) (x : L.V) : D.sgn (p • x) = 0 :=
  (D.hkrn _).mpr ⟨x, rfl⟩

theorem LiftPData.mem_range_liftS (D : LiftPData p L) {x : L.V} (hx : p • x = 0) :
    ∃ c : ZMod p, D.liftS c = x := by
  obtain ⟨c, hc⟩ := D.htors x hx
  exact ⟨c, hc.symm⟩

variable (L : Rep.{0} Coeff G)

/-- Build a morphism of `Rep Coeff G` out of an additive map, when `G` is trivial (the
equivariance is automatic and `Coeff`-linearity follows from additivity and the canonicity of the
`ULift ℤ`-action). -/
noncomputable def repHomOfAddHom [Subsingleton G] (A B : Rep.{0} Coeff G) (f : A.V →+ B.V) :
    A ⟶ B :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (f := { toFun := f
            map_add' := f.map_add
            map_smul' := fun c x => by
              obtain ⟨z⟩ := c
              change f (@SMul.smul Coeff A.V (A.hV2).toDistribMulAction.toSMul (ULift.up z) x)
                = @SMul.smul Coeff B.V (B.hV2).toDistribMulAction.toSMul (ULift.up z) (f x)
              rw [Work.SSGRoute.ulift_int_smul_eq_down A.hV2 (ULift.up z) x,
                Work.SSGRoute.ulift_int_smul_eq_down B.hV2 (ULift.up z) (f x)]
              exact AddMonoidHom.map_zsmul f z x })
    (ρ := A.ρ) (σ := B.ρ)
    (fun g v => by
      rw [Subsingleton.elim g 1]
      simp))

@[simp] theorem repHomOfAddHom_apply [Subsingleton G] (A B : Rep.{0} Coeff G) (f : A.V →+ B.V)
    (x : A.V) : (Rep.Hom.hom (repHomOfAddHom A B f)).toLinearMap x = f x := rfl

variable (L : Rep.{0} Coeff G) (D : LiftPData p L)

/-- The sign functional, as a morphism `L ⟶ ℤ/p`. -/
noncomputable def sgnHom [Subsingleton G] : L ⟶ Rep.trivial Coeff G (ZMod p) :=
  repHomOfAddHom L (Rep.trivial Coeff G (ZMod p)) D.sgn

@[simp] theorem sgnHom_apply [Subsingleton G] (x : L.V) :
    (Rep.Hom.hom (sgnHom L D)).toLinearMap x = D.sgn x := rfl

end Sgn

section Theta

variable (p : ℕ) [Fact p.Prime] (M : Rep.{0} Coeff G) (hM : ∀ m : M.V, p • m = 0)

/-- The morphism `F ⟶ ℤ/p` whose descent to `M` is the lift·`p` functional of `ψ`. -/
noncomputable def thetaK [Subsingleton G] (L : Rep.{0} Coeff G) (D : LiftPData p L)
    (ψ : Rtop M ⟶ L) : Ftop M ⟶ Rep.trivial Coeff G (ZMod p) :=
  (dbl p M hM ≫ ψ) ≫ sgnHom L D

include hM in
theorem thetaK_apply [Subsingleton G] (L : Rep.{0} Coeff G) (D : LiftPData p L)
    (ψ : Rtop M ⟶ L) (x : (Ftop M).V) :
    (Rep.Hom.hom (thetaK p M hM L D ψ)).toLinearMap x
      = D.sgn ((Rep.Hom.hom ψ).toLinearMap ((Rep.Hom.hom (dbl p M hM)).toLinearMap x)) :=
  rfl

include hM in
theorem thetaK_jtop [Subsingleton G] (L : Rep.{0} Coeff G) (D : LiftPData p L)
    (ψ : Rtop M ⟶ L) : jtop M ≫ thetaK p M hM L D ψ = 0 := by
  apply Rep.hom_ext
  rw [Rep.hom_comp, Rep.zero_hom, Representation.IntertwiningMap.ext_iff]
  apply LinearMap.ext
  intro y
  simp only [Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
    Representation.IntertwiningMap.zero_toLinearMap, LinearMap.zero_apply]
  rw [thetaK_apply, dbl_jtop_apply, map_nsmul, LiftPData.sgn_nsmul_self]

/-- **The lift·`p` functional**, as a morphism `M ⟶ ℤ/p` (for a primitive `ψ : R ⟶ L`). -/
noncomputable def theta [Subsingleton G] (L : Rep.{0} Coeff G) (D : LiftPData p L)
    (ψ : Rtop M ⟶ L) : M ⟶ Rep.trivial Coeff G (ZMod p) := by
  haveI : Epi (Work.SSGRoute.freeCoverSES M).g :=
    (Work.SSGRoute.freeCoverSES_shortExact M).epi_g
  exact (Work.SSGRoute.freeCoverSES_shortExact M).exact.desc (thetaK p M hM L D ψ)
    (thetaK_jtop p M hM L D ψ)

include hM in
theorem theta_g_desc [Subsingleton G] (L : Rep.{0} Coeff G) (D : LiftPData p L)
    (ψ : Rtop M ⟶ L) : ctop M ≫ theta p M hM L D ψ = thetaK p M hM L D ψ := by
  haveI : Epi (Work.SSGRoute.freeCoverSES M).g :=
    (Work.SSGRoute.freeCoverSES_shortExact M).epi_g
  have h := ShortComplex.Exact.g_desc (Work.SSGRoute.freeCoverSES_shortExact M).exact
    (thetaK p M hM L D ψ) (thetaK_jtop p M hM L D ψ)
  simpa only [theta] using h

include hM in
theorem theta_apply [Subsingleton G] (L : Rep.{0} Coeff G) (D : LiftPData p L)
    (ψ : Rtop M ⟶ L) (m : M.V) :
    (Rep.Hom.hom (theta p M hM L D ψ)).toLinearMap m
      = D.sgn ((Rep.Hom.hom ψ).toLinearMap ((Rep.Hom.hom (dbl p M hM)).toLinearMap (gen M m))) := by
  have h2 := congrArg (fun f : Ftop M ⟶ Rep.trivial Coeff G (ZMod p) =>
    (Rep.Hom.hom f).toLinearMap (gen M m)) (theta_g_desc p M hM L D ψ)
  rw [Rep.hom_comp] at h2
  simp only [Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply] at h2
  rw [ctop_gen] at h2
  rw [h2, thetaK_apply]

include hM in
theorem theta_zero [Subsingleton G] (L : Rep.{0} Coeff G) (D : LiftPData p L) :
    theta p M hM L D 0 = 0 := by
  apply Rep.hom_ext
  rw [Rep.zero_hom, Representation.IntertwiningMap.ext_iff]
  apply LinearMap.ext
  intro m
  rw [theta_apply, Representation.IntertwiningMap.zero_toLinearMap, LinearMap.zero_apply]
  simp

include hM in
theorem theta_add [Subsingleton G] (L : Rep.{0} Coeff G) (D : LiftPData p L)
    (ψ ψ' : Rtop M ⟶ L) :
    theta p M hM L D (ψ + ψ') = theta p M hM L D ψ + theta p M hM L D ψ' := by
  apply Rep.hom_ext
  rw [Rep.add_hom, Representation.IntertwiningMap.ext_iff]
  apply LinearMap.ext
  intro m
  rw [Representation.IntertwiningMap.add_toLinearMap, LinearMap.add_apply]
  rw [theta_apply, theta_apply, theta_apply]
  rw [Rep.add_hom, Representation.IntertwiningMap.add_toLinearMap, LinearMap.add_apply]
  rw [map_add]

end Theta

/-! ## The lift·`p` functional as an additive map `Ext¹(M,L) → Hom(M, ℤ/p)` -/

section Killing

variable (p : ℕ) [Fact p.Prime] (M : Rep.{0} Coeff G) (hM : ∀ m : M.V, p • m = 0)
  [Module (ZMod p) M.V] (L : Rep.{0} Coeff G) (D : LiftPData p L)

/-- The lift·`p` functional of a primitive `ψ : R ⟶ L`, as an additive map `M →+ ℤ/p`. -/
noncomputable def ThetaHom [Subsingleton G] (ψ : Rtop M ⟶ L) : M.V →+ ZMod p :=
  (Rep.Hom.hom (theta p M hM L D ψ)).toLinearMap.toAddMonoidHom

include hM in
theorem ThetaHom_apply [Subsingleton G] (ψ : Rtop M ⟶ L) (m : M.V) :
    ThetaHom p M hM L D ψ m
      = D.sgn ((Rep.Hom.hom ψ).toLinearMap ((Rep.Hom.hom (dbl p M hM)).toLinearMap (gen M m))) := by
  show (Rep.Hom.hom (theta p M hM L D ψ)).toLinearMap m = _
  rw [theta_apply]

include hM in
theorem ThetaHom_add [Subsingleton G] (ψ ψ' : Rtop M ⟶ L) :
    ThetaHom p M hM L D (ψ + ψ') = ThetaHom p M hM L D ψ + ThetaHom p M hM L D ψ' := by
  ext m
  rw [AddMonoidHom.add_apply, ThetaHom_apply, ThetaHom_apply, ThetaHom_apply]
  rw [Rep.add_hom, Representation.IntertwiningMap.add_toLinearMap, LinearMap.add_apply, map_add]

include hM in
theorem ThetaHom_zero [Subsingleton G] :
    ThetaHom p M hM L D 0 = 0 := by
  ext m
  rw [ThetaHom_apply, AddMonoidHom.zero_apply]
  rw [Rep.zero_hom, Representation.IntertwiningMap.zero_toLinearMap, LinearMap.zero_apply,
    map_zero]

/-- The lift·`p` functional on the primitives `R ⟶ L`, as an additive map. -/
noncomputable def ThetaHomFun [Subsingleton G] : (Rtop M ⟶ L) →+ (M.V →+ ZMod p) where
  toFun := ThetaHom p M hM L D
  map_zero' := ThetaHom_zero p M hM L D
  map_add' := ThetaHom_add p M hM L D

/-- **The lift·`p` functional** `Hom(R,L) → Hom_{ℤ/p}(M,ℤ/p)`. -/
noncomputable def Theta [Subsingleton G] : (Rtop M ⟶ L) →+ (M.V →ₗ[ZMod p] ZMod p) :=
  (AddMonoidHom.toZModLinearMapEquiv p).toAddMonoidHom.comp (ThetaHomFun p M hM L D)

include hM in
@[simp] theorem Theta_apply [Subsingleton G] (ψ : Rtop M ⟶ L) (m : M.V) :
    Theta p M hM L D ψ m
      = D.sgn ((Rep.Hom.hom ψ).toLinearMap ((Rep.Hom.hom (dbl p M hM)).toLinearMap (gen M m))) := by
  change (ThetaHom p M hM L D ψ).toZModLinearMap p m = _
  rw [AddMonoidHom.coe_toZModLinearMap]
  exact ThetaHom_apply p M hM L D ψ m

include hM in
/-- The lift·`p` functional is insensitive to adding a morphism that extends over `F`. -/
theorem Theta_incl [Subsingleton G] (φ : Ftop M ⟶ L) :
    Theta p M hM L D (jtop M ≫ φ) = 0 := by
  apply LinearMap.ext
  intro m
  rw [Theta_apply, LinearMap.zero_apply]
  have h1 : (Rep.Hom.hom (jtop M ≫ φ)).toLinearMap
      = (Rep.Hom.hom φ).toLinearMap.comp (Rep.Hom.hom (jtop M)).toLinearMap := by
    rw [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap]
  rw [h1, LinearMap.comp_apply, jtop_dbl_apply, map_nsmul, LiftPData.sgn_nsmul_self]

end Killing

section Delta

variable (M : Rep.{0} Coeff G) (L : Rep.{0} Coeff G)

/-- The connecting map `δ : Hom(R,L) → Ext¹(M,L)` of the canonical presentation. -/
noncomputable def delta : (Rtop M ⟶ L) →+ Abelian.Ext M L 1 :=
  ((Work.SSGRoute.freeCoverSES_shortExact M).extClass.precomp L (by norm_num : 1 + 0 = 1)).comp
    (Abelian.Ext.addEquiv₀).symm.toAddMonoidHom

/-- The map `Hom(F,L) → Hom(R,L)` given by restriction along `R ↪ F`. -/
noncomputable def inclMap : (Ftop M ⟶ L) →+ (Rtop M ⟶ L) :=
  AddMonoidHom.mk' (fun φ => jtop M ≫ φ) (fun φ φ' => by simp)

theorem delta_apply (ψ : Rtop M ⟶ L) :
    delta M L ψ
      = (Work.SSGRoute.freeCoverSES_shortExact M).extClass.precomp L (by norm_num : 1 + 0 = 1)
          (Abelian.Ext.mk₀ ψ) := by
  rw [delta, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, Abelian.Ext.addEquiv₀_symm_apply]

theorem delta_apply' (ψ : Rtop M ⟶ L) :
    delta M L ψ
      = (Work.SSGRoute.freeCoverSES_shortExact M).extClass.comp (Abelian.Ext.mk₀ ψ)
          (by norm_num : 1 + 0 = 1) := by
  rw [delta_apply, Work.SSGRoute.ext_precomp_apply]

theorem inclMap_apply (φ : Ftop M ⟶ L) : inclMap M L φ = jtop M ≫ φ := rfl

theorem delta_range : (delta M L).range = ⊤ := by
  rw [AddMonoidHom.range_eq_top]
  intro y
  haveI : Subsingleton (Abelian.Ext (Ftop M) L 1) :=
    Abelian.Ext.subsingleton_of_projective (Ftop M) L 0
  have hzero : (Abelian.Ext.mk₀ (Work.SSGRoute.freeCoverSES M).g).comp y (zero_add 1) = 0 :=
    Subsingleton.elim _ _
  obtain ⟨x, hx⟩ := Abelian.Ext.contravariant_sequence_exact₃
    (Work.SSGRoute.freeCoverSES_shortExact M) L y hzero (n₀ := 0) (add_zero 1)
  refine ⟨Abelian.Ext.addEquiv₀ x, ?_⟩
  rw [delta_apply', ← Work.SSGRoute.ext_eq_mk₀_addEquiv₀ x]
  exact hx

theorem delta_ker : (delta M L).ker = (inclMap M L).range := by
  apply le_antisymm
  · intro ψ hψ
    rw [AddMonoidHom.mem_ker] at hψ
    obtain ⟨w, hw⟩ := Abelian.Ext.contravariant_sequence_exact₁
      (Work.SSGRoute.freeCoverSES_shortExact M) L (Abelian.Ext.mk₀ ψ) (n₁ := 1)
      (add_zero 1) (by rw [← delta_apply']; exact hψ)
    refine ⟨Abelian.Ext.addEquiv₀ w, ?_⟩
    rw [inclMap_apply]
    have hw' : (Abelian.Ext.mk₀ (Work.SSGRoute.freeCoverSES M).f).precomp L (zero_add 0) w
        = (Abelian.Ext.mk₀ (Work.SSGRoute.freeCoverSES M).f).comp w (zero_add 0) :=
      Work.SSGRoute.ext_precomp_apply _ _ _ _
    rw [← hw'] at hw
    have h := congrArg Abelian.Ext.addEquiv₀ hw
    rw [Work.SSGRoute.ext_addEquiv₀_precomp, Work.SSGRoute.ext_addEquiv₀_mk₀] at h
    simpa using h
  · rintro ψ ⟨φ, rfl⟩
    rw [AddMonoidHom.mem_ker, delta_apply', inclMap_apply, ← Abelian.Ext.mk₀_comp_mk₀]
    exact (Work.SSGRoute.freeCoverSES_shortExact M).extClass_comp_assoc (Y := L)
      (n := 0) (n' := 1) (h := by norm_num) (Abelian.Ext.mk₀ φ)

end Delta

section KillKer

variable (p : ℕ) [Fact p.Prime] (M : Rep.{0} Coeff G) (hM : ∀ m : M.V, p • m = 0)
  [Module (ZMod p) M.V] (L : Rep.{0} Coeff G) (D : LiftPData p L)

include hM in
theorem theta_kills_ker [Subsingleton G] :
    (delta M L).ker ≤ (Theta p M hM L D).ker := by
  intro ψ hψ
  rw [delta_ker] at hψ
  obtain ⟨φ, rfl⟩ := hψ
  rw [AddMonoidHom.mem_ker]
  exact Theta_incl p M hM L D φ

end KillKer

section Ell

/-- A homomorphism whose kernel contains the kernel of a surjection descends to the target. -/
theorem exists_lift_of_surjective {G' H T : Type*} [AddGroup G'] [AddGroup H] [AddCommGroup T]
    (f : G' →+ H) (hf : Function.Surjective f) (g : G' →+ T) (hg : f.ker ≤ g.ker) :
    ∃ F : H →+ T, F.comp f = g := by
  have key : ∀ x y : G', f x = f y → g x = g y := by
    intro x y hxy
    have h : x - y ∈ f.ker := by
      rw [AddMonoidHom.mem_ker, map_sub, hxy, sub_self]
    have h2 : x - y ∈ g.ker := hg h
    rw [AddMonoidHom.mem_ker, map_sub] at h2
    exact sub_eq_zero.mp h2
  refine ⟨{ toFun := fun h => g (Classical.choose (hf h))
            map_zero' := ?_
            map_add' := ?_ }, ?_⟩
  · show g (Classical.choose (hf 0)) = 0
    rw [key (Classical.choose (hf 0)) 0 (by rw [Classical.choose_spec (hf 0), map_zero])]
    simp
  · intro h h'
    show g (Classical.choose (hf (h + h')))
      = g (Classical.choose (hf h)) + g (Classical.choose (hf h'))
    rw [← key (Classical.choose (hf h) + Classical.choose (hf h')) (Classical.choose (hf (h + h')))
      (by rw [map_add, Classical.choose_spec (hf h), Classical.choose_spec (hf h'),
        Classical.choose_spec (hf (h + h'))]), map_add]
  · ext x
    show g (Classical.choose (hf (f x))) = g x
    exact key (Classical.choose (hf (f x))) x (by rw [Classical.choose_spec (hf (f x))])

end Ell

section EllDef

variable (p : ℕ) [Fact p.Prime] (M : Rep.{0} Coeff G) (hM : ∀ m : M.V, p • m = 0)
  [Module (ZMod p) M.V] (L : Rep.{0} Coeff G) (D : LiftPData p L)

/-- **The lift·`p` functional on `Ext¹(M,L)`**, obtained by descending the lift·`p` functional on
the primitives `R ⟶ L` along the connecting map `δ`. -/
noncomputable def ell [Subsingleton G] : Abelian.Ext M L 1 →+ (M.V →ₗ[ZMod p] ZMod p) :=
  (exists_lift_of_surjective (delta M L) (AddMonoidHom.range_eq_top.mp (delta_range M L))
    (Theta p M hM L D) (theta_kills_ker p M hM L D)).choose

include hM in
theorem ell_delta [Subsingleton G] (ψ : Rtop M ⟶ L) :
    ell p M hM L D (delta M L ψ) = Theta p M hM L D ψ := by
  have h := (exists_lift_of_surjective (delta M L) (AddMonoidHom.range_eq_top.mp (delta_range M L))
    (Theta p M hM L D) (theta_kills_ker p M hM L D)).choose_spec
  have h2 : (ell p M hM L D).comp (delta M L) = Theta p M hM L D := h
  have h3 := congrArg (fun (g : (Rtop M ⟶ L) →+ (M.V →ₗ[ZMod p] ZMod p)) => g ψ) h2
  rwa [AddMonoidHom.comp_apply] at h3

end EllDef

/-! ## Two extension lemmas for `ℤ/p`-valued functionals -/

section Extend

/-- A `ℤ/p`-linear functional on a submodule of a `ℤ/p`-vector space extends to the whole space. -/
theorem exists_linearMap_extend_of_submodule {p : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V]
    [Module (ZMod p) V] (K : Submodule (ZMod p) V) (f : K →ₗ[ZMod p] ZMod p) :
    ∃ F : V →ₗ[ZMod p] ZMod p, ∀ k : K, F k = f k := by
  obtain ⟨K', hK'⟩ := Submodule.exists_isCompl K
  refine ⟨f.comp ((LinearMap.fst (ZMod p) K K').comp
    (Submodule.prodEquivOfIsCompl K K' hK').symm.toLinearMap), ?_⟩
  intro k
  have h1 : (Submodule.prodEquivOfIsCompl K K' hK').symm (k : V) = (k, 0) :=
    Submodule.prodEquivOfIsCompl_symm_apply_left K K' hK' k
  show f ((LinearMap.fst (ZMod p) K K')
    ((Submodule.prodEquivOfIsCompl K K' hK').symm (k : V))) = f k
  rw [h1]
  simp

/-- A `ℤ/p`-valued additive functional on a subgroup of a `ℤ/p`-vector space extends. -/
theorem exists_addHom_extend_of_subgroup_zmod {p : ℕ} [Fact p.Prime] {V : Type*}
    [AddCommGroup V] [Module (ZMod p) V] (K : AddSubgroup V) (f : K →+ ZMod p) :
    ∃ F : V →+ ZMod p, ∀ k : K, F k = f k := by
  obtain ⟨F', hF'⟩ := exists_linearMap_extend_of_submodule (AddSubgroup.toZModSubmodule p K)
    (f.toZModLinearMap p)
  refine ⟨F'.toAddMonoidHom, fun k => ?_⟩
  have hk : F' (k : V) = f.toZModLinearMap p (⟨(k : V), k.2⟩ :
      ↥(AddSubgroup.toZModSubmodule p K)) := hF' ⟨(k : V), k.2⟩
  change F' (k : V) = f k
  rw [hk]
  rfl

/-- **Extension along an injective additive map with a "division by `p`".**  If `jj : R ↪ F` is
injective and `dbl : F →+ R` satisfies `jj (dbl x) = p • x`, then any `ℤ/p`-valued functional on `R`
which kills the image of `dbl` (equivalently `R ∩ pF`) extends to `F` along `jj`. -/
theorem extendAlongInjective' {p : ℕ} [Fact p.Prime] {R F : Type*} [AddCommGroup R]
    [AddCommGroup F] (jj : R →+ F) (hinj : Function.Injective jj) (dbl : F →+ R)
    (hdbl : ∀ x : F, jj (dbl x) = p • x) (ε : R →+ ZMod p) (hε : ∀ x : F, ε (dbl x) = 0) :
    ∃ η : F →+ ZMod p, ∀ r : R, η (jj r) = ε r := by
  let K : AddSubgroup F := (p • AddMonoidHom.id F).range
  have hKmem : ∀ x : F, p • x ∈ K := fun x => ⟨x, by
    rw [AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply]⟩
  letI : Module (ZMod p) (F ⧸ K) := QuotientAddGroup.zmodModule hKmem
  let H : AddSubgroup F := jj.range
  let QH : AddSubgroup (F ⧸ K) := H.map (QuotientAddGroup.mk' K)
  have hwell : ∀ r r' : R, (QuotientAddGroup.mk' K) (jj r) = (QuotientAddGroup.mk' K) (jj r') →
      ε r = ε r' := by
    intro r r' h
    obtain ⟨z, hzK, hz⟩ := (QuotientAddGroup.mk'_eq_mk' K).mp h
    have h1 : jj (r - r') ∈ K := by
      have h2 : jj (r - r') = -z := by
        rw [map_sub, ← hz]
        abel
      rw [h2]
      exact K.neg_mem hzK
    obtain ⟨x, hx⟩ := h1
    have h3 : r - r' = dbl x := hinj (by
      rw [← hx, hdbl, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply])
    have h4 : ε (r - r') = 0 := by rw [h3, hε x]
    rw [map_sub] at h4
    exact sub_eq_zero.mp h4
  have hex : ∀ q : ↥QH, ∃ r : R, (QuotientAddGroup.mk' K) (jj r) = (q : F ⧸ K) := by
    intro q
    obtain ⟨y, hyH, hyq⟩ := AddSubgroup.mem_map.mp q.2
    obtain ⟨r, hr⟩ := hyH
    exact ⟨r, by rw [hr, hyq]⟩
  have fbar_spec : ∀ (q : ↥QH) (r : R), (QuotientAddGroup.mk' K) (jj r) = (q : F ⧸ K) →
      ε r = ε (Classical.choose (hex q)) := by
    intro q r hr
    exact hwell r _ (by rw [hr, Classical.choose_spec (hex q)])
  let fbar : ↥QH →+ ZMod p :=
    { toFun := fun q => ε (Classical.choose (hex q))
      map_zero' := by
        have h := fbar_spec 0 0 (by simp)
        rw [← h, map_zero]
      map_add' := fun q q' => by
        have h := fbar_spec (q + q')
          (Classical.choose (hex q) + Classical.choose (hex q'))
          (by
            have h1 : jj (Classical.choose (hex q) + Classical.choose (hex q'))
                = jj (Classical.choose (hex q)) + jj (Classical.choose (hex q')) :=
              map_add jj _ _
            rw [h1, map_add (QuotientAddGroup.mk' K), Classical.choose_spec (hex q),
              Classical.choose_spec (hex q'), AddSubgroup.coe_add])
        rw [← h, map_add] }
  obtain ⟨F', hF'⟩ := exists_addHom_extend_of_subgroup_zmod QH fbar
  refine ⟨F'.comp (QuotientAddGroup.mk' K), fun r => ?_⟩
  set q : QH := ⟨(QuotientAddGroup.mk' K) (jj r),
    AddSubgroup.mem_map.mpr ⟨jj r, ⟨r, rfl⟩, rfl⟩⟩ with hq
  have h1 : F' ((QuotientAddGroup.mk' K) (jj r)) = fbar q := by
    rw [hq]
    exact hF' q
  show F' ((QuotientAddGroup.mk' K) (jj r)) = ε r
  rw [h1]
  show ε (Classical.choose (hex q)) = ε r
  exact hwell _ r (Classical.choose_spec (hex q))

end Extend

/-! ## The realization rule for an arbitrary short exact presentation -/

section ExactElem

open CategoryTheory

/-- Concrete exactness criterion for short complexes of representations (elementwise form of
`ker g = im f`, transported along the faithful forgetful functor to `ModuleCat`). -/
theorem rep_shortComplex_exact_iff {R : Type} [Ring R] {G : Type} [Group G]
    (S : ShortComplex (Rep.{0} R G)) :
    S.Exact ↔ ∀ (x₂ : S.X₂.V), S.g.hom x₂ = 0 → ∃ x₁ : S.X₁.V, S.f.hom x₁ = x₂ := by
  rw [← ShortComplex.exact_map_iff_of_faithful (S := S) (forget₂ (Rep.{0} R G) (ModuleCat.{0} R))]
  exact ShortComplex.moduleCat_exact_iff _

end ExactElem

section Comparison

variable {G : Type} [Group G] [Fintype G]

/-- **Comparison of a short exact presentation with the canonical free cover.** -/
theorem exists_comparison (S : ShortComplex (Rep.{0} Coeff G)) (hS : S.ShortExact)
    (M : Rep.{0} Coeff G) (eS : S.X₃ ≅ M) :
    ∃ f : Work.SSGRoute.freeCoverSES M ⟶ S, f.τ₃ = eS.inv ∧
      ∀ m : M.V, (Rep.Hom.hom S.g) ((Rep.Hom.hom f.τ₂) (gen M m)) = (Rep.Hom.hom eS.inv) m := by
  classical
  haveI : Epi S.g := hS.epi_g
  haveI : Mono S.f := hS.mono_f
  have hsurj : ∀ m : M.V, ∃ x : S.X₂.V, (Rep.Hom.hom S.g) x = (Rep.Hom.hom eS.inv) m :=
    fun m => (Rep.epi_iff_surjective S.g).mp inferInstance _
  let g₂ : M.V → S.X₂.V := fun m => Classical.choose (hsurj m)
  have hg₂ : ∀ m : M.V, (Rep.Hom.hom S.g) (g₂ m) = (Rep.Hom.hom eS.inv) m :=
    fun m => Classical.choose_spec (hsurj m)
  let τ₂ : Ftop M ⟶ S.X₂ := Rep.freeLift Coeff G S.X₂ g₂
  have hτ₂ : ∀ m : M.V, (Rep.Hom.hom τ₂) (gen M m) = g₂ m := fun m =>
    Work.SSGRoute.rep_freeLift_apply_single S.X₂ M.V g₂ m
  have hsq : τ₂ ≫ S.g = ctop M ≫ eS.inv := by
    apply Rep.free_ext Coeff G S.X₃ (τ₂ ≫ S.g) (ctop M ≫ eS.inv)
    intro m
    rw [Rep.comp_apply, Rep.comp_apply, hτ₂, hg₂]
    show (Rep.Hom.hom eS.inv).toLinearMap m
      = (Rep.Hom.hom eS.inv).toLinearMap ((Rep.Hom.hom (ctop M)).toLinearMap (gen M m))
    rw [ctop_gen]
  have hk : (jtop M ≫ τ₂) ≫ S.g = 0 := by
    rw [Category.assoc, hsq, ← Category.assoc, ctop_jtop, Limits.zero_comp]
  let τ₁ : Rtop M ⟶ S.X₁ := hS.exact.lift (jtop M ≫ τ₂) hk
  have hτ₁ : τ₁ ≫ S.f = jtop M ≫ τ₂ := ShortComplex.Exact.lift_f _ _ _
  refine ⟨{ τ₁ := τ₁, τ₂ := τ₂, τ₃ := eS.inv, comm₁₂ := hτ₁, comm₂₃ := hsq }, rfl, ?_⟩
  intro m
  rw [hτ₂, hg₂]

end Comparison

/-! ## Surjectivity of the lift·`p` functional -/

/-- A `ℤ/p`-valued functional on a subgroup `H ≥ pR` of an abelian group `R`, vanishing on `pR`,
extends to the whole of `R`. -/
theorem zmodExtend' {p : ℕ} [Fact p.Prime] {R : Type*} [AddCommGroup R]
    (H : AddSubgroup R) (hle : ∀ r : R, p • r ∈ H) (f : H →+ ZMod p)
    (hf : ∀ r : R, f ⟨p • r, hle r⟩ = 0) :
    ∃ F : R →+ ZMod p, ∀ h : H, F h = f h := by
  refine extendAlongInjective' H.subtype (fun x y hxy => Subtype.ext hxy)
    ((p • AddMonoidHom.id R).codRestrict H hle) ?_ f ?_
  · intro x
    change (((⟨(p • AddMonoidHom.id R) x, hle x⟩ : H)) : R) = p • x
    rw [AddSubgroup.coe_mk, AddMonoidHom.nsmul_apply, AddMonoidHom.id_apply]
  · intro x
    show f ((p • AddMonoidHom.id R).codRestrict H hle x) = 0
    rw [AddMonoidHom.codRestrict_apply]
    exact hf x

section Surjectivity

variable (p : ℕ) [Fact p.Prime] (M : Rep.{0} Coeff G) (hM : ∀ m : M.V, p • m = 0)
  [Module (ZMod p) M.V] (L : Rep.{0} Coeff G) (D : LiftPData p L)

include hM in
theorem Theta_surjective [Subsingleton G] (φ : M.V →ₗ[ZMod p] ZMod p) :
    ∃ ψ : Rtop M ⟶ L, Theta p M hM L D ψ = φ := by
  let τ : (Ftop M).V →+ ZMod p :=
    (φ.toAddMonoidHom).comp ((Rep.Hom.hom (ctop M)).toLinearMap.toAddMonoidHom)
  let H : AddSubgroup (Rtop M).V := (Rep.Hom.hom (dbl p M hM)).toLinearMap.range.toAddSubgroup
  let dblH : (Ftop M).V →+ H :=
    ((Rep.Hom.hom (dbl p M hM)).toLinearMap.toAddMonoidHom).codRestrict H (fun x => ⟨x, rfl⟩)
  have hdblH : ∀ x : (Ftop M).V, ((dblH x : H) : (Rtop M).V)
      = (Rep.Hom.hom (dbl p M hM)).toLinearMap x := fun x => rfl
  have hbij : Function.Bijective dblH := by
    constructor
    · intro x y hxy
      have h : (Rep.Hom.hom (dbl p M hM)).toLinearMap x
          = (Rep.Hom.hom (dbl p M hM)).toLinearMap y := by
        rw [← hdblH x, ← hdblH y, hxy]
      exact dbl_injective p (Fact.out : p.Prime).ne_zero M hM h
    · intro h
      obtain ⟨x, hx⟩ := h.2
      exact ⟨x, Subtype.ext (by rw [hdblH]; exact hx)⟩
  let e : (Ftop M).V ≃+ H := AddEquiv.ofBijective dblH hbij
  have he : ∀ x : (Ftop M).V, e x = dblH x := fun x => rfl
  let σ₀ : H →+ ZMod p := τ.comp e.symm.toAddMonoidHom
  have hle : ∀ r : (Rtop M).V, p • r ∈ H := fun r =>
    ⟨(Rep.Hom.hom (jtop M)).toLinearMap r, dbl_jtop_apply p M hM r⟩
  have hf : ∀ r : (Rtop M).V, σ₀ ⟨p • r, hle r⟩ = 0 := by
    intro r
    have h1 : (⟨p • r, hle r⟩ : H) = dblH ((Rep.Hom.hom (jtop M)).toLinearMap r) := by
      apply Subtype.ext
      show p • r = (Rep.Hom.hom (dbl p M hM)).toLinearMap ((Rep.Hom.hom (jtop M)).toLinearMap r)
      rw [dbl_jtop_apply]
    rw [h1]
    show τ (e.symm (dblH ((Rep.Hom.hom (jtop M)).toLinearMap r))) = 0
    rw [← he, e.symm_apply_apply]
    show φ ((Rep.Hom.hom (ctop M)).toLinearMap ((Rep.Hom.hom (jtop M)).toLinearMap r)) = 0
    rw [ctop_jtop_apply, map_zero]
  obtain ⟨σ, hσ⟩ := zmodExtend' H hle σ₀ hf
  refine ⟨repHomOfAddHom (Rtop M) L (D.liftS.comp σ), ?_⟩
  apply LinearMap.ext
  intro m
  rw [Theta_apply, repHomOfAddHom_apply, AddMonoidHom.comp_apply, D.hlift]
  show σ ((dblH (gen M m) : H) : (Rtop M).V) = φ m
  rw [hσ (dblH (gen M m))]
  show τ (e.symm (dblH (gen M m))) = φ m
  rw [← he, e.symm_apply_apply]
  show φ ((Rep.Hom.hom (ctop M)).toLinearMap (gen M m)) = φ m
  rw [ctop_gen]

end Surjectivity

/-! ## Injectivity of the lift·`p` functional -/

section Injectivity

variable (p : ℕ) [Fact p.Prime] (M : Rep.{0} Coeff G) (hM : ∀ m : M.V, p • m = 0)
  [Module (ZMod p) M.V] (L : Rep.{0} Coeff G) (D : LiftPData p L)

include hM in
theorem delta_eq_zero_of_Theta_eq_zero [Subsingleton G] (ψ : Rtop M ⟶ L)
    (hψ : Theta p M hM L D ψ = 0) : delta M L ψ = 0 := by
  have ha : ∀ m : M.V, ∃ a : L.V, p • a = (Rep.Hom.hom ψ).toLinearMap
      ((Rep.Hom.hom (dbl p M hM)).toLinearMap (gen M m)) := fun m => by
    have hm : Theta p M hM L D ψ m = 0 := by rw [hψ]; rfl
    rw [Theta_apply] at hm
    exact (D.hkrn _).mp hm
  let a : M.V → L.V := fun m => Classical.choose (ha m)
  have ha' : ∀ m : M.V, p • a m = (Rep.Hom.hom ψ).toLinearMap
      ((Rep.Hom.hom (dbl p M hM)).toLinearMap (gen M m)) := fun m => Classical.choose_spec (ha m)
  let φ₀ : Ftop M ⟶ L := Rep.freeLift Coeff G L a
  have hφ₀ : ∀ m : M.V, (Rep.Hom.hom φ₀).toLinearMap (gen M m) = a m := fun m =>
    Work.SSGRoute.rep_freeLift_apply_single L M.V a m
  let ε : Rtop M ⟶ L := ψ - jtop M ≫ φ₀
  have hε_apply : ∀ r : (Rtop M).V, (Rep.Hom.hom ε).toLinearMap r
      = (Rep.Hom.hom ψ).toLinearMap r - (Rep.Hom.hom (jtop M ≫ φ₀)).toLinearMap r := by
    intro r
    rw [show ε = ψ - jtop M ≫ φ₀ from rfl, Rep.sub_hom,
      Representation.IntertwiningMap.sub_toLinearMap, LinearMap.sub_apply]
  have hε1 : dbl p M hM ≫ ε = 0 := by
    apply Rep.free_ext Coeff G L (dbl p M hM ≫ ε) 0
    intro m
    rw [Rep.comp_apply]
    show (Rep.Hom.hom ε).toLinearMap ((Rep.Hom.hom (dbl p M hM)).toLinearMap (gen M m)) = 0
    rw [hε_apply, Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
      jtop_dbl_apply, map_nsmul, hφ₀, ha']
    exact sub_self _
  have hε2 : p • ε = 0 := by
    have h1 : (jtop M ≫ dbl p M hM) ≫ ε = 0 := by
      rw [Category.assoc, hε1, Limits.comp_zero]
    rw [jtop_dbl, Preadditive.nsmul_comp, Category.id_comp] at h1
    exact h1
  have hεp : ∀ r : (Rtop M).V, p • ((Rep.Hom.hom ε).toLinearMap r) = 0 := by
    intro r
    have h2 := congrArg (fun f : Rtop M ⟶ L => (Rep.Hom.hom f) r) hε2
    rw [Rep.nsmul_hom, Rep.zero_hom] at h2
    simp only [Representation.IntertwiningMap.coe_nsmul, Pi.smul_apply] at h2
    simpa using h2
  let εz : (Rtop M).V →+ ZMod p :=
    { toFun := fun r => Classical.choose (D.mem_range_liftS (hεp r))
      map_zero' := by
        apply D.hinj
        show D.liftS (Classical.choose (D.mem_range_liftS (hεp 0))) = D.liftS 0
        rw [Classical.choose_spec (D.mem_range_liftS (hεp 0))]
        simp
      map_add' := fun x y => by
        apply D.hinj
        show D.liftS (Classical.choose (D.mem_range_liftS (hεp (x + y))))
          = D.liftS (Classical.choose (D.mem_range_liftS (hεp x))
            + Classical.choose (D.mem_range_liftS (hεp y)))
        calc D.liftS (Classical.choose (D.mem_range_liftS (hεp (x + y))))
            = (Rep.Hom.hom ε).toLinearMap (x + y) :=
              Classical.choose_spec (D.mem_range_liftS (hεp (x + y)))
          _ = (Rep.Hom.hom ε).toLinearMap x + (Rep.Hom.hom ε).toLinearMap y :=
              map_add _ x y
          _ = D.liftS (Classical.choose (D.mem_range_liftS (hεp x))
                + Classical.choose (D.mem_range_liftS (hεp y))) := by
              rw [map_add, Classical.choose_spec (D.mem_range_liftS (hεp x)),
                Classical.choose_spec (D.mem_range_liftS (hεp y))] }
  have hεz : ∀ r : (Rtop M).V, D.liftS (εz r) = (Rep.Hom.hom ε).toLinearMap r := fun r =>
    Classical.choose_spec (D.mem_range_liftS (hεp r))
  obtain ⟨η, hη⟩ := extendAlongInjective'
    ((Rep.Hom.hom (jtop M)).toLinearMap.toAddMonoidHom)
    (fun x y hxy => (Rep.mono_iff_injective (jtop M)).mp inferInstance hxy)
    ((Rep.Hom.hom (dbl p M hM)).toLinearMap.toAddMonoidHom)
    (fun x => jtop_dbl_apply p M hM x)
    εz
    (fun x => by
      have h3 : (Rep.Hom.hom ε).toLinearMap ((Rep.Hom.hom (dbl p M hM)).toLinearMap x) = 0 := by
        have h4 := congrArg (fun f : Ftop M ⟶ L => (Rep.Hom.hom f).toLinearMap x) hε1
        rwa [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
          Rep.zero_hom, Representation.IntertwiningMap.zero_toLinearMap,
          LinearMap.zero_apply] at h4
      apply D.hinj
      rw [hεz]
      show (Rep.Hom.hom ε).toLinearMap ((Rep.Hom.hom (dbl p M hM)).toLinearMap x) = D.liftS 0
      rw [h3, map_zero])
  let εL : Ftop M ⟶ L := repHomOfAddHom (Ftop M) L (D.liftS.comp η)
  have hεL : jtop M ≫ εL = ε := by
    apply Rep.hom_ext
    rw [Rep.hom_comp, Representation.IntertwiningMap.ext_iff]
    apply LinearMap.ext
    intro r
    simp only [Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply]
    change D.liftS (η (((Rep.Hom.hom (jtop M)).toLinearMap).toAddMonoidHom r))
      = (Rep.Hom.hom ε).toLinearMap r
    rw [hη r, hεz r]
  have hψ' : ψ = jtop M ≫ (φ₀ + εL) := by
    rw [Preadditive.comp_add]
    have hsub : ε = ψ - (jtop M ≫ φ₀) := rfl
    have : (jtop M ≫ φ₀) + ε = ψ := by rw [hsub, add_sub_cancel]
    rw [← this, hεL]
  have hker : ψ ∈ (delta M L).ker := by
    rw [delta_ker]
    exact ⟨φ₀ + εL, by rw [inclMap_apply]; exact hψ'.symm⟩
  simpa [AddMonoidHom.mem_ker] using hker

include hM in
theorem ell_injective [Subsingleton G] : Function.Injective (ell p M hM L D) := by
  intro c c' hcc
  obtain ⟨ψ, rfl⟩ := AddMonoidHom.range_eq_top.mp (delta_range M L) c
  obtain ⟨ψ', rfl⟩ := AddMonoidHom.range_eq_top.mp (delta_range M L) c'
  rw [ell_delta, ell_delta] at hcc
  have h0 : Theta p M hM L D (ψ - ψ') = 0 := by
    rw [map_sub, hcc, sub_self]
  have h1 := delta_eq_zero_of_Theta_eq_zero p M hM L D (ψ - ψ') h0
  rw [map_sub, sub_eq_zero] at h1
  rw [h1]

end Injectivity

/-! ## Naturality of the connecting class (local copies, to keep the file self-contained) -/

section ExtNat

open CategoryTheory

/-- Naturality of the connecting class, in composition form. -/
theorem extClass_naturality_comp' {G : Type} [Group G] (L : Rep.{0} Coeff G)
    {S₁ S₂ : ShortComplex (Rep.{0} Coeff G)} (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact)
    (f : S₁ ⟶ S₂) (ψ : S₂.X₁ ⟶ L) :
    (Abelian.Ext.mk₀ f.τ₃).comp
        (h₂.extClass.comp (Abelian.Ext.mk₀ ψ) (add_zero 1)) (zero_add 1)
      = h₁.extClass.comp (Abelian.Ext.mk₀ (f.τ₁ ≫ ψ)) (add_zero 1) := by
  rw [← Abelian.Ext.comp_assoc, ← ShortComplex.ShortExact.extClass_naturality h₁ h₂ f,
    Abelian.Ext.comp_assoc, Abelian.Ext.mk₀_comp_mk₀]
  all_goals omega

/-- Naturality of the connecting class along the canonical free covers. -/
theorem extClass_freeMapKernel' {G : Type} [Group G] [Fintype G]
    (L M M₂ : Rep.{0} Coeff G) (F' : M₂ ⟶ M) (ψ : Rtop M ⟶ L) :
    (Abelian.Ext.mk₀ F').comp
        ((Work.SSGRoute.freeCoverSES_shortExact M).extClass.comp
          (Abelian.Ext.mk₀ ψ) (add_zero 1)) (zero_add 1)
      = (Work.SSGRoute.freeCoverSES_shortExact M₂).extClass.comp
          (Abelian.Ext.mk₀ (Work.SSGRoute.freeMapKernel F' ≫ ψ)) (add_zero 1) := by
  let f : Work.SSGRoute.freeCoverSES M₂ ⟶ Work.SSGRoute.freeCoverSES M :=
    { τ₁ := Work.SSGRoute.freeMapKernel F'
      τ₂ := Work.SSGRoute.freeMap F'
      τ₃ := F'
      comm₁₂ := Work.SSGRoute.freeMapKernel_ι F'
      comm₂₃ := Work.SSGRoute.freeMap_freeCover F' }
  exact extClass_naturality_comp' L (Work.SSGRoute.freeCoverSES_shortExact M₂)
    (Work.SSGRoute.freeCoverSES_shortExact M) f ψ

end ExtNat

section Compat

/-- The comparison of the canonical covers is compatible with the "multiplication by `p`" maps. -/
theorem freeMapKernel_dbl (p : ℕ) {M M₂ : Rep.{0} Coeff G}
    (hM : ∀ m : M.V, p • m = 0) (hM₂ : ∀ m : M₂.V, p • m = 0) (F' : M₂ ⟶ M) (m₂ : M₂.V) :
    (Rep.Hom.hom (Work.SSGRoute.freeMapKernel F')).toLinearMap
        ((Rep.Hom.hom (dbl p M₂ hM₂)).toLinearMap (gen M₂ m₂))
      = (Rep.Hom.hom (dbl p M hM)).toLinearMap (gen M (Rep.Hom.hom F' m₂)) := by
  apply (Rep.mono_iff_injective (jtop M)).mp inferInstance
  change (Rep.Hom.hom (jtop M)).toLinearMap
      ((Rep.Hom.hom (Work.SSGRoute.freeMapKernel F')).toLinearMap
        ((Rep.Hom.hom (dbl p M₂ hM₂)).toLinearMap (gen M₂ m₂)))
    = (Rep.Hom.hom (jtop M)).toLinearMap
      ((Rep.Hom.hom (dbl p M hM)).toLinearMap (gen M (Rep.Hom.hom F' m₂)))
  have hι : ∀ y : (Rtop M₂).V, (Rep.Hom.hom (jtop M)).toLinearMap
        ((Rep.Hom.hom (Work.SSGRoute.freeMapKernel F')).toLinearMap y)
      = (Rep.Hom.hom (Work.SSGRoute.freeMap F')).toLinearMap
          ((Rep.Hom.hom (jtop M₂)).toLinearMap y) := by
    intro y
    have h := congrArg (fun g : Rtop M₂ ⟶ Ftop M => (Rep.Hom.hom g).toLinearMap y)
      (Work.SSGRoute.freeMapKernel_ι F')
    rw [Rep.hom_comp, Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
      Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
      LinearMap.comp_apply] at h
    exact h
  have hgen : (Rep.Hom.hom (Work.SSGRoute.freeMap F')).toLinearMap (gen M₂ m₂)
      = gen M (Rep.Hom.hom F' m₂) := by
    simpa [gen] using Work.SSGRoute.freeMap_generator F' m₂
  rw [hι, jtop_dbl_apply, map_nsmul, hgen, jtop_dbl_apply]

end Compat

/-! ## The realization rule, bijectivity and naturality of the lift·`p` family -/

section Final

/-- In a `ℤ/p`-module, `p • m = 0`. -/
theorem nsmul_self_eq_zero (p : ℕ) {M : Type*} [AddCommGroup M] [Module (ZMod p) M] (m : M) :
    p • m = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod p) p m, ZMod.natCast_self, zero_smul]

variable (p : ℕ) [Fact p.Prime] (M : Rep.{0} Coeff G) (hM : ∀ m : M.V, p • m = 0)
  [Module (ZMod p) M.V] (L : Rep.{0} Coeff G) (D : LiftPData p L)

include hM in
theorem ell_surjective [Subsingleton G] : Function.Surjective (ell p M hM L D) := by
  intro φ
  obtain ⟨ψ, hψ⟩ := Theta_surjective p M hM L D φ
  exact ⟨delta M L ψ, by rw [ell_delta, hψ]⟩

include hM in
theorem ell_bijective [Subsingleton G] : Function.Bijective (ell p M hM L D) :=
  ⟨ell_injective p M hM L D, ell_surjective p M hM L D⟩

include hM in
/-- **The realization rule**: the class `δ(ψ)` of a morphism `ψ` out of the first term of any short
exact presentation of `M` is killed by the lift·`p` functional at `m` exactly when the `p`-lift
obstruction of `ψ` at a lift `v` of `m` is trivial. -/
theorem ell_realization [Subsingleton G] (S : ShortComplex (Rep.{0} Coeff G)) (hS : S.ShortExact)
    (eS : S.X₃ ≅ M) (ψ : S.X₁ ⟶ L) (v : S.X₂.V) (m : M.V)
    (hm : Rep.Hom.hom eS.hom (Rep.Hom.hom S.g v) = m) :
    ell p M hM L D ((Abelian.Ext.mk₀ eS.inv).comp
        (hS.extClass.comp (Abelian.Ext.mk₀ ψ) (add_zero 1)) (zero_add 1)) m = 0 ↔
      ∃ (r : S.X₁.V) (u : L.V), Rep.Hom.hom S.f r = p • v ∧ p • u = Rep.Hom.hom ψ r := by
  classical
  haveI : Mono S.f := hS.mono_f
  obtain ⟨f, hf3, hf2⟩ := exists_comparison S hS M eS
  have hcls : (Abelian.Ext.mk₀ eS.inv).comp
        (hS.extClass.comp (Abelian.Ext.mk₀ ψ) (add_zero 1)) (zero_add 1)
      = delta M L (f.τ₁ ≫ ψ) := by
    rw [← hf3, extClass_naturality_comp' L (Work.SSGRoute.freeCoverSES_shortExact M) hS f ψ,
      delta_apply']
  rw [hcls, ell_delta, Theta_apply]
  set x := (Rep.Hom.hom (dbl p M hM)).toLinearMap (gen M m) with hx
  set r₀ := (Rep.Hom.hom f.τ₁).toLinearMap x with hr₀
  set v' := (Rep.Hom.hom f.τ₂).toLinearMap (gen M m) with hv'
  have hτ : (Rep.Hom.hom (f.τ₁ ≫ ψ)).toLinearMap x = (Rep.Hom.hom ψ).toLinearMap r₀ := by
    rw [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply, hr₀]
  rw [hτ]
  have hv'Sg : (Rep.Hom.hom S.g) v' = (Rep.Hom.hom eS.inv) m := hf2 m
  have hvSg : (Rep.Hom.hom S.g) v = (Rep.Hom.hom eS.inv) m := by
    have h : (Rep.Hom.hom eS.inv) ((Rep.Hom.hom eS.hom) ((Rep.Hom.hom S.g) v))
        = (Rep.Hom.hom eS.inv) m := by rw [hm]
    simpa using h
  have hSf_r₀ : (Rep.Hom.hom S.f) r₀ = p • v' := by
    have h := congrArg (fun g : Rtop M ⟶ S.X₂ => (Rep.Hom.hom g).toLinearMap x) f.comm₁₂
    rw [Rep.hom_comp, Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
      Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
      LinearMap.comp_apply] at h
    have hx' : (Rep.Hom.hom (jtop M)).toLinearMap x = p • gen M m := by
      rw [hx]
      exact jtop_dbl_apply p M hM (gen M m)
    rw [hx', map_nsmul] at h
    show (Rep.Hom.hom S.f).toLinearMap r₀ = p • v'
    rw [hr₀, hv']
    exact h
  obtain ⟨r', hr'⟩ : (∃ y : S.X₁.V, (Rep.Hom.hom S.f) y = v - v') := by
    refine (rep_shortComplex_exact_iff S).mp hS.exact (v - v') ?_
    rw [map_sub, hvSg, hv'Sg, sub_self]
  have hSf_can : (Rep.Hom.hom S.f) (r₀ + p • r') = p • v := by
    rw [map_add, map_nsmul, hSf_r₀, hr', ← nsmul_add]
    congr 1
    abel
  have hcan : D.sgn ((Rep.Hom.hom ψ).toLinearMap (r₀ + p • r'))
      = D.sgn ((Rep.Hom.hom ψ).toLinearMap r₀) := by
    have h1 : (Rep.Hom.hom ψ).toLinearMap (r₀ + p • r')
        = (Rep.Hom.hom ψ).toLinearMap r₀ + (Rep.Hom.hom ψ).toLinearMap (p • r') :=
      map_add _ r₀ (p • r')
    have h2 : (Rep.Hom.hom ψ).toLinearMap (p • r')
        = p • ((Rep.Hom.hom ψ).toLinearMap r') :=
      map_nsmul _ p r'
    rw [h1, h2, map_add D.sgn, LiftPData.sgn_nsmul_self, add_zero]
  have huniq : ∀ r : S.X₁.V, (Rep.Hom.hom S.f) r = p • v →
      D.sgn ((Rep.Hom.hom ψ).toLinearMap r) = D.sgn ((Rep.Hom.hom ψ).toLinearMap r₀) := by
    intro r hr
    have h1 : (Rep.Hom.hom S.f) r = (Rep.Hom.hom S.f) (r₀ + p • r') := by rw [hr, hSf_can]
    have h2 : r = r₀ + p • r' :=
      (Rep.mono_iff_injective S.f).mp inferInstance h1
    rw [h2]
    exact hcan
  constructor
  · intro h0
    rw [← hcan] at h0
    obtain ⟨u, hu⟩ := (D.hkrn ((Rep.Hom.hom ψ).toLinearMap (r₀ + p • r'))).mp h0
    exact ⟨r₀ + p • r', u, hSf_can, hu⟩
  · rintro ⟨r, u, hr, hu⟩
    rw [← huniq r hr]
    exact (D.hkrn ((Rep.Hom.hom ψ).toLinearMap r)).mpr ⟨u, hu⟩

end Final

section Natural

variable (p : ℕ) [Fact p.Prime] (M : Rep.{0} Coeff G) (hM : ∀ m : M.V, p • m = 0)
  [Module (ZMod p) M.V] (L : Rep.{0} Coeff G) (D : LiftPData p L)

include hM in
/-- **Naturality of the lift·`p` functional in the coefficient module.** -/
theorem ell_natural [Subsingleton G] (M₂ : Rep.{0} Coeff G) [Module (ZMod p) M₂.V]
    (hM₂ : ∀ m : M₂.V, p • m = 0) (F' : M₂ ⟶ M) (x : Abelian.Ext M L 1) (m₂ : M₂.V) :
    ell p M₂ hM₂ L D ((Abelian.Ext.mk₀ F').comp x (zero_add 1)) m₂
      = ell p M hM L D x ((Rep.Hom.hom F').toLinearMap m₂) := by
  obtain ⟨ψ, rfl⟩ := AddMonoidHom.range_eq_top.mp (delta_range M L) x
  rw [delta_apply' (M := M) (L := L) ψ]
  rw [extClass_freeMapKernel' L M M₂ F' ψ]
  rw [← delta_apply' (M := M₂) (L := L) (Work.SSGRoute.freeMapKernel F' ≫ ψ),
    ← delta_apply' (M := M) (L := L) ψ]
  rw [ell_delta p M₂ hM₂ L D (Work.SSGRoute.freeMapKernel F' ≫ ψ), ell_delta p M hM L D ψ]
  rw [Theta_apply, Theta_apply]
  congr 1
  rw [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, LinearMap.comp_apply,
    freeMapKernel_dbl p hM hM₂ F' m₂]
  rfl

end Natural

/-! ## The lift·`p` family -/

/-- **The lift·`p` family for a trivial group.**  For a coefficient `L` with the sign data
(`LiftPData`), there is a family, natural in the finite `ℤ/p`-module `M`, of additive bijections
`Ext¹(M,L) ≅ Hom(M, ℤ/p)` which satisfies the lift·`p` realization rule for every short exact
presentation of `M`. -/
theorem botLiftFamily [Subsingleton G] (p : ℕ) [Fact p.Prime] (L : Rep.{0} Coeff G)
    (D : LiftPData p L) :
    ∃ ell : ∀ (M : Rep.{0} Coeff G) [Module (ZMod p) M.V],
        Abelian.Ext M L 1 →+ (M.V →ₗ[ZMod p] ZMod p),
      (∀ (M : Rep.{0} Coeff G) [Module (ZMod p) M.V], Function.Bijective (ell M)) ∧
      (∀ (M : Rep.{0} Coeff G) [Module (ZMod p) M.V]
        (S : ShortComplex (Rep.{0} Coeff G)) (hS : S.ShortExact) (eS : S.X₃ ≅ M)
        (ψ : S.X₁ ⟶ L) (v : S.X₂.V) (m : M.V)
        (hm : Rep.Hom.hom eS.hom (Rep.Hom.hom S.g v) = m),
        ell M ((Abelian.Ext.mk₀ eS.inv).comp
            (hS.extClass.comp (Abelian.Ext.mk₀ ψ) (add_zero 1)) (zero_add 1)) m = 0 ↔
          ∃ (r : S.X₁.V) (u : L.V), Rep.Hom.hom S.f r = p • v ∧ p • u = Rep.Hom.hom ψ r) ∧
      (∀ (M : Rep.{0} Coeff G) [Module (ZMod p) M.V]
        (M₂ : Rep.{0} Coeff G) [Module (ZMod p) M₂.V]
        (F' : M₂ ⟶ M) (x : Abelian.Ext M L 1) (m₂ : M₂.V),
        ell M₂ ((Abelian.Ext.mk₀ F').comp x (zero_add 1)) m₂
          = ell M x ((Rep.Hom.hom F').toLinearMap m₂)) := by
  classical
  refine ⟨fun M _ => ell p M (fun m => nsmul_self_eq_zero p m) L D, ?_, ?_, ?_⟩
  · intro M _
    exact ell_bijective p M (fun m => nsmul_self_eq_zero p m) L D
  · intro M _ S hS eS ψ v m hm
    exact ell_realization p M (fun m => nsmul_self_eq_zero p m) L D S hS eS ψ v m hm
  · intro M _ M₂ _ F' x m₂
    exact ell_natural p M (fun m => nsmul_self_eq_zero p m) L D M₂
      (fun m => nsmul_self_eq_zero p m) F' x m₂

end Work.SSGRoute.ArchSplit2

import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.PTdualControl.detectorDescent
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTdualControl

open CategoryTheory SSGRoute.PTExt

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- **Presentation-independence of the level pairing.**

If `hff : f = f'`, the level pairing computed with the level map `f` and the class
`h'.comp (mk₀ (eqToHom …))` (where the `eqToHom` is the transport of a coefficient module along
`hff`) equals the level pairing computed with `f'` and `h'`.  This is the bookkeeping that lets
one replace a level map by a definitionally equal one inside `levelPair`. -/
theorem levelPair_congr_hom {G H : Type} [Group G] [Group H] (f f' : H →* G) (hff : f = f')
    (A : Rep.{0} Coeff G) (x : Abelian.Ext.{0} A (unitRep G) 1) (h' : extH (Rep.res f' A) 1) :
    levelPair f (trivResInv f Coeff) x
      (h'.comp (Abelian.Ext.mk₀ (eqToHom (congrArg (fun t => Rep.res t A) hff.symm))) (add_zero 1))
    = levelPair f' (trivResInv f' Coeff) x h' := by
  cases hff
  rw [show congrArg (fun t => Rep.res t A) (rfl : f = f).symm = rfl from Subsingleton.elim _ _,
    eqToHom_refl]
  simp only [levelPair, extRes]
  rw [Abelian.Ext.comp_mk₀_id]

/-- **Restriction of a class post-composed with a coefficient morphism.**

For a subgroup `D ≤ G`, a morphism of `G`-modules `R : B ⟶ A` and `y ∈ H¹(G, B)`, restricting
`y ≫ mk₀ R` to `D` is the restriction of `y` post-composed with `mk₀ (res D R)`. -/
theorem extHRestrict_comp_mk₀ {G : Type} [Group G] (D : Subgroup G)
    {B A : Rep.{0} Coeff G} (R : B ⟶ A) (y : extH B 1) :
    extHRestrict D (y.comp (Abelian.Ext.mk₀ R) (add_zero 1))
      = (extHRestrict D y).comp (Abelian.Ext.mk₀ (Rep.resMap D.subtype R)) (add_zero 1) := by
  unfold extHRestrict extHMap extRes
  simp only [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc, Abelian.Ext.comp_mk₀_id, Abelian.Ext.mk₀_comp_mk₀]

/-- **The base-change descent for the unramified detector, at one class.**

Tower `k ⊆ K ⊆ K' ⊆ Ω` of number fields with `Ω` algebraically closed, `K'/k` and `K/k` finite
Galois, `p ∤ [K' : K]`, a place `w'` of `K'` lying over a place `w = q` of `K`, and a finite
`p`-torsion `Gal(K/k)`-module `M`.

If the unramified detector holds for the extension `K'/k` at `w'` with the coefficient module
`res_{K'/K} M`, then it holds for `K/k` at `w` with `M`.

Route, with the ingredients already on disk:
* every nonzero `φ ∈ Ext¹_{D_w}(res M, ℤ)` is `δ μ` for a nonzero functional `μ`
  (`Work.E7cOmega.exists_divRep_of_ext_nonzero_aux`);
* the inflated class over `D_{w'}` is `δ (res μ)` (`extRes_extDelta`, in
  `Submission/Work/SSGRoute/PTdualControl/detectorDescent_algebra.lean`) and is nonzero
  (`extDelta_ne_zero`, same module);
* the detector over `K'` supplies a level `L : IntermediateField K' Ω`, a place `q'' | w'` with
  `p ∤ e(q''|q')` and an unramified class `h`;
* view `L` as a level over `K` (`restrictField`, in
  `Submission/Work/SSGRoute/PTdualControl/detectorDescent.lean`), and `q''` as a place over `w`
  with `p ∤ e(q''|q)` (`Work.SSGRoute.PTdualControl.place_ramification_descent`, delegated
  separately; import its module when it lands);
* the pairing over `K` is the pairing over `K'` of the inflated class (`levelPair_inflation`). -/
theorem baseChange_detectsAt (p : ℕ) [Fact p.Prime]
    (k K K' Ω : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Field K'] [NumberField K']
    [Field Ω] [IsAlgClosed Ω]
    [Algebra k K] [Algebra k K'] [Algebra k Ω] [Algebra K K'] [Algebra K Ω] [Algebra K' Ω]
    [IsScalarTower k K K'] [IsScalarTower k K Ω] [IsScalarTower k K' Ω] [IsScalarTower K K' Ω]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k K'] [IsGalois k K']
    [FiniteDimensional K K'] [IsGalois K K']
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (w' : NK.GlobalCFT.Place K')
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K'))
    (hwq' : w' = NK.GlobalCFT.Place.ofFinite q')
    (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (hp : ¬ p ∣ Module.finrank K K')
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (hdet : Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K' Ω w' q' hwq'
      (Rep.res (SSGRoute.PTExt.galRes k K K') M))
    (φ : CategoryTheory.Abelian.Ext.{0} (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M)
      (SSGRoute.PTExt.unitRep ↥(SSGRoute.PTExt.decompK (k := k) w)) 1) (hφ : φ ≠ 0) :
    Work.SSGRoute.Sha2Lib.DetectsAt p k K Ω w q hwq M φ := by
  rw [Work.SSGRoute.Sha2Lib.DetectsAt]
  obtain ⟨μ, hμne, hφμ⟩ := Work.E7cOmega.functional_of_ext_nonzero p k K M hM w φ hφ
  let g1 : ↥(SSGRoute.PTExt.decompK (k:=k) w') →* ↥(SSGRoute.PTExt.decompK (k:=k) w) :=
    Work.SSGRoute.decompKRestrict k K K' w w' hw'
  have hresne : Rep.resMap g1 μ ≠ 0 := by
    intro h
    exact hμne ((Rep.resFunctor g1).map_injective
      (h.trans (Functor.map_zero (Rep.resFunctor g1) _ _).symm))
  let ψ : Abelian.Ext (Rep.res (SSGRoute.PTExt.decompK (k:=k) w').subtype
        (Rep.res (SSGRoute.PTExt.galRes k K K') M))
      (SSGRoute.PTExt.unitRep ↥(SSGRoute.PTExt.decompK (k:=k) w')) 1 :=
    (SSGRoute.PTExt.extRes g1 φ).comp
      (Abelian.Ext.mk₀ (SSGRoute.PTExt.trivResInv g1 SSGRoute.PTExt.Coeff)) (add_zero 1)
  have hψ : ψ = SSGRoute.PTExt.extRes g1 φ := by
    show (SSGRoute.PTExt.extRes g1 φ).comp
      (Abelian.Ext.mk₀ (SSGRoute.PTExt.trivResInv g1 SSGRoute.PTExt.Coeff)) (add_zero 1)
      = SSGRoute.PTExt.extRes g1 φ
    exact Abelian.Ext.comp_mk₀_id (SSGRoute.PTExt.extRes g1 φ)
  have hstep : ψ = (Abelian.Ext.mk₀ (Rep.resMap g1 μ)).comp
      (CategoryTheory.ShortComplex.ShortExact.extClass
        (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := ↥(SSGRoute.PTExt.decompK (k:=k) w'))))
      (zero_add 1) :=
    hψ.trans ((congrArg (SSGRoute.PTExt.extRes g1) hφμ).trans
      (Work.SSGRoute.PTdualControl.extRes_extDelta g1 μ))
  have hψne : ψ ≠ 0 := fun h0 =>
    (Work.SSGRoute.PTdualControl.extDelta_ne_zero (G := ↥(SSGRoute.PTExt.decompK (k:=k) w'))
      p (M := Rep.res g1 (Rep.res (SSGRoute.PTExt.decompK (k:=k) w).subtype M))
      (fun m => hM m) hresne) (hstep.symm.trans h0)
  obtain ⟨L', hL'n, hL'fd, hL'g, q'', hq'', h', hunram, hcop, hpair⟩ := hdet ψ hψne
  let L : IntermediateField K Ω := Work.SSGRoute.PTdualControl.restrictField k K K' Ω L'
  haveI hLn : NumberField ↥L := (inferInstance : NumberField ↥L')
  haveI hLfd : FiniteDimensional k ↥L := (inferInstance : FiniteDimensional k ↥L')
  haveI hLg : IsGalois k ↥L := (inferInstance : IsGalois k ↥L')
  haveI htower : IsScalarTower k K ↥L' :=
    IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext (IsScalarTower.algebraMap_apply k K Ω x))
  have h2 : ¬ p ∣ q'.asIdeal.ramificationIdx' q''.asIdeal :=
    ((Fact.out : p.Prime).coprime_iff_not_dvd).mp hcop.symm
  have harith := Work.SSGRoute.PTdualControl.place_ramification_descent p k K K' ↥L'
    w w' (NK.GlobalCFT.Place.ofFinite q'') hw' hq'' q hwq q' hwq' q'' rfl hp h2
  have hqK : NK.GlobalCFT.Place.LiesOver ((NK.GlobalCFT.Place.ofFinite q'') : NK.GlobalCFT.Place ↥L) w := harith.1
  have hcopK : Nat.Coprime (q.asIdeal.ramificationIdx' q''.asIdeal) p :=
    (((Fact.out : p.Prime).coprime_iff_not_dvd).mpr harith.2.1).symm
  let R : Rep.res (SSGRoute.PTExt.galRes k K' ↥L') (Rep.res (SSGRoute.PTExt.galRes k K K') M)
      ⟶ Rep.res (SSGRoute.PTExt.galRes k K ↥L') M :=
    SSGRoute.PTExt.resResHom (k:=k) (K:=K) (L:=K') (L':=↥L') M
  let h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K ↥L') M) 1 :=
    h'.comp (Abelian.Ext.mk₀ R) (add_zero 1)
  have hunramK : SSGRoute.PTExt.IsUnramifiedClassAt (q'' : IsDedekindDomain.HeightOneSpectrum
      (NumberField.RingOfIntegers ↥L)) h := by
    intro Dsub hD
    rw [show h = h'.comp (Abelian.Ext.mk₀ R) (add_zero 1) from rfl]
    rw [extHRestrict_comp_mk₀ Dsub R h', hunram Dsub hD]
    exact Abelian.Ext.zero_comp _ _ _ _ _
  have key : SSGRoute.PTExt.levelPair
      (Work.SSGRoute.decompKRestrict k K ↥L' w (NK.GlobalCFT.Place.ofFinite q'') harith.1)
      (SSGRoute.PTExt.trivResInv
        (Work.SSGRoute.decompKRestrict k K ↥L' w (NK.GlobalCFT.Place.ofFinite q'') harith.1)
        SSGRoute.PTExt.Coeff)
      φ
      (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L')
        (NK.GlobalCFT.Place.ofFinite q'')) h) ≠ 0 := by
    let M_D : Rep.{0} Coeff ↥(SSGRoute.PTExt.decompK (k:=k) (K:=K) w) :=
      Rep.res (SSGRoute.PTExt.decompK (k:=k) (K:=K) w).subtype M
    let D' : Subgroup (↥L' ≃ₐ[k] ↥L') :=
      SSGRoute.PTExt.decompK (k:=k) (K:=↥L') (NK.GlobalCFT.Place.ofFinite q'')
    let g2 : ↥D' →* ↥(SSGRoute.PTExt.decompK (k:=k) w') :=
      Work.SSGRoute.decompKRestrict k K' ↥L' w' (NK.GlobalCFT.Place.ofFinite q'') hq''
    have hFF : g1.comp g2 = (Work.SSGRoute.decompKRestrict k K ↥L' w
        (NK.GlobalCFT.Place.ofFinite q'') harith.1) := by
      refine MonoidHom.ext (fun σ => Subtype.ext ?_)
      show SSGRoute.PTExt.galRes k K K' (SSGRoute.PTExt.galRes k K' ↥L' (Subtype.val σ : ↥L' ≃ₐ[k] ↥L'))
        = SSGRoute.PTExt.galRes k K ↥L' (Subtype.val σ : ↥L' ≃ₐ[k] ↥L')
      exact SSGRoute.PTExt.galRes_trans (L := K') (L' := ↥L') (Subtype.val σ : ↥L' ≃ₐ[k] ↥L')
    let Y := SSGRoute.PTExt.extHRestrict D' h'
    have ha : SSGRoute.PTExt.extHRestrict D' h = Y.comp (Abelian.Ext.mk₀
        (Rep.resMap D'.subtype R)) (add_zero 1) := by
      rw [show h = h'.comp (Abelian.Ext.mk₀ R) (add_zero 1) from rfl]
      exact extHRestrict_comp_mk₀ D' R h'
    have hT : Rep.resMap D'.subtype R = eqToHom (congrArg (fun t => Rep.res t M_D) hFF) := by
      rw [show Rep.resMap D'.subtype R = (Rep.resFunctor D'.subtype).map R from rfl]
      rw [show R = SSGRoute.PTExt.resResHom (k:=k) (K:=K) (L:=K') (L':=↥L') M from rfl]
      unfold SSGRoute.PTExt.resResHom
      rw [CategoryTheory.eqToHom_map]
    rw [ha, hT]
    rw [levelPair_congr_hom (Work.SSGRoute.decompKRestrict k K ↥L' w
      (NK.GlobalCFT.Place.ofFinite q'') harith.1) (g1.comp g2) hFF.symm M_D φ Y]
    rw [Work.SSGRoute.PTdualControl.levelPair_inflation g1 g2 M_D φ Y]
    exact hpair
  refine ⟨L, hLn, hLfd, hLg, q'', hqK, h, hunramK, hcopK, ?_⟩
  show SSGRoute.PTExt.levelPair
      (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q'') hqK)
      (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L w
        (NK.GlobalCFT.Place.ofFinite q'') hqK) SSGRoute.PTExt.Coeff)
      φ
      (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q'')) h) ≠ 0
  exact key

end Work.SSGRoute.PTdualControl

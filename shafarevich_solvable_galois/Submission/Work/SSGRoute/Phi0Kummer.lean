import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.ExtH1Iso
import Submission.Work.AbsoluteKummer.Basic
import Submission.Work.SSGRoute.augSES_shortExact
import Submission.Work.SSGRoute.exists_zetaCoeff
import Submission.Work.SSGRoute.kummer_level_defs
import Submission.Work.SSGRoute.Phi0Aux
import Submission.Work.SSGRoute.exists_level_pthRoot
import Submission.Work.SSGRoute.exists_pthResIncl
import Submission.Work.SSGRoute.kummerSES_extClass_naturality
import Submission.Work.SSGRoute.exists_factorisation_of_kummer_data
import Submission.Work.SSGRoute.exists_kummer_generator_of_derivCochain
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Work.SSGRoute
namespace Phi0Kummer


open CategoryTheory SSGRoute.PTExt

/-- The computation rule for `ExtH1.phiMap`. -/
theorem phiMap_apply_aux {G : Type} [Group G] (M : Type) [AddCommGroup M]
    [DistribMulAction G M] [SMulCommClass G Coeff M] (hS : (ExtH1.augSES G).ShortExact)
    (f : ExtH1.augI G ⟶ modRep G M) :
    ExtH1.phiMap G M hS f = hS.extClass.comp (Abelian.Ext.mk₀ f) (by norm_num) := rfl

/-- **The Kummer step at the level of extension classes**: the class `c ∪ δ` of the relative
Kummer sequence dies after inflation to `L'`, because the Hilbert 90 element `x` becomes a `p`-th
power at `L'`.  (This is `kummer_inflation_vanish_step`, with its one auxiliary input
`pth_coboundary_lift_aux` replaced by the proved `exists_factorisation_of_kummer_data`.) -/
theorem kummerMainStep
    (k : Type) [Field k] [NumberField k] (L : Type) [Field L] [NumberField L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    (L' : Type) [Field L'] [NumberField L'] [Algebra k L'] [FiniteDimensional k L']
    [IsGalois k L'] [Algebra L L'] [IsScalarTower k L L'] (p : ℕ) [Fact p.Prime]
    (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (z : Rep.trivial SSGRoute.PTExt.Coeff (L ≃ₐ[k] L) (ZMod p) ⟶ Work.SSGRoute.levelUnits k L)
    (hz : ((Additive.toMul (z.hom (1 : ZMod p)) : Lˣ) : L) = algebraMap k L ζ)
    (z' : Rep.trivial SSGRoute.PTExt.Coeff (L' ≃ₐ[k] L') (ZMod p) ⟶ Work.SSGRoute.levelUnits k L')
    (hz' : ((Additive.toMul (z'.hom (1 : ZMod p)) : L'ˣ) : L') = algebraMap k L' ζ)
    (τ₂ : Rep.res (SSGRoute.PTExt.galRes k L L') (Work.SSGRoute.levelUnits k L) ⟶
      Work.SSGRoute.levelUnits k L')
    (τ₃ : Rep.res (SSGRoute.PTExt.galRes k L L') (Work.SSGRoute.pthRepX k L p) ⟶
      Work.SSGRoute.pthRepX k L' p)
    (hτ₂ : ∀ u : Lˣ, τ₂.hom (Additive.ofMul u)
        = Additive.ofMul (Units.map (algebraMap L L').toMonoidHom u))
    (hτ₃ : ∀ u : Lˣ, τ₃.hom ⟨(p:ℕ) • Additive.ofMul u, LinearMap.mem_range_self _ _⟩
        = ⟨(p:ℕ) • Additive.ofMul (Units.map (algebraMap L L').toMonoidHom u),
           LinearMap.mem_range_self _ _⟩)
    (hτ₃sq : ∀ u : Lˣ, τ₃.hom ((Work.SSGRoute.pthMapX k L p).hom (Additive.ofMul u))
        = (Work.SSGRoute.pthMapX k L' p).hom (τ₂.hom (Additive.ofMul u)))
    (c : SSGRoute.PTExt.extH (Work.SSGRoute.pthRepX k L p) 1)
    (f : Work.SSGRoute.ExtH1.augI (L ≃ₐ[k] L) ⟶ Work.SSGRoute.pthRepX k L p)
    (hf : Work.SSGRoute.ExtH1.phiMap (L ≃ₐ[k] L) ↥(Work.SSGRoute.pthSubX L p)
        (Work.SSGRoute.augSES_shortExact (L ≃ₐ[k] L)) f = c)
    (x : Lˣ)
    (hφ : ∀ σ : L ≃ₐ[k] L,
      ((Work.SSGRoute.ExtH1.derivCochain (L ≃ₐ[k] L) f σ : ↥(Work.SSGRoute.pthSubX L p))
          : Additive Lˣ)
        = σ • (Additive.ofMul x) - Additive.ofMul x)
    (hy : ∃ y : L'ˣ, Units.map (algebraMap L L').toMonoidHom x = y ^ p) :
    (SSGRoute.PTExt.extHMap (SSGRoute.PTExt.galRes k L L')
      (SSGRoute.PTExt.trivResInv (SSGRoute.PTExt.galRes k L L') (ZMod p))
      (c.comp (Work.SSGRoute.kummerSESX_shortExact k L p hζ z hz).extClass (by norm_num))
      : SSGRoute.PTExt.extH (Rep.trivial SSGRoute.PTExt.Coeff (L' ≃ₐ[k] L') (ZMod p)) 2) = 0 := by
  classical
  -- the derivation lifts across the augmentation inclusion (proved form of `pth_coboundary_lift_aux`)
  obtain ⟨kk, hkkpt⟩ :=
    exists_factorisation_of_kummer_data k L L' p τ₂ τ₃ hτ₃ hτ₂ f x hy hφ
  have hkk : CategoryTheory.CategoryStruct.comp
        (Rep.resMap (SSGRoute.PTExt.galRes k L L')
          (Work.SSGRoute.ExtH1.augIncl (L ≃ₐ[k] L))) kk
      = CategoryTheory.CategoryStruct.comp
          (Rep.resMap (SSGRoute.PTExt.galRes k L L') f) τ₃ := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    show kk.hom ((Rep.resMap (SSGRoute.PTExt.galRes k L L')
        (Work.SSGRoute.ExtH1.augIncl (L ≃ₐ[k] L))).hom z)
      = τ₃.hom ((Rep.resMap (SSGRoute.PTExt.galRes k L L') f).hom z)
    rw [Rep.resMap_hom_apply, Rep.resMap_hom_apply]
    exact hkkpt z
  -- naturality of the Kummer extension class
  have hnat :=
    kummerSES_extClass_naturality k L L' p ζ hζ z hz z' hz' τ₂ τ₃ hτ₂ hτ₃ hτ₃sq
  -- the augmentation extension class kills the augmentation inclusion
  have hkill : ((augSES_shortExact (L ≃ₐ[k] L)).map_of_exact
        (Rep.resFunctor (SSGRoute.PTExt.galRes k L L'))).extClass.comp
        (Abelian.Ext.mk₀ (Rep.resMap (SSGRoute.PTExt.galRes k L L')
          (Work.SSGRoute.ExtH1.augIncl (L ≃ₐ[k] L))))
        (add_zero 1) = 0 :=
    ShortComplex.ShortExact.extClass_comp _
  rw [← hf]
  rw [phiMap_apply_aux]
  simp only [SSGRoute.PTExt.extHMap, SSGRoute.PTExt.extRes,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.mapExactFunctor_extClass]
  simp only [Abelian.Ext.comp_assoc_of_second_deg_zero,
    Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [hnat]
  simp only [Abelian.Ext.mk₀_comp_mk₀_assoc]
  rw [← hkk]
  rw [← Abelian.Ext.mk₀_comp_mk₀]
  simp only [Abelian.Ext.comp_assoc_of_second_deg_zero]
  rw [← Abelian.Ext.comp_assoc_of_second_deg_zero, hkill]
  simp only [Abelian.Ext.zero_comp, Abelian.Ext.comp_zero]

/-- **Kummer theory: the relative Kummer class dies at a higher level.** -/
theorem kummer_dies_at_higher_level (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower k K Ω] (ζ : k) (hζ : IsPrimitiveRoot ζ p)
    (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (z : Rep.trivial SSGRoute.PTExt.Coeff (L ≃ₐ[k] L) (ZMod p) ⟶
      SSGRoute.PTExt.unitsK k L)
    (hz : ((Additive.toMul (z.hom (1 : ZMod p)) : Lˣ) : L) = algebraMap k L ζ)
    (h : SSGRoute.PTExt.extH (Rep.trivial SSGRoute.PTExt.Coeff (L ≃ₐ[k] L) (ZMod p)) 2)
    (hk : h.comp (CategoryTheory.Abelian.Ext.mk₀ z) (add_zero 2) = 0) :
    ∃ (L' : IntermediateField K Ω) (_ : NumberField L') (_ : FiniteDimensional k L')
      (_ : IsGalois k L') (hLL : L ≤ L'),
      SSGRoute.PTExt.inflTrivIn (k := k) hLL (ZMod p) h = 0 := by
  classical
  let S : ShortComplex (Rep.{0,0,0} Coeff (L ≃ₐ[k] L)) := kummerSESX k L p hζ z hz
  have hS : S.ShortExact := kummerSESX_shortExact k L p hζ z hz
  -- step 1: `h` is the connecting image of a class `c ∈ H¹(Gal(L/k), (Lˣ)^p)`
  obtain ⟨c, hc⟩ := Abelian.Ext.covariant_sequence_exact₁ (X := unitRep (L ≃ₐ[k] L))
    (S := S) hS h hk (n₀ := 1) (by norm_num)
  -- step 2: `c` is the image of an explicit derivation on the augmentation ideal
  obtain ⟨f, hf⟩ := ExtH1.phiMap_surjective (L ≃ₐ[k] L) ↥(pthSubX L p)
    (augSES_shortExact (L ≃ₐ[k] L)) c
  -- step 3 (Hilbert 90 + Kummer): the derivation is the coboundary of a Kummer generator
  obtain ⟨x, hφ'⟩ := exists_kummer_generator_of_derivCochain k L p f
  -- step 4: enlarge the level so that `x` becomes a `p`-th power
  obtain ⟨L', hN', hFD', hGal', hLL, y, hy⟩ := exists_level_pthRoot p k K Ω L x
  haveI : NumberField L' := hN'
  haveI : FiniteDimensional k L' := hFD'
  haveI : IsGalois k L' := hGal'
  letI : Algebra L L' := (IntermediateField.inclusion hLL).toAlgebra
  haveI : IsScalarTower k L L' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- step 5: a Kummer coefficient class at the level `L'`
  obtain ⟨u', hu', z', hz'val⟩ := exists_zetaCoeff p k L' ζ hζ
  have hz' : ((Additive.toMul (z'.hom (1 : ZMod p)) : L'ˣ) : L') = algebraMap k L' ζ := by
    rw [show (1 : ZMod p) = ((1 : ℤ) : ZMod p) from by norm_num, hz'val 1]
    rw [zpow_one]
    exact hu'
  -- step 6: the coefficient inclusions `τ₂`, `τ₃` for the level extension
  obtain ⟨τ₂, τ₃, hτ₂, hτ₃, hτ₃sq⟩ := exists_pthResIncl k L L' p
  -- step 7: the class dies after inflation
  have hzero := kummerMainStep k L L' p ζ hζ z hz z' hz' τ₂ τ₃ hτ₂ hτ₃ hτ₃sq
    c f hf x hφ' ⟨y, hy⟩
  -- step 8: conclude
  refine ⟨L', hN', hFD', hGal', hLL, ?_⟩
  have hLHS : SSGRoute.PTExt.inflTrivIn (k := k) hLL (ZMod p) h
      = SSGRoute.PTExt.extHMap (SSGRoute.PTExt.galRes k L L')
          (SSGRoute.PTExt.trivResInv (SSGRoute.PTExt.galRes k L L') (ZMod p))
          (c.comp hS.extClass (by norm_num)) := by
    show SSGRoute.PTExt.extHMap (SSGRoute.PTExt.galRes k L L')
          (SSGRoute.PTExt.trivResInv (SSGRoute.PTExt.galRes k L L') (ZMod p)) h = _
    rw [← hc]
  rw [hLHS]
  exact hzero

end Phi0Kummer
end Work.SSGRoute

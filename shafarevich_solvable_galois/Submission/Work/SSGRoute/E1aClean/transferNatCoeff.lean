import Mathlib
import Submission.Work.SSGRoute.E1aClean.finPlaceDict
import Submission.Work.AbsoluteKummer.SES.range_mapH1_eq_ker_mapH1
import Submission.Work.SSGRoute.ExtChain.e1c_natural
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the `H¹`-transfer and of `levelChangeTransferD` in the coefficients

`Work.SSGRoute.PT.h1Transfer Φ hΦ Ψ hΨ : H¹(G',M') ≃+ H¹(G,M)` transfers continuous cohomology
along a homeomorphic group isomorphism `Φ : G' ≃* G` and a compatible coefficient isomorphism
`Ψ : M' ≃+ M`.  The library had its naturality only at `Ψ = AddEquiv.refl`
(`E1aClean/h1TransferReflNat.lean`); the finite-place dictionary of
`E1aClean.finPlaceDict_holds` needs it at the *level-change* coefficient identification
`levelTwoCoeffEquiv`, i.e. in the general form proved here.

* `Work.SSGRoute.PT.h1TransferAddHom_mapH1` — the general naturality square: for a second
  coefficient system `(Ψ₂ : N' ≃+ N)`, maps `f' : N' →+ M'`, `f : N →+ M` equivariant for `G'`
  resp. `G` and satisfying `Ψ ∘ f' = f ∘ Ψ₂` pointwise, the transfer commutes with the coefficient
  change.
* `Work.SSGRoute.E1aClean.levelChangeTransferD_natural` — the instance of it needed for the
  five-factor naturality chase of `FinPlaceDict`: `levelChangeTransferD` commutes with `mapH1` of
  an equivariant coefficient map.
-/

open scoped Classical
open Work.AbsoluteKummer

namespace Work.SSGRoute.PT

noncomputable section

variable {G G' : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']

/-- **Naturality of the `H¹`-transfer in the coefficients.**

For `Φ : G' ≃* G` and two compatible coefficient isomorphisms `Ψ : M' ≃+ M`, `Ψ₂ : N' ≃+ N`
(`G'`-modules on the primed side, `G`-modules on the unprimed side), the transfer commutes with an
equivariant coefficient change `f' : N' →+ M'` on the level of `Z¹`: the only extra input is the
commuting square `Ψ ∘ f' = f ∘ Ψ₂` on the nose. -/
theorem h1TransferAddHom_mapH1 (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    {M M' N N' : Type*} [AddCommGroup M] [DistribMulAction G M]
    [AddCommGroup M'] [DistribMulAction G' M']
    [AddCommGroup N] [DistribMulAction G N] [AddCommGroup N'] [DistribMulAction G' N']
    (Ψ : M' ≃+ M) (hΨ : ∀ (g' : G') (m' : M'), Ψ (g' • m') = Φ g' • Ψ m')
    (Ψ₂ : N' ≃+ N) (hΨ₂ : ∀ (g' : G') (n' : N'), Ψ₂ (g' • n') = Φ g' • Ψ₂ n')
    (f' : N' →+ M') (hf' : Work.GroupCohomology.IsEquivariant G' f')
    (f : N →+ M) (hf : Work.GroupCohomology.IsEquivariant G f)
    (hsq : ∀ n' : N', Ψ (f' n') = f (Ψ₂ n'))
    (y : H1 G' N') :
    h1TransferAddHom Φ hΦc Ψ hΨ (mapH1 f' hf' y)
      = mapH1 f hf (h1TransferAddHom Φ hΦc Ψ₂ hΨ₂ y) := by
  refine Work.AbsoluteKummer.SES.H1_induction_on
    (C := fun y => h1TransferAddHom Φ hΦc Ψ hΨ (mapH1 f' hf' y)
      = mapH1 f hf (h1TransferAddHom Φ hΦc Ψ₂ hΨ₂ y)) y ?_
  intro c
  rw [Work.AbsoluteKummer.mapH1_H1π, h1TransferAddHom_mk, h1TransferAddHom_mk,
    Work.AbsoluteKummer.mapH1_H1π]
  congr 1
  apply Subtype.ext
  funext g
  simp only [Work.AbsoluteKummer.mapZ1_apply, z1Transfer_coe, cochainTransfer_apply]
  exact hsq _

end

end Work.SSGRoute.PT

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-- **Naturality of `levelChangeTransferD` in the coefficient.**

The level-change transfer of `E1aClean/finPlaceDict.lean` commutes with the coefficient change
induced by an equivariant morphism `g : R ⟶ R₂` of `Coeff`-representations (on both sides of the
level change: through `g` at the decomposition subgroup `D_A` and through `Rep.res φ g` at the
henselian level `Gal(Ω/k^h)`).

This is the `levelChangeTransferD_natural` brick required by the first (naturality) obligation of
`E1aClean.finPlaceDict_holds`; it is the general transfer-naturality square
`Work.SSGRoute.PT.h1TransferAddHom_mapH1` at the level-change datum, where the commuting square
`levelTwoCoeffEquiv A R φ ∘ precomp (Rep.res φ g) = precomp g ∘ levelTwoCoeffEquiv A R₂ φ` is
`rfl` (`levelTwoCoeffEquiv` is the identity on the common underlying additive group and
`Rep.resMap` does not change the underlying map). -/
theorem levelChangeTransferD_natural
    (p : ℕ) (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω)
    (R R₂ : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V] [Module.Finite ℤ R₂.V]
    (φ : (↥(henselOverDecomp k Ω K A) ≃ₐ[↥(decompField k Ω A)] ↥(henselOverDecomp k Ω K A)) →* (K ≃ₐ[k] K))
    [CharZero ↥(decompField k Ω A)] [IsAlgClosure ↥(decompField k Ω A) Ω]
    [FiniteDimensional ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    [IsGalois ↥(decompField k Ω A) ↥(henselOverDecomp k Ω K A)]
    (hφres : ∀ g : Ω ≃ₐ[↥(decompField k Ω A)] Ω,
      φ (SSGRoute.res ↥(decompField k Ω A) (henselOverDecomp k Ω K A) g)
        = SSGRoute.res k K (AlgEquiv.restrictScalars k g))
    (g : R ⟶ R₂)
    (hg : Work.GroupCohomology.IsEquivariant ↥((decompField k Ω A).fixingSubgroup)
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom))
    (hg' : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[↥(decompField k Ω A)] Ω)
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom (Rep.resMap φ g)).toAddMonoidHom))
    (y : Work.AbsoluteKummer.H1 ↥((decompField k Ω A).fixingSubgroup)
      (Work.SSGRoute.homCoind k Ω K R₂)) :
    levelChangeTransferD p k Ω K A R φ hφres
        (Work.AbsoluteKummer.mapH1 (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom) hg y) =
      Work.AbsoluteKummer.mapH1
        (Work.SSGRoute.precompAddHom (Rep.Hom.hom (Rep.resMap φ g)).toAddMonoidHom) hg'
        (levelChangeTransferD p k Ω K A R₂ φ hφres y) := by
  simp only [levelChangeTransferD]
  exact Work.SSGRoute.PT.h1TransferAddHom_mapH1
    (G := Ω ≃ₐ[↥(decompField k Ω A)] Ω) (G' := ↥((decompField k Ω A).fixingSubgroup))
    (Φ := IntermediateField.fixingSubgroupEquiv (decompField k Ω A)) (hΦc := _)
    (Ψ := levelTwoCoeffEquiv A R φ) (hΨ := _)
    (Ψ₂ := levelTwoCoeffEquiv A R₂ φ) (hΨ₂ := _)
    (f' := Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom) (hf' := hg)
    (f := Work.SSGRoute.precompAddHom (Rep.Hom.hom (Rep.resMap φ g)).toAddMonoidHom) (hf := hg')
    (hsq := fun n' => rfl) (y := y)

end

end Work.SSGRoute.E1aClean

/-! ## The two `Ext`-level naturality bricks of the `Φcan` chain -/

namespace Work.SSGRoute.E1aClean

open CategoryTheory

/-- **`mapExtAddHom` commutes with `mk₀`-composition.**

`Functor.mapExtAddHom` of a composite with a degree-`0` class `mk₀ g` is the composite of the
images; this is the `Ext`-bookkeeping used by the push step of `Φcan`. -/
theorem ext_mapExtAddHom_mk₀_comp {C D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] [CategoryTheory.HasExt C] [CategoryTheory.Category D]
    [CategoryTheory.Abelian D] [CategoryTheory.HasExt D] (F : C ⥤ D) [F.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F]
    {X₁ X₂ Y : C} (g : X₂ ⟶ X₁) (w : CategoryTheory.Abelian.Ext X₁ Y 1) :
    F.mapExtAddHom X₂ Y 1 ((CategoryTheory.Abelian.Ext.mk₀ g).comp w (zero_add 1))
      = (CategoryTheory.Abelian.Ext.mk₀ (F.map g)).comp
          (F.mapExtAddHom X₁ Y 1 w) (zero_add 1) := by
  rw [Functor.mapExtAddHom_apply, CategoryTheory.Abelian.Ext.mapExactFunctor_comp,
    CategoryTheory.Abelian.Ext.mapExactFunctor_mk₀, Functor.mapExtAddHom_apply]

/-- **Naturality of `extResEquivExplicit` in the coefficient**: the explicit form of
`ext_res_mulEquiv` commutes with premultiplication by `mk₀` of a coefficient morphism. -/
theorem extResEquivExplicit_natural {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (X₁ X₂ Y : Rep.{0} SSGRoute.PTExt.Coeff G) (g : X₂ ⟶ X₁)
    (z : CategoryTheory.Abelian.Ext (Rep.res e.symm.toMonoidHom X₁)
      (Rep.res e.symm.toMonoidHom Y) 1) :
    extResEquivExplicit e X₂ Y
        ((CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap e.symm.toMonoidHom g)).comp z (zero_add 1))
      = (CategoryTheory.Abelian.Ext.mk₀ g).comp
          (extResEquivExplicit e X₁ Y z) (zero_add 1) := by
  refine (extResEquivExplicit e X₂ Y).symm.injective ?_
  rw [AddEquiv.symm_apply_apply, extResEquivExplicit_symm_apply, ext_mapExtAddHom_mk₀_comp]
  have h1 : (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) e.symm.toMonoidHom).mapExtAddHom X₁ Y 1
      ((extResEquivExplicit e X₁ Y) z) = z := by
    rw [← extResEquivExplicit_symm_apply e X₁ Y ((extResEquivExplicit e X₁ Y) z),
      AddEquiv.symm_apply_apply]
  rw [h1]

end Work.SSGRoute.E1aClean

namespace Work.SSGRoute.ExtChain.E1cGeneric

/-- **Naturality of `e1cEquiv.symm`** in the coefficient: the inverse of the `E1c` dictionary
commutes with the coefficient change.  This is `e1cMap_natural` read through the bijectivity of
`e1cMap`. -/
theorem e1cEquiv_symm_mapH1 {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] (R R₂ : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Module.Finite ℤ R.V]
    [Module.Finite ℤ R₂.V] (g : R ⟶ R₂)
    (hg : Work.GroupCohomology.IsEquivariant (Ω ≃ₐ[k] Ω)
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom))
    (y : Work.AbsoluteKummer.H1 (Ω ≃ₐ[k] Ω) (Work.SSGRoute.homCoind k Ω K R₂)) :
    (e1cEquiv (k := k) (Ω := Ω) (K := K) R).symm
        (Work.AbsoluteKummer.mapH1
          (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom) hg y)
      = (CategoryTheory.Abelian.Ext.mk₀ g).comp
          ((e1cEquiv (k := k) (Ω := Ω) (K := K) R₂).symm y) (zero_add 1) := by
  refine (e1cEquiv (k := k) (Ω := Ω) (K := K) R).injective ?_
  rw [AddEquiv.apply_symm_apply]
  change Work.AbsoluteKummer.mapH1
      (Work.SSGRoute.precompAddHom (Rep.Hom.hom g).toAddMonoidHom) hg y
    = e1cMap (k := k) (Ω := Ω) (K := K) R
        ((CategoryTheory.Abelian.Ext.mk₀ g).comp
          ((e1cEquiv (k := k) (Ω := Ω) (K := K) R₂).symm y) (zero_add 1))
  rw [e1cMap_natural (k := k) (Ω := Ω) (K := K) R R₂ g hg
      ((e1cEquiv (k := k) (Ω := Ω) (K := K) R₂).symm y)]
  have h2 : e1cMap (k := k) (Ω := Ω) (K := K) R₂
      ((e1cEquiv (k := k) (Ω := Ω) (K := K) R₂).symm y) = y := by
    show (e1cEquiv (k := k) (Ω := Ω) (K := K) R₂)
      ((e1cEquiv (k := k) (Ω := Ω) (K := K) R₂).symm y) = y
    exact AddEquiv.apply_symm_apply _ y
  rw [h2]

end Work.SSGRoute.ExtChain.E1cGeneric

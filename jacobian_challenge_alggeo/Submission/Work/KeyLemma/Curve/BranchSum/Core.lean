/-
# The closed point of a branch

For the branch `branch C h σ : Spec R' ⟶ C` of the pencil at a `K`-embedding
`σ : K(C) →ₐ[K] N`, this file proves that if the local ring `O_{C,Q} = Q.valuationSubring` of a
place `Q` at which `h` is regular maps into `R'` by `σ` *and* the induced map is local, then the
closed point of the branch is `Q`.

The construction is the following.  From a local ring homomorphism `χ : Q.valuationSubring →+* R'`
compatible with `σ` (i.e. `algebraMap R' N ∘ χ = σ`), transport along the canonical isomorphism
`O_{C,Q} ≅ C.stalk Q.point` and form

  `γ' := Spec (ofHom χ') ≫ C.fromSpecStalk Q.point : Spec R' ⟶ C`.

The generic point of `γ'` is the conjugate point `conjPt C h σ` (the compatibility of `χ` with the
function fields), so `γ'` is an extension of `conjPt C h σ` to `Spec R'`; since `C` is separated,
`γ' = branch C h σ` (`branch_unique`), and the closed point of `γ'` is `Q` because `χ'` is local.
-/
import Mathlib
import Submission.Work.KeyLemma.Curve.BranchSum.Defs
import Submission.Work.KeyLemma.Curve.BranchSum.Valuative
import Submission.Work.CurveBasics.Place.Valuation
import Submission.Work.KeyLemma.Sum

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option synthInstance.maxHeartbeats 800000
open CategoryTheory AlgebraicGeometry Limits
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

universe u

namespace Work.KeyLemma.Curve

open Work.SpecLin

noncomputable section

variable {k : Type u} [Field k]

/-- The canonical morphism `Spec K(C) ⟶ C` at the generic point followed by the structure
morphism is `Spec` of the `k`-algebra structure on the function field. -/
theorem specMap_algebraMap_fromSpecStalk (C : Work.CurveBasics.Curve k) (x : C.left) :
    Spec.map (CommRingCat.ofHom (algebraMap (C.left.presheaf.stalk x) C.functionField))
      ≫ C.left.fromSpecStalk x = C.left.fromSpecStalk (genericPoint C.left) := by
  rw [RingHom.algebraMap_toAlgebra]
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec C.left).specializes trivial)

variable (C : Work.CurveBasics.Curve k) (h : C.functionField)
  {N : Type u} [Field N] [Algebra ↥(baseField C h) N] [Algebra k N]
  [IsScalarTower k ↥(baseField C h) N]

/-- **The structure morphism is determined by the generic fibre.**  A morphism
`u : Spec R' ⟶ C` whose restriction to `Spec N` is the conjugate point `conjPt C h σ` is a
morphism over `Spec k`. -/
theorem over_of_generic {R' : Type u} [CommRing R'] [Algebra k R'] [Algebra R' N]
    [IsScalarTower k R' N] [IsFractionRing R' N]
    (σ : ↥C.functionField →ₐ[↥(baseField C h)] N)
    {u : Spec (CommRingCat.of R') ⟶ C.left}
    (hu : Spec.map (CommRingCat.ofHom (algebraMap R' N)) ≫ u = conjPt C h N σ) :
    u ≫ C.hom = Spec.map (CommRingCat.ofHom (algebraMap k R')) := by
  have hconj : conjPt C h N σ ≫ C.hom
      = Spec.map (CommRingCat.ofHom (algebraMap k N)) := (conjPtOverC C h σ).w
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (u ≫ C.hom)
  have keyL : Spec.map (CommRingCat.ofHom ((algebraMap R' N).comp ψ.hom))
      = Spec.map (CommRingCat.ofHom (algebraMap R' N)) ≫ Spec.map ψ := by
    rw [← Spec.map_comp]
    congr 1
  have key : Spec.map (CommRingCat.ofHom ((algebraMap R' N).comp ψ.hom))
      = Spec.map (CommRingCat.ofHom (algebraMap k N)) := by
    rw [keyL, hψ, ← Category.assoc, hu, hconj]
  have h3 : (algebraMap R' N).comp ψ.hom = algebraMap k N := by
    have hspec := Spec.map_injective key
    simpa using congrArg CommRingCat.Hom.hom hspec
  have h4 : ψ.hom = algebraMap k R' := by
    ext x
    apply IsFractionRing.injective R' N
    have hx := RingHom.congr_fun h3 x
    simp only [RingHom.comp_apply] at hx
    rw [hx, IsScalarTower.algebraMap_apply k R' N]
  have hψ' : ψ = CommRingCat.ofHom (algebraMap k R') := by
    apply CommRingCat.hom_ext
    exact h4
  rw [hψ'] at hψ
  exact hψ.symm

end

end Work.KeyLemma.Curve

namespace Work.KeyLemma.Curve

open Work.SpecLin

noncomputable section

variable {k : Type u} [Field k]

open Work.CurveBasics in
/-- The canonical isomorphism between the local ring of `C` at a place and the valuation subring
of the function field consisting of the functions regular at that place. -/
def stalkEquivVal (C : Work.CurveBasics.Curve k) (Q : C.Place) :
    C.left.presheaf.stalk Q.point ≃+* Q.valuationSubring :=
  haveI := Q.instIsDiscreteValuationRing
  IsDiscreteValuationRing.equivValuationSubring (A := C.left.presheaf.stalk Q.point)
    (K := C.functionField)

open Work.CurveBasics in
theorem stalkEquivVal_coe (C : Work.CurveBasics.Curve k) (Q : C.Place)
    (a : C.left.presheaf.stalk Q.point) :
    ((stalkEquivVal C Q a : Q.valuationSubring) : C.functionField)
      = algebraMap (C.left.presheaf.stalk Q.point) C.functionField a := by
  haveI := Q.instIsDiscreteValuationRing
  rw [show stalkEquivVal C Q = IsDiscreteValuationRing.equivValuationSubring
      (A := C.left.presheaf.stalk Q.point) (K := C.functionField) from rfl]
  unfold Work.CurveBasics.Curve.Place.valuationSubring
  simp only [IsDiscreteValuationRing.equivValuationSubring]
  rw [RingEquiv.trans_apply, RingEquiv.trans_apply]
  rw [RingEquiv.coe_subringCongr_apply, Subring.coe_equivMapOfInjective_apply,
    Subring.topEquiv_symm_apply_coe]

open Work.CurveBasics in
theorem stalkEquivVal_local (C : Work.CurveBasics.Curve k) (Q : C.Place) :
    IsLocalHom (stalkEquivVal C Q).toRingHom :=
  IsLocalHom.of_surjective _ (stalkEquivVal C Q).surjective

variable (C : Work.CurveBasics.Curve k) (h : C.functionField)
  {N : Type u} [Field N] [Algebra ↥(baseField C h) N] [Algebra k N]
  [IsScalarTower k ↥(baseField C h) N]

/-- **The closed point of a branch.**  If the valuation subring `O_{C,Q}` of a place `Q` maps into
`R'` by a *local* ring homomorphism `χ` compatible with `σ` (i.e. `algebraMap R' N ∘ χ = σ` on
`O_{C,Q}`), then the branch of `σ` specialises to `Q`. -/
theorem branch_closed_point_of_center {R' : Type u} [CommRing R'] [IsDomain R']
    [ValuationRing R'] [Algebra k R'] [Algebra R' N] [IsScalarTower k R' N]
    [IsFractionRing R' N]
    (σ : ↥C.functionField →ₐ[↥(baseField C h)] N)
    {Q : C.Place} (χ : Q.valuationSubring →+* R') (hχloc : IsLocalHom χ)
    (hχ : ∀ y : Q.valuationSubring, algebraMap R' N (χ y) = σ (y : C.functionField)) :
    (branch C h σ).left (IsLocalRing.closedPoint R') = Q.point := by
  classical
  set ψ : C.left.presheaf.stalk Q.point →+* R' := χ.comp (stalkEquivVal C Q).toRingHom with hψ
  haveI hεloc : IsLocalHom (stalkEquivVal C Q).toRingHom := stalkEquivVal_local C Q
  have hψloc : IsLocalHom ψ := by
    refine ⟨fun a ha => ?_⟩
    rw [hψ] at ha
    simp only [RingHom.comp_apply] at ha
    exact IsUnit.of_map (stalkEquivVal C Q) a (IsLocalHom.map_nonunit (f := χ) _ ha)
  have hcompat : (algebraMap R' N).comp ψ
      = σ.toRingHom.comp (algebraMap (C.left.presheaf.stalk Q.point) C.functionField) := by
    ext a
    show algebraMap R' N (ψ a)
      = σ (algebraMap (C.left.presheaf.stalk Q.point) C.functionField a)
    rw [hψ]
    simp only [RingHom.comp_apply]
    rw [hχ]
    exact congrArg σ (stalkEquivVal_coe C Q a).symm
  let gg : Spec (CommRingCat.of R') ⟶ C.left :=
    Spec.map (CommRingCat.ofHom ψ) ≫ C.left.fromSpecStalk Q.point
  have hgen : Spec.map (CommRingCat.ofHom (algebraMap R' N)) ≫ gg = conjPt C h N σ := by
    show Spec.map (CommRingCat.ofHom (algebraMap R' N))
        ≫ (Spec.map (CommRingCat.ofHom ψ) ≫ C.left.fromSpecStalk Q.point)
      = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ C.left.fromSpecStalk (genericPoint C.left)
    rw [← Category.assoc, ← Spec.map_comp]
    rw [show CommRingCat.ofHom ψ ≫ CommRingCat.ofHom (algebraMap R' N)
        = CommRingCat.ofHom ((algebraMap R' N).comp ψ) from by
      rw [← CommRingCat.ofHom_comp]]
    rw [hcompat]
    rw [show CommRingCat.ofHom (σ.toRingHom.comp
          (algebraMap (C.left.presheaf.stalk Q.point) C.functionField))
        = CommRingCat.ofHom (algebraMap (C.left.presheaf.stalk Q.point) C.functionField)
          ≫ CommRingCat.ofHom σ.toRingHom from by
      rw [← CommRingCat.ofHom_comp]]
    rw [Spec.map_comp, Category.assoc, specMap_algebraMap_fromSpecStalk]
  have hover : gg ≫ C.hom = Spec.map (CommRingCat.ofHom (algebraMap k R')) :=
    over_of_generic C h σ hgen
  let ggO : specOf (K := k) R' ⟶ C.toOver := Over.homMk gg hover
  have hggO : specOfMap (K := k) (IsScalarTower.toAlgHom k R' N) ≫ ggO = conjPtOverC C h σ := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, Over.homMk_left, Work.SpecLin.specOfMap,
      Work.SpecLin.specOfMapHom, IsScalarTower.toAlgHom]
    exact hgen
  have hbranch : branch C h σ = ggO :=
    branch_unique C (g := branch C h σ) (g' := ggO) (by rw [branch_spec, hggO])
  rw [hbranch]
  have hpair : (SpecToEquivOfLocalRing C.left (CommRingCat.of R')) gg
      = ⟨Q.point, ⟨CommRingCat.ofHom ψ, hψloc⟩⟩ := by
    have h0 : gg = (SpecToEquivOfLocalRing C.left (CommRingCat.of R')).symm
        ⟨Q.point, ⟨CommRingCat.ofHom ψ, hψloc⟩⟩ := rfl
    rw [h0, Equiv.apply_symm_apply]
  exact congrArg Sigma.fst hpair



section Count

variable (C : Work.CurveBasics.Curve k) (h : C.functionField)
  {N : Type u} [Field N] [Algebra ↥(baseField C h) N] [Algebra k N]
  [IsScalarTower k ↥(baseField C h) N]

/-- **The number of `K`-embeddings of `K(C)` into `N` is `[K(C) : K]`.**  (`N` is a Galois
extension of `K = k(h)` into which `K(C)` embeds over `K` -- the compatibility `hKE`.) -/
theorem card_algHom_functionField [IsGalois ↥(baseField C h) N]
    [Algebra ↥C.functionField N]
    [FiniteDimensional ↥(baseField C h) ↥C.functionField]
    [Algebra.IsSeparable ↥(baseField C h) ↥C.functionField]
    [FiniteDimensional ↥(baseField C h) N]
    (hKE : (algebraMap ↥(baseField C h) N)
      = (algebraMap ↥C.functionField N).comp
        (algebraMap ↥(baseField C h) ↥C.functionField)) :
    Nat.card (↥C.functionField →ₐ[↥(baseField C h)] N)
      = Module.finrank ↥(baseField C h) ↥C.functionField := by
  refine AlgHom.natCard_of_splits ↥(baseField C h) ↥C.functionField N ?_
  intro x
  have hroot : (Polynomial.aeval (algebraMap ↥C.functionField N x))
      (minpoly ↥(baseField C h) x) = 0 := by
    rw [Polynomial.aeval_def, hKE, ← Polynomial.hom_eval₂ (minpoly ↥(baseField C h) x)
        (algebraMap ↥(baseField C h) ↥C.functionField) (algebraMap ↥C.functionField N) x]
    rw [show (minpoly ↥(baseField C h) x).eval₂
          (algebraMap ↥(baseField C h) ↥C.functionField) x = 0 from by
        rw [← Polynomial.aeval_def]; exact minpoly.aeval _ _]
    rw [map_zero]
  have hdiv : minpoly ↥(baseField C h) (algebraMap ↥C.functionField N x)
      ∣ minpoly ↥(baseField C h) x := minpoly.dvd _ _ hroot
  have hz : IsIntegral ↥(baseField C h) (algebraMap ↥C.functionField N x) :=
    Algebra.IsIntegral.isIntegral _
  have hx : IsIntegral ↥(baseField C h) x := Algebra.IsIntegral.isIntegral _
  have hassoc : Associated (minpoly ↥(baseField C h) (algebraMap ↥C.functionField N x))
      (minpoly ↥(baseField C h) x) :=
    Irreducible.associated_of_dvd (minpoly.irreducible hz) (minpoly.irreducible hx) hdiv
  have heq : minpoly ↥(baseField C h) (algebraMap ↥C.functionField N x)
      = minpoly ↥(baseField C h) x :=
    Polynomial.eq_of_monic_of_associated (minpoly.monic hz) (minpoly.monic hx) hassoc
  rw [← heq]
  exact Normal.splits (inferInstance : Normal ↥(baseField C h) N) _

end Count



section Prod

variable {k : Type u} [Field k]

/-- Post-composition with a fixed morphism preserves products of morphisms into a commutative
group object. -/
theorem comp_prod {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsCommMonObj A]
    {X Y : Over (Spec (CommRingCat.of k))} (u : Y ⟶ X) {J : Type*} (s : Finset J)
    (g : J → (X ⟶ A)) :
    u ≫ (∏ i ∈ s, g i) = ∏ i ∈ s, (u ≫ g i) := by
  have hmul : ∀ f g' : X ⟶ A, u ≫ (f * g') = (u ≫ f) * (u ≫ g') := by
    intro f g'
    rw [Hom.mul_def, Hom.mul_def,
      ← Category.assoc]
    congr 1
    ext <;> simp
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, Hom.one_def,
      Hom.one_def, ← Category.assoc,
      Subsingleton.elim (u ≫ CartesianMonoidalCategory.toUnit X)
        (CartesianMonoidalCategory.toUnit Y)]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.prod_insert hi, hmul, ih]

/-- Post-composition with a fixed morphism preserves finite products (`Finset.univ` form). -/
theorem comp_prod_univ {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsCommMonObj A]
    {X Y : Over (Spec (CommRingCat.of k))} (u : Y ⟶ X) {J : Type*} [Fintype J]
    (g : J → (X ⟶ A)) :
    u ≫ (∏ i, g i) = ∏ i, (u ≫ g i) :=
  comp_prod u Finset.univ g

end Prod



section DivHelpers

variable {k : Type u} [Field k]

/-- The divisor of a one-point multiset is the place of that point. -/
theorem toDiv_single (C : Work.CurveBasics.Curve k) (p : Point C) :
    SumDiv.toDiv C (Finsupp.single p 1) = Finsupp.single (placeOfPoint C p) 1 := by
  ext Q
  rw [SumDiv.toDiv_apply, SumDiv.coeffAt, Finsupp.sum_single_index (by simp), Finsupp.single_apply]
  split <;> simp_all

/-- The sum of a finite multiset of points written as a finset sum. -/
theorem sumOfPoints_finsetSum {C : Work.CurveBasics.Curve k}
    {A : Over (Spec (CommRingCat.of k))} [GrpObj A] [IsCommMonObj A] (f : C.toOver ⟶ A)
    {J : Type*} (s : Finset J) (p : J → Point C) :
    SumDiv.sumOfPoints C f (∑ j ∈ s, Finsupp.single (p j) 1) = ∏ j ∈ s, (p j ≫ f) := by
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.prod_insert hj, SumDiv.sumOfPoints_add,
        SumDiv.sumOfPoints_single, ih, pow_one]

end DivHelpers

end

end Work.KeyLemma.Curve

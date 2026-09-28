import Mathlib
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.sphereVanishing
import Submission.Work.Cohomology.sphereHomologyTop

set_option synthInstance.maxHeartbeats 400000

/-!
# The rational homology of spheres

The integral computation of the singular homology of the sphere
(`Work.Cohomology.sphereHomologyTop`, `Work.Cohomology.sphereVanishing`) is transported to
coefficients in `ℚ` by the change-of-rings functor `ModuleCat.extendScalars (Int.castRingHom ℚ)`
(extension of scalars `- ⊗[ℤ] ℚ`).

The chapter built here consists of

* `Work.StemsB.SphRat.baseChange_add` and the instance
  `Work.StemsB.SphRat.extendScalarsAdditive`: extension of scalars is an additive functor;
* `Work.StemsB.SphRat.sigmaConstObjCompIso`: `sigmaConst.obj R ⋙ F ≅ sigmaConst.obj (F.obj R)`
  for a functor `F` preserving coproducts (the singular chains of a simplicial set with
  coefficients in `F.obj R` are the `F`-image of the integral ones);
* `Work.StemsB.SphRat.chainComplexBaseChange` and `Work.StemsB.SphRat.chainComplexCoeffIso`:
  the resulting isomorphism of chain complexes
  `C_*(X; ℤ) ⊗[ℤ] ℚ ≅ C_*(X; ℚ)`;
* `Work.StemsB.SphRat.homologyMapBaseChange`: for an exact functor `F`,
  `H_k(F(K)) ≅ F(H_k(K))`;
* `Work.StemsB.SphRat.extendScalarsIntRatIso`: `(extendScalars (ℤ → ℚ)).obj ℤ ≅ ℚ`.

The result `Work.StemsB.sphRatHomology` is then immediate from `H_n(S^n; ℤ) ≅ ℤ` and the
vanishing of `H_k(S^n; ℤ)` for `k ≠ 0, n`.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial TensorProduct

namespace Work.StemsB.SphRat

noncomputable section

/-! ## 1. Extension of scalars is additive -/

/-- `LinearMap.baseChange` is additive in its linear-map argument. -/
lemma baseChange_add {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (g h : M →ₗ[R] N) :
    LinearMap.baseChange S (g + h) = LinearMap.baseChange S g + LinearMap.baseChange S h := by
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      rw [LinearMap.baseChange_tmul, LinearMap.add_apply, LinearMap.add_apply, TensorProduct.tmul_add,
          LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
  | add x y hx hy =>
      rw [map_add, LinearMap.add_apply, map_add, map_add, hx, hy, LinearMap.add_apply,
        LinearMap.add_apply]
      abel

/-- **Extension of scalars along a ring homomorphism is an additive functor.** -/
instance extendScalarsAdditive {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars f).Additive where
  map_add {M N} g h := by
    letI : Algebra R S := f.toAlgebra
    apply ModuleCat.hom_ext
    show LinearMap.baseChange S (ModuleCat.Hom.hom (g + h)) =
        LinearMap.baseChange S (ModuleCat.Hom.hom g) + LinearMap.baseChange S (ModuleCat.Hom.hom h)
    rw [ModuleCat.hom_add, baseChange_add]

/-! ## 2. Coproducts and the functor `sigmaConst` -/

/-- **A functor preserving coproducts commutes with `sigmaConst`.**  The coproduct of copies of `R`
indexed by a type, mapped by `F`, is the coproduct of copies of `F.obj R`. -/
noncomputable def sigmaConstObjCompIso {C : Type*} [Category* C] {D : Type*} [Category* D]
    [HasCoproducts.{0} C] [HasCoproducts.{0} D] (F : C ⥤ D)
    [∀ (S : Type), PreservesColimitsOfShape (Discrete S) F] (R : C) :
    Limits.sigmaConst.obj R ⋙ F ≅ Limits.sigmaConst.obj (F.obj R) :=
  NatIso.ofComponents (fun S => PreservesCoproduct.iso F (fun _ : S ↦ R)) (by
    intro S T g
    have key : ∀ (U : Type) (t : U),
        F.map (Sigma.ι (fun _ : U ↦ R) t) ≫ (PreservesCoproduct.iso F (fun _ : U ↦ R)).hom
          = Sigma.ι (fun _ : U ↦ F.obj R) t := by
      intro U t
      have h2 : inv (sigmaComparison F (fun _ : U ↦ R)) =
          (PreservesCoproduct.iso F (fun _ : U ↦ R)).hom := by
        refine IsIso.inv_eq_of_hom_inv_id ?_
        rw [← PreservesCoproduct.inv_hom, Iso.inv_hom_id]
      have h := map_ι_comp_inv_sigmaComparison F (fun _ : U ↦ R) t
      rw [h2] at h
      exact h
    apply (isColimitOfHasCoproductOfPreservesColimit F (fun _ : S ↦ R)).hom_ext
    rintro ⟨s⟩
    simp only [Functor.comp_obj, Functor.comp_map, Cofan.mk_ι_app]
    dsimp only [Limits.sigmaConst]
    rw [← Category.assoc, ← F.map_comp, Sigma.ι_comp_map', Category.id_comp, key T (g s),
      ← Category.assoc, key S s, Sigma.ι_comp_map', Category.id_comp])

/-! ## 3. Base change of the singular chain complex -/

/-- **Base change of the singular chain complex of a simplicial set.** -/
noncomputable def chainComplexBaseChange {C : Type*} [Category* C] [Preadditive C]
    {D : Type*} [Category* D] [Preadditive D]
    [HasCoproducts.{0} C] [HasCoproducts.{0} D] (F : C ⥤ D) [F.Additive]
    [∀ (S : Type), PreservesColimitsOfShape (Discrete S) F] (X : SSet.{0}) (R : C) :
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (X.chainComplex R) ≅
      X.chainComplex (F.obj R) := by
  have h1 : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (X.chainComplex R)
      = (AlgebraicTopology.alternatingFaceMapComplex D).obj
          ((X ⋙ Limits.sigmaConst.obj R) ⋙ F) :=
    congrArg (fun G : SimplicialObject C ⥤ ChainComplex D ℕ =>
        G.obj (X ⋙ Limits.sigmaConst.obj R))
      (AlgebraicTopology.map_alternatingFaceMapComplex F)
  rw [h1]
  exact ((AlgebraicTopology.alternatingFaceMapComplex D).mapIso
    (eqToIso (Functor.assoc X (Limits.sigmaConst.obj R) F) ≪≫
      Functor.isoWhiskerLeft X (sigmaConstObjCompIso F R)))

/-- Changing the coefficient object of the singular chain complex. -/
noncomputable def chainComplexCoeffIso {C : Type*} [Category* C] [Preadditive C]
    [HasCoproducts.{0} C] (X : SSet.{0}) {R R' : C} (e : R ≅ R') :
    X.chainComplex R ≅ X.chainComplex R' :=
  (AlgebraicTopology.alternatingFaceMapComplex C).mapIso
    (Functor.isoWhiskerLeft X (Limits.sigmaConst.mapIso e))

/-! ## 4. Homology of a base change of a chain complex -/

/-- **An additive functor preserving homology commutes with the passage to homology.** -/
lemma homologyMapBaseChange {C : Type*} [Category* C] [Preadditive C] {D : Type*}
    [Category* D] [Preadditive D] (F : C ⥤ D) [F.Additive] [CategoryWithHomology C]
    [CategoryWithHomology D] [F.PreservesHomology] (K : ChainComplex C ℕ) (n : ℕ) :
    Nonempty ((((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology n) ≅
      F.obj (K.homology n)) :=
  ⟨ShortComplex.mapHomologyIso (K.sc n) F ≪≫ Iso.refl _⟩

/-! ## 5. The free module of rank one over `ℚ` -/

/-- The `ℚ`-linear equivalence `ℚ ⊗[ℤ] ℤ ≅ ℚ`, `a ⊗ z ↦ a * z`. -/
noncomputable def ratTensorIntLinearEquiv : (ℚ ⊗[ℤ] ℤ) ≃ₗ[ℚ] ℚ where
  toFun := fun x => TensorProduct.rid ℤ ℚ x
  map_add' := fun x y => map_add (TensorProduct.rid ℤ ℚ) x y
  map_smul' := by
    intro q x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a z =>
        show TensorProduct.rid ℤ ℚ (q • (a ⊗ₜ[ℤ] z)) = q • TensorProduct.rid ℤ ℚ (a ⊗ₜ[ℤ] z)
        rw [TensorProduct.smul_tmul', TensorProduct.rid_tmul, TensorProduct.rid_tmul]
        ring
    | add x y hx hy => simp only [smul_add, map_add, hx, hy, smul_add]
  invFun := fun q => q ⊗ₜ[ℤ] (1 : ℤ)
  left_inv := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a z =>
        show (TensorProduct.rid ℤ ℚ (a ⊗ₜ[ℤ] z)) ⊗ₜ[ℤ] (1 : ℤ) = a ⊗ₜ[ℤ] z
        rw [TensorProduct.rid_tmul]
        rw [← TensorProduct.smul_tmul' (R := ℤ) (R' := ℤ) z a (1 : ℤ)]
        rw [← TensorProduct.tmul_smul z a (1 : ℤ)]
        simp
    | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]
  right_inv := by
    intro q
    show TensorProduct.rid ℤ ℚ (q ⊗ₜ[ℤ] (1 : ℤ)) = q
    rw [TensorProduct.rid_tmul]
    simp

/-- **The free `ℚ`-module of rank one, as the extension of scalars of `ℤ`.** -/
noncomputable def extendScalarsIntRatIso :
    (ModuleCat.extendScalars (Int.castRingHom ℚ)).obj (ModuleCat.of ℤ ℤ) ≅
      ModuleCat.of ℚ ℚ :=
  LinearEquiv.toModuleIso ratTensorIntLinearEquiv

end

end Work.StemsB.SphRat

namespace Work.StemsB

open SphRat

theorem sphRatHomology (n : ℕ) (hn : 1 ≤ n) :
    Nonempty (CategoryTheory.Iso
      ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))).homology n)
      (ModuleCat.of ℚ ℚ)) ∧
    (∀ k : ℕ, k ≠ 0 → k ≠ n → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))).homology k)) := by
  have hf : (Int.castRingHom ℚ).Flat := by
    rw [RingHom.Flat]
    infer_instance
  haveI : PreservesFiniteLimits (ModuleCat.extendScalars (Int.castRingHom ℚ)) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  haveI : PreservesFiniteColimits (ModuleCat.extendScalars (Int.castRingHom ℚ)) := inferInstance
  haveI : (ModuleCat.extendScalars (Int.castRingHom ℚ)).PreservesHomology := inferInstance
  haveI : ∀ (S : Type),
      PreservesColimitsOfShape (Discrete S) (ModuleCat.extendScalars (Int.castRingHom ℚ)) :=
    fun _ => inferInstance
  let X : TopCat := TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
  let K : ChainComplex (ModuleCat ℤ) ℕ := Work.Cohomology.singularChains ℤ X
  let L : ChainComplex (ModuleCat ℚ) ℕ := Work.Cohomology.singularChains ℚ X
  let F : ModuleCat ℤ ⥤ ModuleCat ℚ := ModuleCat.extendScalars (Int.castRingHom ℚ)
  have hΦ : (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K ≅ L :=
    chainComplexBaseChange F (TopCat.toSSet.obj X) (ModuleCat.of ℤ ℤ) ≪≫
      chainComplexCoeffIso (TopCat.toSSet.obj X) extendScalarsIntRatIso
  have hΨ : ∀ k : ℕ, L.homology k ≅ F.obj (K.homology k) := fun k =>
    (HomologicalComplex.homologyMapIso hΦ k).symm ≪≫ (homologyMapBaseChange F K k).some
  constructor
  · obtain ⟨e⟩ := Work.Cohomology.sphereHomologyTop n hn
    exact ⟨hΨ n ≪≫ F.mapIso e ≪≫ extendScalarsIntRatIso⟩
  · intro k hk0 hkn
    exact IsZero.of_iso (Functor.map_isZero F (Work.Cohomology.sphereVanishing n k hn hk0 hkn))
      (hΨ k)

end Work.StemsB

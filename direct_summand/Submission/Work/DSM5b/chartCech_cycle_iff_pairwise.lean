import Mathlib
import Submission.Work.DSMap.Mix2
import Submission.Work.DSM5b.CycleDefs

/-!
# The `0`-cycles of the honest chart Čech complex, in coordinates

For a commutative ring `W` and a finite family `t : ι → W`, the degree-`0` term of the chart Čech
complex `chartCech t = Č({D(t_i)}, W[J/t_i])` of `DSMap.Mix2` is identified, as a `W`-module, with
the product `∏ᵢ W[J/t_i]` of the chart rings of the cover `i ↦ {i}`, and the `0`-cycles are exactly
the families satisfying the pairwise agreement conditions on the overlaps `{i} ∪ {j}`.

The proof splits into

* `ccCech_d_π`: the component formula for Mathlib's Čech differential (in the universes needed for
  `ModuleCat`, where objects and morphisms live in different universes);
* `ccD01`: the `σ`-component of `d 0 1` in the coordinates given by the Čech nerve of `i ↦ {i}`;
* `ccLocRes_ccC0`/`ccD01_pairwise`: the translation of that component formula into the coordinates
  `e0 : (chartCech t).X 0 ≃ₗ[W] ∀ i, W[J/t_i]` of `CycleDefs`.
-/

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open CategoryTheory.Limits Opposite
open scoped Simplicial BigOperators

universe a u v v' w u'

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Work.DSM5b

/-- The coface index map of the Čech nerve is `ccDel`. -/
lemma ccCoface_f {ι : Type a} [DecidableEq ι] (a : Fin 2) (σ : Fin 2 → ι) :
    (((FormalCoproduct.mk ι (chartIdx ι)).cech.map (SimplexCategory.δ a).op).f σ) = ccDel a σ := by
  funext b; rfl

/-- **Component formula for the Čech differential**, in universes where the target category has its
morphisms in a possibly different universe than its objects (the version available in the workspace
requires them to coincide, which fails for `ModuleCat`). -/
theorem ccCech_d_π {C : Type u} [Category.{v} C] [HasFiniteProducts C] {D : Type u'}
    [Category.{v'} D] [HasProducts.{w} D] [Preadditive D] {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ D)
    (n : ℕ) (x : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n+1⦌)).I) :
    ((cechComplexFunctor U).obj P).d n (n+1) ≫
        (Pi.π (fun y => P.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n+1⦌)).obj y))) x)
      = ∑ a : Fin (n+2), (-1 : ℤ) ^ (a : ℕ) •
          ((Pi.π (fun y => P.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj y)))
              (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ a).op).f x)) ≫
            P.map (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ a).op).φ x).op) := by
  simp only [CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor_obj_d]
  rw [CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rw [Preadditive.sum_comp, Finset.sum_congr rfl (fun i _ => Preadditive.zsmul_comp _ _ _)]
  simp only [CosimplicialObject.δ, FormalCoproduct.cosimplicialObjectFunctor_obj_map,
    Pi.lift_comp_π]

/-- The element-level component formula for the chart presheaf. -/
lemma ccPresheaf_map_apply {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι] (t : ι → W)
    {S T : Finset ι} (F : op (op S) ⟶ op (op T)) (y : ↥(chartRing t S)) :
    (((chartPresheaf t).map F).hom y)
      = ⟨locRes t (leOfHom F.unop.unop) y.1,
          chartRing_map_le t (leOfHom F.unop.unop) ⟨y.1, y.2, rfl⟩⟩ := rfl

/-- The components of the Čech differential, in the coordinates given by the Čech nerve of the
cover `i ↦ {i}`. -/
lemma ccD01 (W : Type a) [CommRing W] (ι : Type a) [DecidableEq ι] (t : ι → W)
    (z : (chartCech t).X 0) (σ : Fin 2 → ι) :
    (Pi.π (ccZ W ι 1 t) σ).hom ((chartCech t).d 0 1 z)
      = ccRestr t (ccIdx_del_subset 0 σ) (ccC0 W ι t z (ccDel 0 σ))
        - ccRestr t (ccIdx_del_subset 1 σ) (ccC0 W ι t z (ccDel 1 σ)) := by
  have h := ccCech_d_π (U := chartIdx ι) (P := chartPresheaf t) (n := 0) σ
  have h2 := congrArg (fun φ => φ.hom z) h
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.comp_apply] at h2
  erw [h2, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul]
  congr 1

/-- The `locRes`-image of the `x`-component of `z` is the `locRes`-image of the `x 0`-component
of `e0 z`. -/
lemma ccLocRes_ccC0 (W : Type a) [CommRing W] (ι : Type a) [DecidableEq ι] (t : ι → W)
    (z : ↥((chartCech t).X 0)) {x : Fin 1 → ι} {T : Finset ι}
    (h : ccIdx x ⊆ T) (h' : {x 0} ⊆ T) :
    locRes t h ((ccC0 W ι t z x : ↥(chartRing t (ccIdx x))) : Localization.Away (tS t (ccIdx x)))
      = locRes t h' ((e0 W ι t z (x 0) : ↥(chartRing t {x 0}))
          : Localization.Away (tS t {x 0})) := by
  have hST : ccIdx x = ccIdx (ccConst (x 0)) := congrArg ccIdx (ccUniq x)
  have hc : ccIdx (ccConst (x 0)) = {x 0} := ccIdx_singleton _
  have hT' : ccIdx (ccConst (x 0)) ⊆ T := (le_of_eq hST.symm).trans h
  have hT'' : {x 0} ⊆ T := h'
  have key1 : ccAway t hST ((ccC0 W ι t z x : ↥(chartRing t (ccIdx x)))
        : Localization.Away (tS t (ccIdx x)))
      = ((ccC0 W ι t z (ccConst (x 0)) : ↥(chartRing t (ccIdx (ccConst (x 0)))))
        : Localization.Away (tS t (ccIdx (ccConst (x 0))))) :=
    ccC0_congr_coe W ι t (ccUniq x) z
  have key2 : locRes t hT'
        ((ccC0 W ι t z (ccConst (x 0)) : ↥(chartRing t (ccIdx (ccConst (x 0)))))
          : Localization.Away (tS t (ccIdx (ccConst (x 0)))))
      = locRes t h ((ccC0 W ι t z x : ↥(chartRing t (ccIdx x)))
          : Localization.Away (tS t (ccIdx x))) := by
    rw [← key1]
    exact ccAway_src t hST hT' h _
  have key3 : locRes t h' ((e0 W ι t z (x 0) : ↥(chartRing t {x 0}))
        : Localization.Away (tS t {x 0}))
      = locRes t h' (ccAway t hc ((ccC0 W ι t z (ccConst (x 0))
          : ↥(chartRing t (ccIdx (ccConst (x 0)))))
            : Localization.Away (tS t (ccIdx (ccConst (x 0)))))) := rfl
  have key4 : locRes t hT'' (ccAway t hc ((ccC0 W ι t z (ccConst (x 0))
        : ↥(chartRing t (ccIdx (ccConst (x 0)))))
          : Localization.Away (tS t (ccIdx (ccConst (x 0))))))
      = locRes t hT' ((ccC0 W ι t z (ccConst (x 0))
          : ↥(chartRing t (ccIdx (ccConst (x 0)))))
            : Localization.Away (tS t (ccIdx (ccConst (x 0))))) :=
    ccAway_src t hc hT'' hT' _
  rw [key3, key4]
  exact key2.symm

/-- The components of the Čech differential, in the coordinates `e0`:
the `σ`-component of `d 0 1 z` is the difference of the `σ 1`- and `σ 0`-components of `e0 z`,
restricted to `{σ 0} ∪ {σ 1}`. -/
lemma ccD01_pairwise (W : Type a) [CommRing W] (ι : Type a) [DecidableEq ι] (t : ι → W)
    (z : (chartCech t).X 0) (σ : Fin 2 → ι) :
    ccAway t (ccIdx_pair σ) ((Pi.π (ccZ W ι 1 t) σ).hom ((chartCech t).d 0 1 z))
      = locRes t (Finset.subset_union_right : ({σ 1} : Finset ι) ⊆ {σ 0} ∪ {σ 1})
          ((e0 W ι t z (σ 1) : ↥(chartRing t {σ 1})) : Localization.Away (tS t {σ 1}))
        - locRes t (Finset.subset_union_left : ({σ 0} : Finset ι) ⊆ {σ 0} ∪ {σ 1})
          ((e0 W ι t z (σ 0) : ↥(chartRing t {σ 0})) : Localization.Away (tS t {σ 0})) := by
  rw [ccD01 W ι t z σ, Subalgebra.coe_sub, map_sub]
  congr 1
  · have hA : ccIdx (ccDel 0 σ) ⊆ ({σ 0} : Finset ι) ∪ {σ 1} :=
      (le_of_eq (congrArg ccIdx (ccDel_zero σ))).trans
        ((le_of_eq (ccIdx_singleton (ccConst (σ 1)))).trans Finset.subset_union_right)
    have h1 : ccAway t (ccIdx_pair σ)
        ((ccRestr t (ccIdx_del_subset 0 σ) (ccC0 W ι t z (ccDel 0 σ))
          : ↥(chartRing t (ccIdx σ))) : Localization.Away (tS t (ccIdx σ)))
        = locRes t hA ((ccC0 W ι t z (ccDel 0 σ) : ↥(chartRing t (ccIdx (ccDel 0 σ))))
            : Localization.Away (tS t (ccIdx (ccDel 0 σ)))) := by
      rw [ccRestr_coe]
      exact ccAway_tgt t (ccIdx_pair σ) (ccIdx_del_subset 0 σ) hA _
    rw [h1, ccLocRes_ccC0 W ι t z (x := ccDel 0 σ) hA Finset.subset_union_right]
    rfl
  · have hB : ccIdx (ccDel 1 σ) ⊆ ({σ 0} : Finset ι) ∪ {σ 1} :=
      (le_of_eq (congrArg ccIdx (ccDel_one σ))).trans
        ((le_of_eq (ccIdx_singleton (ccConst (σ 0)))).trans Finset.subset_union_left)
    have h1 : ccAway t (ccIdx_pair σ)
        ((ccRestr t (ccIdx_del_subset 1 σ) (ccC0 W ι t z (ccDel 1 σ))
          : ↥(chartRing t (ccIdx σ))) : Localization.Away (tS t (ccIdx σ)))
        = locRes t hB ((ccC0 W ι t z (ccDel 1 σ) : ↥(chartRing t (ccIdx (ccDel 1 σ))))
            : Localization.Away (tS t (ccIdx (ccDel 1 σ)))) := by
      rw [ccRestr_coe]
      exact ccAway_tgt t (ccIdx_pair σ) (ccIdx_del_subset 1 σ) hB _
    rw [h1, ccLocRes_ccC0 W ι t z (x := ccDel 1 σ) hB Finset.subset_union_left]
    rfl

theorem chartCech_cycle_iff_pairwise {W : Type a} [CommRing W] {ι : Type a} [Fintype ι]
    [DecidableEq ι] (t : ι → W) :
    ∃ e0 : (DSMap.Mix2.chartCech t).X 0 ≃ₗ[W] (∀ i : ι, DSMap.Mix2.chartRing t {i}),
      (∀ (w : W) (i : ι),
        e0 ((DSMap.Mix2.chartCoaugW t).hom w) i = algebraMap W (DSMap.Mix2.chartRing t {i}) w) ∧
      ∀ z : (DSMap.Mix2.chartCech t).X 0,
        ((DSMap.Mix2.chartCech t).d 0 1 z = 0) ↔
          ∀ i j : ι,
            DSMap.Mix2.locRes t (Finset.subset_union_left : ({i} : Finset ι) ⊆ {i} ∪ {j})
                ((e0 z i : DSMap.Mix2.chartRing t {i}) : Localization.Away (DSMap.Mix2.tS t {i})) =
              DSMap.Mix2.locRes t (Finset.subset_union_right : ({j} : Finset ι) ⊆ {i} ∪ {j})
                ((e0 z j : DSMap.Mix2.chartRing t {j}) : Localization.Away (DSMap.Mix2.tS t {j})) := by
  refine ⟨e0 W ι t, fun w i => e0_coaug W ι t w i, ?_⟩
  intro z
  have hcomp : ((chartCech t).d 0 1 z = 0) ↔ ∀ σ : Fin 2 → ι,
      (Pi.π (ccZ W ι 1 t) σ).hom ((chartCech t).d 0 1 z) = 0 := by
    constructor
    · intro h σ
      rw [h]
      exact map_zero _
    · intro h
      refine (ccC1 W ι t).injective ?_
      funext σ
      rw [ccC1_apply, h σ]
      simp
  rw [hcomp]
  constructor
  · intro h i j
    have h1 := h ![i, j]
    have h2 : ccAway t (ccIdx_pair (![i, j] : Fin 2 → ι))
        ((Pi.π (ccZ W ι 1 t) ![i, j]).hom ((chartCech t).d 0 1 z)) = 0 := by
      rw [h1]
      simp
    rw [ccD01_pairwise W ι t z ![i, j], sub_eq_zero] at h2
    rw [show (![i, j] : Fin 2 → ι) 0 = i from rfl,
      show (![i, j] : Fin 2 → ι) 1 = j from rfl] at h2
    exact h2.symm
  · intro h σ
    have h2 : ccAway t (ccIdx_pair σ)
        ((Pi.π (ccZ W ι 1 t) σ).hom ((chartCech t).d 0 1 z)
          : ↥(chartRing t (ccIdx σ))) = 0 := by
      rw [ccD01_pairwise W ι t z σ, sub_eq_zero]
      exact (h (σ 0) (σ 1)).symm
    have h3 : ((Pi.π (ccZ W ι 1 t) σ).hom ((chartCech t).d 0 1 z)
        : ↥(chartRing t (ccIdx σ))) = 0 := by
      apply Subtype.ext
      simpa using (ccAway_eq_zero t (ccIdx_pair σ) _).mp h2
    exact h3

end Work.DSM5b

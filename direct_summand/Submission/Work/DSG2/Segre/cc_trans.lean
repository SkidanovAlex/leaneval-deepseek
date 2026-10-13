import Mathlib
import Submission.Work.DSG2.Segre.cc_charts

/-!
# The chart transition data of the Segre charts

This file contains the auxiliary computations for `Work.DSG2.Segre.charts_compat`:

* the tensor decompositions `ccThetaL_comp`, `ccThetaR_comp` of the two chart maps;
* the factorizations `ccAlphaL_fac`, …, and the range descriptions of the chart maps;
* the "intersection chart" maps `ccUa`, `ccUb` of the two projective spaces;
* the chart transition identities `cc_alpha_mul`, `cc_beta_mul` of `P^a` and `P^b`,
  transported to the fibre product `ccP` of the two product charts.
-/

namespace Work.DSG2.Segre

universe u

open CategoryTheory AlgebraicGeometry Limits MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

section Main

variable (A : Type u) [CommRing A] (a b : ℕ) (k k' : Fin (a+1) × Fin (b+1))

/-! ## The tensor decomposition of the product-chart maps -/

lemma ccThetaL_comp (u : chartRingA A a k.1) (v : chartRingB A b k.2) :
    (cc_rr (ccP A a b k k') (chartRing A a b k) (ccThetaL A a b k k')) (u ⊗ₜ[A] v)
      = (cc_rr (ccP A a b k k') (chartRingA A a k.1) (ccAlphaL A a b k k')) u
        * (cc_rr (ccP A a b k k') (chartRingB A b k.2) (ccBetaL A a b k k')) v := by
  have h1 : (cc_rr (ccP A a b k k') (chartRing A a b k) (ccThetaL A a b k k')).comp
      (algebraMap (chartRingA A a k.1) (chartRing A a b k)) =
      cc_rr (ccP A a b k k') (chartRingA A a k.1) (ccAlphaL A a b k k') := by
    rw [← cc_rr_comp_specMap (h := ccThetaL A a b k k')
      (φ := algebraMap (chartRingA A a k.1) (chartRing A a b k))]
  have h2 : (cc_rr (ccP A a b k k') (chartRing A a b k) (ccThetaL A a b k k')).comp
      (Algebra.TensorProduct.includeRight (R := A) (A := chartRingA A a k.1)
        (B := chartRingB A b k.2)).toRingHom =
      cc_rr (ccP A a b k k') (chartRingB A b k.2) (ccBetaL A a b k k') := by
    rw [← cc_rr_comp_specMap (h := ccThetaL A a b k k')
      (φ := (Algebra.TensorProduct.includeRight (R := A) (A := chartRingA A a k.1)
        (B := chartRingB A b k.2)).toRingHom)]
  have h3 : u ⊗ₜ[A] v = (algebraMap (chartRingA A a k.1) (chartRing A a b k) u) *
      (Algebra.TensorProduct.includeRight (R := A) (A := chartRingA A a k.1)
        (B := chartRingB A b k.2) v) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one]
  rw [h3, map_mul]
  rw [show (cc_rr (ccP A a b k k') (chartRing A a b k) (ccThetaL A a b k k'))
        (algebraMap (chartRingA A a k.1) (chartRing A a b k) u)
      = (cc_rr (ccP A a b k k') (chartRingA A a k.1) (ccAlphaL A a b k k')) u
    from RingHom.congr_fun h1 u]
  rw [show (cc_rr (ccP A a b k k') (chartRing A a b k) (ccThetaL A a b k k'))
        (Algebra.TensorProduct.includeRight (R := A) (A := chartRingA A a k.1)
          (B := chartRingB A b k.2) v)
      = (cc_rr (ccP A a b k k') (chartRingB A b k.2) (ccBetaL A a b k k')) v
    from RingHom.congr_fun h2 v]

lemma ccThetaR_comp (u : chartRingA A a k'.1) (v : chartRingB A b k'.2) :
    (cc_rr (ccP A a b k k') (chartRing A a b k') (ccThetaR A a b k k')) (u ⊗ₜ[A] v)
      = (cc_rr (ccP A a b k k') (chartRingA A a k'.1) (ccAlphaR A a b k k')) u
        * (cc_rr (ccP A a b k k') (chartRingB A b k'.2) (ccBetaR A a b k k')) v := by
  have h1 : (cc_rr (ccP A a b k k') (chartRing A a b k') (ccThetaR A a b k k')).comp
      (algebraMap (chartRingA A a k'.1) (chartRing A a b k')) =
      cc_rr (ccP A a b k k') (chartRingA A a k'.1) (ccAlphaR A a b k k') := by
    rw [← cc_rr_comp_specMap (h := ccThetaR A a b k k')
      (φ := algebraMap (chartRingA A a k'.1) (chartRing A a b k'))]
  have h2 : (cc_rr (ccP A a b k k') (chartRing A a b k') (ccThetaR A a b k k')).comp
      (Algebra.TensorProduct.includeRight (R := A) (A := chartRingA A a k'.1)
        (B := chartRingB A b k'.2)).toRingHom =
      cc_rr (ccP A a b k k') (chartRingB A b k'.2) (ccBetaR A a b k k') := by
    rw [← cc_rr_comp_specMap (h := ccThetaR A a b k k')
      (φ := (Algebra.TensorProduct.includeRight (R := A) (A := chartRingA A a k'.1)
        (B := chartRingB A b k'.2)).toRingHom)]
  have h3 : u ⊗ₜ[A] v = (algebraMap (chartRingA A a k'.1) (chartRing A a b k') u) *
      (Algebra.TensorProduct.includeRight (R := A) (A := chartRingA A a k'.1)
        (B := chartRingB A b k'.2) v) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, mul_one]
  rw [h3, map_mul]
  rw [show (cc_rr (ccP A a b k k') (chartRing A a b k') (ccThetaR A a b k k'))
        (algebraMap (chartRingA A a k'.1) (chartRing A a b k') u)
      = (cc_rr (ccP A a b k k') (chartRingA A a k'.1) (ccAlphaR A a b k k')) u
    from RingHom.congr_fun h1 u]
  rw [show (cc_rr (ccP A a b k k') (chartRing A a b k') (ccThetaR A a b k k'))
        (Algebra.TensorProduct.includeRight (R := A) (A := chartRingA A a k'.1)
          (B := chartRingB A b k'.2) v)
      = (cc_rr (ccP A a b k k') (chartRingB A b k'.2) (ccBetaR A a b k k')) v
    from RingHom.congr_fun h2 v]

/-! ## The factorizations of the chart maps -/

lemma ccAlphaL_fac : ccAlphaL A a b k k' ≫ Work.DSG4c.chartι A a k.1 =
    pullback.fst (V A a b k).ι (V A a b k').ι ≫ (V A a b k).ι ≫
      pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) := by
  simp only [ccAlphaL, ccThetaL, Category.assoc, ← chartIncl_fst, chartIso_inv_chartIncl_assoc]

lemma ccAlphaR_fac : ccAlphaR A a b k k' ≫ Work.DSG4c.chartι A a k'.1 =
    pullback.fst (V A a b k).ι (V A a b k').ι ≫ (V A a b k).ι ≫
      pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) := by
  simp only [ccAlphaR, ccThetaR, Category.assoc, ← chartIncl_fst A a b k',
    chartIso_inv_chartIncl_assoc, pullback.condition_assoc]

lemma ccBetaL_fac : ccBetaL A a b k k' ≫ Work.DSG4c.chartι A b k.2 =
    pullback.fst (V A a b k).ι (V A a b k').ι ≫ (V A a b k).ι ≫
      pullback.snd (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) := by
  simp only [ccBetaL, ccThetaL, Category.assoc, ← cc_chartIncl_snd A a b k,
    chartIso_inv_chartIncl_assoc]

lemma ccBetaR_fac : ccBetaR A a b k k' ≫ Work.DSG4c.chartι A b k'.2 =
    pullback.fst (V A a b k).ι (V A a b k').ι ≫ (V A a b k).ι ≫
      pullback.snd (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) := by
  simp only [ccBetaR, ccThetaR, Category.assoc, ← cc_chartIncl_snd A a b k',
    chartIso_inv_chartIncl_assoc, pullback.condition_assoc]

/-! ## The ranges of the chart maps -/

lemma ccAlphaR_le_rng : Set.range ⇑(ccAlphaR A a b k k' ≫ Work.DSG4c.chartι A a k'.1) ⊆
    ↑(Proj.basicOpen (DSMap.PGr A a) (MvPolynomial.X k'.1)) := by
  refine Set.Subset.trans (Set.range_comp_subset_range (⇑(ccAlphaR A a b k k'))
    (⇑(Work.DSG4c.chartι A a k'.1))) ?_
  rw [cc_range_chartι_gen A a k'.1]

lemma ccAlphaL_le_rng : Set.range ⇑(ccAlphaL A a b k k' ≫ Work.DSG4c.chartι A a k.1) ⊆
    ↑(Proj.basicOpen (DSMap.PGr A a) (MvPolynomial.X k'.1)) := by
  have h := ccAlphaR_le_rng A a b k k'
  rw [ccAlphaR_fac A a b k k', ← ccAlphaL_fac A a b k k'] at h
  exact h

lemma ccAlphaL_le_rng' : Set.range ⇑(ccAlphaL A a b k k' ≫ Work.DSG4c.chartι A a k.1) ⊆
    ↑(Proj.basicOpen (DSMap.PGr A a) (MvPolynomial.X k.1)) := by
  refine Set.Subset.trans (Set.range_comp_subset_range (⇑(ccAlphaL A a b k k'))
    (⇑(Work.DSG4c.chartι A a k.1))) ?_
  rw [cc_range_chartι_gen A a k.1]

lemma ccAlphaR_le_rng' : Set.range ⇑(ccAlphaR A a b k k' ≫ Work.DSG4c.chartι A a k'.1) ⊆
    ↑(Proj.basicOpen (DSMap.PGr A a) (MvPolynomial.X k.1)) := by
  have h := ccAlphaL_le_rng' A a b k k'
  rw [ccAlphaL_fac A a b k k', ← ccAlphaR_fac A a b k k'] at h
  exact h

lemma ccBetaR_le_rng : Set.range ⇑(ccBetaR A a b k k' ≫ Work.DSG4c.chartι A b k'.2) ⊆
    ↑(Proj.basicOpen (DSMap.PGr A b) (MvPolynomial.X k'.2)) := by
  refine Set.Subset.trans (Set.range_comp_subset_range (⇑(ccBetaR A a b k k'))
    (⇑(Work.DSG4c.chartι A b k'.2))) ?_
  rw [cc_range_chartι_gen A b k'.2]

lemma ccBetaL_le_rng : Set.range ⇑(ccBetaL A a b k k' ≫ Work.DSG4c.chartι A b k.2) ⊆
    ↑(Proj.basicOpen (DSMap.PGr A b) (MvPolynomial.X k'.2)) := by
  have h := ccBetaR_le_rng A a b k k'
  rw [ccBetaR_fac A a b k k', ← ccBetaL_fac A a b k k'] at h
  exact h

lemma ccBetaL_le_rng' : Set.range ⇑(ccBetaL A a b k k' ≫ Work.DSG4c.chartι A b k.2) ⊆
    ↑(Proj.basicOpen (DSMap.PGr A b) (MvPolynomial.X k.2)) := by
  refine Set.Subset.trans (Set.range_comp_subset_range (⇑(ccBetaL A a b k k'))
    (⇑(Work.DSG4c.chartι A b k.2))) ?_
  rw [cc_range_chartι_gen A b k.2]

lemma ccBetaR_le_rng' : Set.range ⇑(ccBetaR A a b k k' ≫ Work.DSG4c.chartι A b k'.2) ⊆
    ↑(Proj.basicOpen (DSMap.PGr A b) (MvPolynomial.X k.2)) := by
  have h := ccBetaL_le_rng' A a b k k'
  rw [ccBetaL_fac A a b k k', ← ccBetaR_fac A a b k k'] at h
  exact h

lemma ccAlphaL_range : Set.range ⇑(ccAlphaL A a b k k' ≫ Work.DSG4c.chartι A a k.1) ⊆
    Set.range ⇑(Proj.awayι (DSMap.PGr A a)
      (MvPolynomial.X k.1 * MvPolynomial.X k'.1)
      (SetLike.mul_mem_graded (Work.DSG4c.X_mem A a k.1) (Work.DSG4c.X_mem A a k'.1))
      (by norm_num)) := by
  rw [← Scheme.Hom.coe_opensRange (Proj.awayι (DSMap.PGr A a)
      (MvPolynomial.X k.1 * MvPolynomial.X k'.1)
      (SetLike.mul_mem_graded (Work.DSG4c.X_mem A a k.1) (Work.DSG4c.X_mem A a k'.1))
      (by norm_num)), Proj.opensRange_awayι, Proj.basicOpen_mul]
  change Set.range ⇑(ccAlphaL A a b k k' ≫ Work.DSG4c.chartι A a k.1) ⊆
      ↑(Proj.basicOpen (DSMap.PGr A a) (MvPolynomial.X k.1)) ∩
        ↑(Proj.basicOpen (DSMap.PGr A a) (MvPolynomial.X k'.1))
  rw [Set.subset_inter_iff]
  exact ⟨ccAlphaL_le_rng' A a b k k', ccAlphaL_le_rng A a b k k'⟩

lemma ccAlphaR_range : Set.range ⇑(ccAlphaR A a b k k' ≫ Work.DSG4c.chartι A a k'.1) ⊆
    Set.range ⇑(Proj.awayι (DSMap.PGr A a)
      (MvPolynomial.X k.1 * MvPolynomial.X k'.1)
      (SetLike.mul_mem_graded (Work.DSG4c.X_mem A a k.1) (Work.DSG4c.X_mem A a k'.1))
      (by norm_num)) := by
  rw [← Scheme.Hom.coe_opensRange (Proj.awayι (DSMap.PGr A a)
      (MvPolynomial.X k.1 * MvPolynomial.X k'.1)
      (SetLike.mul_mem_graded (Work.DSG4c.X_mem A a k.1) (Work.DSG4c.X_mem A a k'.1))
      (by norm_num)), Proj.opensRange_awayι, Proj.basicOpen_mul]
  change Set.range ⇑(ccAlphaR A a b k k' ≫ Work.DSG4c.chartι A a k'.1) ⊆
      ↑(Proj.basicOpen (DSMap.PGr A a) (MvPolynomial.X k.1)) ∩
        ↑(Proj.basicOpen (DSMap.PGr A a) (MvPolynomial.X k'.1))
  rw [Set.subset_inter_iff]
  exact ⟨ccAlphaR_le_rng' A a b k k', ccAlphaR_le_rng A a b k k'⟩

lemma ccBetaL_range : Set.range ⇑(ccBetaL A a b k k' ≫ Work.DSG4c.chartι A b k.2) ⊆
    Set.range ⇑(Proj.awayι (DSMap.PGr A b)
      (MvPolynomial.X k.2 * MvPolynomial.X k'.2)
      (SetLike.mul_mem_graded (Work.DSG4c.X_mem A b k.2) (Work.DSG4c.X_mem A b k'.2))
      (by norm_num)) := by
  rw [← Scheme.Hom.coe_opensRange (Proj.awayι (DSMap.PGr A b)
      (MvPolynomial.X k.2 * MvPolynomial.X k'.2)
      (SetLike.mul_mem_graded (Work.DSG4c.X_mem A b k.2) (Work.DSG4c.X_mem A b k'.2))
      (by norm_num)), Proj.opensRange_awayι, Proj.basicOpen_mul]
  change Set.range ⇑(ccBetaL A a b k k' ≫ Work.DSG4c.chartι A b k.2) ⊆
      ↑(Proj.basicOpen (DSMap.PGr A b) (MvPolynomial.X k.2)) ∩
        ↑(Proj.basicOpen (DSMap.PGr A b) (MvPolynomial.X k'.2))
  rw [Set.subset_inter_iff]
  exact ⟨ccBetaL_le_rng' A a b k k', ccBetaL_le_rng A a b k k'⟩

lemma ccBetaR_range : Set.range ⇑(ccBetaR A a b k k' ≫ Work.DSG4c.chartι A b k'.2) ⊆
    Set.range ⇑(Proj.awayι (DSMap.PGr A b)
      (MvPolynomial.X k.2 * MvPolynomial.X k'.2)
      (SetLike.mul_mem_graded (Work.DSG4c.X_mem A b k.2) (Work.DSG4c.X_mem A b k'.2))
      (by norm_num)) := by
  rw [← Scheme.Hom.coe_opensRange (Proj.awayι (DSMap.PGr A b)
      (MvPolynomial.X k.2 * MvPolynomial.X k'.2)
      (SetLike.mul_mem_graded (Work.DSG4c.X_mem A b k.2) (Work.DSG4c.X_mem A b k'.2))
      (by norm_num)), Proj.opensRange_awayι, Proj.basicOpen_mul]
  change Set.range ⇑(ccBetaR A a b k k' ≫ Work.DSG4c.chartι A b k'.2) ⊆
      ↑(Proj.basicOpen (DSMap.PGr A b) (MvPolynomial.X k.2)) ∩
        ↑(Proj.basicOpen (DSMap.PGr A b) (MvPolynomial.X k'.2))
  rw [Set.subset_inter_iff]
  exact ⟨ccBetaR_le_rng' A a b k k', ccBetaR_le_rng A a b k k'⟩

/-! ## The intersection charts of `P^a` and `P^b` seen from the pullback -/

/-- The intersection chart of `P^a` seen from the pullback of the two product charts. -/
noncomputable def ccUa : ccP A a b k k' ⟶ Spec (CommRingCat.of
    (HomogeneousLocalization.Away (DSMap.PGr A a)
      (MvPolynomial.X k.1 * MvPolynomial.X k'.1))) :=
  IsOpenImmersion.lift (Proj.awayι (DSMap.PGr A a)
      (MvPolynomial.X k.1 * MvPolynomial.X k'.1)
      (SetLike.mul_mem_graded (Work.DSG4c.X_mem A a k.1) (Work.DSG4c.X_mem A a k'.1))
      (by norm_num)) (ccAlphaL A a b k k' ≫ Work.DSG4c.chartι A a k.1)
    (ccAlphaL_range A a b k k')

/-- The intersection chart of `P^b` seen from the pullback of the two product charts. -/
noncomputable def ccUb : ccP A a b k k' ⟶ Spec (CommRingCat.of
    (HomogeneousLocalization.Away (DSMap.PGr A b)
      (MvPolynomial.X k.2 * MvPolynomial.X k'.2))) :=
  IsOpenImmersion.lift (Proj.awayι (DSMap.PGr A b)
      (MvPolynomial.X k.2 * MvPolynomial.X k'.2)
      (SetLike.mul_mem_graded (Work.DSG4c.X_mem A b k.2) (Work.DSG4c.X_mem A b k'.2))
      (by norm_num)) (ccBetaL A a b k k' ≫ Work.DSG4c.chartι A b k.2)
    (ccBetaL_range A a b k k')

lemma cc_awayι_mul_left : Spec.map (CommRingCat.ofHom (ccAMa A a b k k')) ≫
    Work.DSG4c.chartι A a k.1 = Proj.awayι (DSMap.PGr A a)
      (MvPolynomial.X k.1 * MvPolynomial.X k'.1)
      (SetLike.mul_mem_graded (Work.DSG4c.X_mem A a k.1) (Work.DSG4c.X_mem A a k'.1))
      (by norm_num) :=
  (Proj.SpecMap_awayMap_awayι (DSMap.PGr A a)
    (Work.DSG4c.X_mem A a k.1) one_pos (Work.DSG4c.X_mem A a k'.1) rfl).trans
    (cc_awayι_congr _ _ _ _)

lemma cc_awayι_mul_right : Spec.map (CommRingCat.ofHom (ccAMa' A a b k k')) ≫
    Work.DSG4c.chartι A a k'.1 = Proj.awayι (DSMap.PGr A a)
      (MvPolynomial.X k.1 * MvPolynomial.X k'.1)
      (SetLike.mul_mem_graded (Work.DSG4c.X_mem A a k.1) (Work.DSG4c.X_mem A a k'.1))
      (by norm_num) :=
  (Proj.SpecMap_awayMap_awayι (DSMap.PGr A a)
    (Work.DSG4c.X_mem A a k'.1) one_pos (Work.DSG4c.X_mem A a k.1)
    (mul_comm (MvPolynomial.X k.1) (MvPolynomial.X k'.1))).trans
    (cc_awayι_congr _ _ _ _)

lemma cc_awayι_mul_b_left : Spec.map (CommRingCat.ofHom (ccAMb A a b k k')) ≫
    Work.DSG4c.chartι A b k.2 = Proj.awayι (DSMap.PGr A b)
      (MvPolynomial.X k.2 * MvPolynomial.X k'.2)
      (SetLike.mul_mem_graded (Work.DSG4c.X_mem A b k.2) (Work.DSG4c.X_mem A b k'.2))
      (by norm_num) :=
  (Proj.SpecMap_awayMap_awayι (DSMap.PGr A b)
    (Work.DSG4c.X_mem A b k.2) one_pos (Work.DSG4c.X_mem A b k'.2) rfl).trans
    (cc_awayι_congr _ _ _ _)

lemma cc_awayι_mul_b_right : Spec.map (CommRingCat.ofHom (ccAMb' A a b k k')) ≫
    Work.DSG4c.chartι A b k'.2 = Proj.awayι (DSMap.PGr A b)
      (MvPolynomial.X k.2 * MvPolynomial.X k'.2)
      (SetLike.mul_mem_graded (Work.DSG4c.X_mem A b k.2) (Work.DSG4c.X_mem A b k'.2))
      (by norm_num) :=
  (Proj.SpecMap_awayMap_awayι (DSMap.PGr A b)
    (Work.DSG4c.X_mem A b k'.2) one_pos (Work.DSG4c.X_mem A b k.2)
    (mul_comm (MvPolynomial.X k.2) (MvPolynomial.X k'.2))).trans
    (cc_awayι_congr _ _ _ _)

lemma ccUa_fac : ccUa A a b k k' ≫ Spec.map (CommRingCat.ofHom (ccAMa A a b k k')) =
    ccAlphaL A a b k k' := by
  haveI := IsOpenImmersion.mono (Work.DSG4c.chartι A a k.1)
  refine (cancel_mono (Work.DSG4c.chartι A a k.1)).mp ?_
  rw [Category.assoc, cc_awayι_mul_left, ccUa, IsOpenImmersion.lift_fac, ccAlphaL_fac]

lemma ccUa_fac' : ccUa A a b k k' ≫ Spec.map (CommRingCat.ofHom (ccAMa' A a b k k')) =
    ccAlphaR A a b k k' := by
  haveI := IsOpenImmersion.mono (Work.DSG4c.chartι A a k'.1)
  refine (cancel_mono (Work.DSG4c.chartι A a k'.1)).mp ?_
  rw [Category.assoc, cc_awayι_mul_right, ccUa, IsOpenImmersion.lift_fac, ccAlphaR_fac,
    ← ccAlphaL_fac]

lemma ccUb_fac : ccUb A a b k k' ≫ Spec.map (CommRingCat.ofHom (ccAMb A a b k k')) =
    ccBetaL A a b k k' := by
  haveI := IsOpenImmersion.mono (Work.DSG4c.chartι A b k.2)
  refine (cancel_mono (Work.DSG4c.chartι A b k.2)).mp ?_
  rw [Category.assoc, cc_awayι_mul_b_left, ccUb, IsOpenImmersion.lift_fac, ccBetaL_fac]

lemma ccUb_fac' : ccUb A a b k k' ≫ Spec.map (CommRingCat.ofHom (ccAMb' A a b k k')) =
    ccBetaR A a b k k' := by
  haveI := IsOpenImmersion.mono (Work.DSG4c.chartι A b k'.2)
  refine (cancel_mono (Work.DSG4c.chartι A b k'.2)).mp ?_
  rw [Category.assoc, cc_awayι_mul_b_right, ccUb, IsOpenImmersion.lift_fac, ccBetaR_fac,
    ← ccBetaL_fac]

/-! ## The chart transition identities -/

lemma cc_alpha_mul (p : Fin (a+1)) :
    (cc_rr (ccP A a b k k') (chartRingA A a k.1) (ccAlphaL A a b k k'))
        (Work.DSG4c.ChartPushout.chartElemAll A a k.1 p)
      * (cc_rr (ccP A a b k k') (chartRingA A a k'.1) (ccAlphaR A a b k k'))
          (Work.DSG4c.ChartPushout.chartElemAll A a k'.1 k.1)
      = (cc_rr (ccP A a b k k') (chartRingA A a k'.1) (ccAlphaR A a b k k'))
          (Work.DSG4c.ChartPushout.chartElemAll A a k'.1 p) := by
  have hL : cc_rr (ccP A a b k k') (chartRingA A a k.1) (ccAlphaL A a b k k') =
      (cc_rr (ccP A a b k k') (HomogeneousLocalization.Away (DSMap.PGr A a)
        (MvPolynomial.X k.1 * MvPolynomial.X k'.1)) (ccUa A a b k k')).comp
        (ccAMa A a b k k') := by
    rw [← ccUa_fac A a b k k', cc_rr_comp, cc_rr_specMap]
    rfl
  have hR : cc_rr (ccP A a b k k') (chartRingA A a k'.1) (ccAlphaR A a b k k') =
      (cc_rr (ccP A a b k k') (HomogeneousLocalization.Away (DSMap.PGr A a)
        (MvPolynomial.X k.1 * MvPolynomial.X k'.1)) (ccUa A a b k k')).comp
        (ccAMa' A a b k k') := by
    rw [← ccUa_fac' A a b k k', cc_rr_comp, cc_rr_specMap]
    rfl
  rw [hL, hR, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, ← map_mul]
  exact congrArg (cc_rr (ccP A a b k k') (HomogeneousLocalization.Away (DSMap.PGr A a)
    (MvPolynomial.X k.1 * MvPolynomial.X k'.1)) (ccUa A a b k k'))
    (cc_awayMap_transition A a k.1 k'.1 p)

lemma cc_beta_mul (q : Fin (b+1)) :
    (cc_rr (ccP A a b k k') (chartRingB A b k.2) (ccBetaL A a b k k'))
        (Work.DSG4c.ChartPushout.chartElemAll A b k.2 q)
      * (cc_rr (ccP A a b k k') (chartRingB A b k'.2) (ccBetaR A a b k k'))
          (Work.DSG4c.ChartPushout.chartElemAll A b k'.2 k.2)
      = (cc_rr (ccP A a b k k') (chartRingB A b k'.2) (ccBetaR A a b k k'))
          (Work.DSG4c.ChartPushout.chartElemAll A b k'.2 q) := by
  have hL : cc_rr (ccP A a b k k') (chartRingB A b k.2) (ccBetaL A a b k k') =
      (cc_rr (ccP A a b k k') (HomogeneousLocalization.Away (DSMap.PGr A b)
        (MvPolynomial.X k.2 * MvPolynomial.X k'.2)) (ccUb A a b k k')).comp
        (ccAMb A a b k k') := by
    rw [← ccUb_fac A a b k k', cc_rr_comp, cc_rr_specMap]
    rfl
  have hR : cc_rr (ccP A a b k k') (chartRingB A b k'.2) (ccBetaR A a b k k') =
      (cc_rr (ccP A a b k k') (HomogeneousLocalization.Away (DSMap.PGr A b)
        (MvPolynomial.X k.2 * MvPolynomial.X k'.2)) (ccUb A a b k k')).comp
        (ccAMb' A a b k k') := by
    rw [← ccUb_fac' A a b k k', cc_rr_comp, cc_rr_specMap]
    rfl
  rw [hL, hR, RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, ← map_mul]
  exact congrArg (cc_rr (ccP A a b k k') (HomogeneousLocalization.Away (DSMap.PGr A b)
    (MvPolynomial.X k.2 * MvPolynomial.X k'.2)) (ccUb A a b k k'))
    (cc_awayMap_transition A b k.2 k'.2 q)

end Main

end Work.DSG2.Segre

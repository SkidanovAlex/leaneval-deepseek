import Mathlib
import Submission.Work.DSG2.Segre.Basic
import Submission.Work.DSG2.Segre.projChart_relation
import Submission.Work.DSG2.Segre.chartElemAll_surjective
import Submission.Work.DSG2.Segre.Triangle
import Submission.Work.DSG4c.ChartPushout.chartToPoly_surjective

import Submission.Work.DSG2.Segre.cc_base

namespace Work.DSG2.Segre

universe u

open CategoryTheory AlgebraicGeometry Limits MvPolynomial
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

section Main

variable (A : Type u) [CommRing A] (a b : ℕ) (k k' : Fin (a+1) × Fin (b+1))

/-- The pullback of the two charts. -/
noncomputable abbrev ccP : Scheme.{u} := pullback (V A a b k).ι (V A a b k').ι

/-- The product-chart coordinate `m'' = x_m · x_{m'}` in `ℙ^N`. -/
noncomputable abbrev ccX2 : MvPolynomial (Fin (segreN a b + 1)) A :=
  MvPolynomial.X (toIdx a b k) * MvPolynomial.X (toIdx a b k')

lemma ccX2_mem : ccX2 A a b k k' ∈ DSMap.PGr A (segreN a b) 2 :=
  SetLike.mul_mem_graded (Work.DSG4c.X_mem A (segreN a b) (toIdx a b k))
    (Work.DSG4c.X_mem A (segreN a b) (toIdx a b k'))

/-- The localisation map from the `m`-chart to the intersection chart of `ℙ^N`. -/
noncomputable abbrev ccAM : HomogeneousLocalization.Away (DSMap.PGr A (segreN a b))
    (MvPolynomial.X (toIdx a b k)) →+* HomogeneousLocalization.Away (DSMap.PGr A (segreN a b))
    (ccX2 A a b k k') :=
  HomogeneousLocalization.awayMap (DSMap.PGr A (segreN a b))
    (Work.DSG4c.X_mem A (segreN a b) (toIdx a b k')) rfl

/-- The localisation map from the `m'`-chart to the intersection chart of `ℙ^N`. -/
noncomputable abbrev ccAM' : HomogeneousLocalization.Away (DSMap.PGr A (segreN a b))
    (MvPolynomial.X (toIdx a b k')) →+* HomogeneousLocalization.Away (DSMap.PGr A (segreN a b))
    (ccX2 A a b k k') :=
  HomogeneousLocalization.awayMap (DSMap.PGr A (segreN a b))
    (Work.DSG4c.X_mem A (segreN a b) (toIdx a b k))
    (mul_comm (MvPolynomial.X (toIdx a b k)) (MvPolynomial.X (toIdx a b k')))

/-- The open immersion of the intersection chart of `ℙ^N` (the chart `D₊(x_m x_{m'})`). -/
noncomputable abbrev ccIntι : Spec (CommRingCat.of (HomogeneousLocalization.Away
    (DSMap.PGr A (segreN a b)) (ccX2 A a b k k'))) ⟶ DSMap.PSpace A (segreN a b) :=
  Proj.awayι (DSMap.PGr A (segreN a b)) (ccX2 A a b k k') (ccX2_mem A a b k k') (by norm_num)

/-- The `k`-chart component of `sigma`. -/
noncomputable abbrev ccPhi : ccP A a b k k' ⟶ Spec (CommRingCat.of
    (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k))) :=
  pullback.fst (V A a b k).ι (V A a b k').ι ≫ (chartIso A a b k).inv ≫
    Spec.map (CommRingCat.ofHom (segreChart A a b k))

/-- The `k'`-chart component of `sigma`. -/
noncomputable abbrev ccPsi : ccP A a b k k' ⟶ Spec (CommRingCat.of
    (Work.DSG4c.awayChart A (segreN a b) (toIdx a b k'))) :=
  pullback.snd (V A a b k).ι (V A a b k').ι ≫ (chartIso A a b k').inv ≫
    Spec.map (CommRingCat.ofHom (segreChart A a b k'))

/-- The left-hand side of the compatibility statement. -/
noncomputable abbrev ccSigmaF : ccP A a b k k' ⟶ DSMap.PSpace A (segreN a b) :=
  pullback.fst (V A a b k).ι (V A a b k').ι ≫ sigma A a b k

/-- The right-hand side of the compatibility statement. -/
noncomputable abbrev ccSigmaG : ccP A a b k k' ⟶ DSMap.PSpace A (segreN a b) :=
  pullback.snd (V A a b k).ι (V A a b k').ι ≫ sigma A a b k'

/-- The structure map of the pullback. -/
noncomputable abbrev ccStr : ccP A a b k k' ⟶ Spec (CommRingCat.of A) :=
  pullback.fst (V A a b k).ι (V A a b k').ι ≫ (V A a b k).ι ≫
    pullback.fst (DSMap.PSpace.toSpec A a) (DSMap.PSpace.toSpec A b) ≫
      DSMap.PSpace.toSpec A a

/-- The `k`-chart of `ℙ^N` seen from the pullback. -/
noncomputable abbrev ccThetaL : ccP A a b k k' ⟶
    Spec (CommRingCat.of (chartRing A a b k)) :=
  pullback.fst (V A a b k).ι (V A a b k').ι ≫ (chartIso A a b k).inv

/-- The `k'`-chart of `ℙ^N` seen from the pullback. -/
noncomputable abbrev ccThetaR : ccP A a b k k' ⟶
    Spec (CommRingCat.of (chartRing A a b k')) :=
  pullback.snd (V A a b k).ι (V A a b k').ι ≫ (chartIso A a b k').inv

/-- The `x`-part of the `k`-chart ring seen from the pullback. -/
noncomputable abbrev ccAlphaL : ccP A a b k k' ⟶ Spec (CommRingCat.of (chartRingA A a k.1)) :=
  ccThetaL A a b k k' ≫ Spec.map (CommRingCat.ofHom (algebraMap (chartRingA A a k.1)
    (chartRing A a b k)))

/-- The `y`-part of the `k`-chart ring seen from the pullback. -/
noncomputable abbrev ccBetaL : ccP A a b k k' ⟶ Spec (CommRingCat.of (chartRingB A b k.2)) :=
  ccThetaL A a b k k' ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A)
    (A := chartRingA A a k.1) (B := chartRingB A b k.2)).toRingHom)

/-- The `x`-part of the `k'`-chart ring seen from the pullback. -/
noncomputable abbrev ccAlphaR : ccP A a b k k' ⟶ Spec (CommRingCat.of (chartRingA A a k'.1)) :=
  ccThetaR A a b k k' ≫ Spec.map (CommRingCat.ofHom (algebraMap (chartRingA A a k'.1)
    (chartRing A a b k')))

/-- The `y`-part of the `k'`-chart ring seen from the pullback. -/
noncomputable abbrev ccBetaR : ccP A a b k k' ⟶ Spec (CommRingCat.of (chartRingB A b k'.2)) :=
  ccThetaR A a b k k' ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A)
    (A := chartRingA A a k'.1) (B := chartRingB A b k'.2)).toRingHom)

lemma ccPhi_fac : ccPhi A a b k k' ≫ Work.DSG4c.chartι A (segreN a b) (toIdx a b k) =
    ccSigmaF A a b k k' := by
  simp only [ccPhi, ccSigmaF, sigma, sigmaChart, Category.assoc, chartIso_hom_sigmaChart]

lemma ccPsi_fac : ccPsi A a b k k' ≫ Work.DSG4c.chartι A (segreN a b) (toIdx a b k') =
    ccSigmaG A a b k k' := by
  simp only [ccPsi, ccSigmaG, sigma, sigmaChart, Category.assoc, chartIso_hom_sigmaChart]

lemma ccIntι_fac : ccIntι A a b k k' =
    Spec.map (CommRingCat.ofHom (ccAM A a b k k')) ≫
      Work.DSG4c.chartι A (segreN a b) (toIdx a b k) := by
  have h : Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (DSMap.PGr A (segreN a b))
        (Work.DSG4c.X_mem A (segreN a b) (toIdx a b k')) rfl)) ≫
      Proj.awayι (DSMap.PGr A (segreN a b)) (MvPolynomial.X (toIdx a b k))
        (Work.DSG4c.X_mem A (segreN a b) (toIdx a b k)) one_pos =
      Proj.awayι (DSMap.PGr A (segreN a b))
        (MvPolynomial.X (toIdx a b k) * MvPolynomial.X (toIdx a b k'))
        (SetLike.mul_mem_graded (Work.DSG4c.X_mem A (segreN a b) (toIdx a b k))
          (Work.DSG4c.X_mem A (segreN a b) (toIdx a b k')))
        (one_pos.trans_le (Nat.le_add_right 1 1)) :=
    Proj.SpecMap_awayMap_awayι ..
  exact (h.trans (cc_awayι_congr _ _ _ _)).symm

lemma ccIntι_fac' : ccIntι A a b k k' =
    Spec.map (CommRingCat.ofHom (ccAM' A a b k k')) ≫
      Work.DSG4c.chartι A (segreN a b) (toIdx a b k') := by
  have h : Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap (DSMap.PGr A (segreN a b))
        (Work.DSG4c.X_mem A (segreN a b) (toIdx a b k))
        (mul_comm (MvPolynomial.X (toIdx a b k)) (MvPolynomial.X (toIdx a b k'))))) ≫
      Proj.awayι (DSMap.PGr A (segreN a b)) (MvPolynomial.X (toIdx a b k'))
        (Work.DSG4c.X_mem A (segreN a b) (toIdx a b k')) one_pos =
      Proj.awayι (DSMap.PGr A (segreN a b))
        (MvPolynomial.X (toIdx a b k) * MvPolynomial.X (toIdx a b k'))
        (SetLike.mul_mem_graded (Work.DSG4c.X_mem A (segreN a b) (toIdx a b k))
          (Work.DSG4c.X_mem A (segreN a b) (toIdx a b k')))
        (one_pos.trans_le (Nat.le_add_right 1 1)) :=
    Proj.SpecMap_awayMap_awayι ..
  exact (h.trans (cc_awayι_congr _ _ _ _)).symm

/-- The chart isomorphism composed with `sigma k`. -/
lemma cc_comp_sigma : (chartIso A a b k).hom ≫ sigma A a b k =
    Spec.map (CommRingCat.ofHom (segreChart A a b k)) ≫
      Work.DSG4c.chartι A (segreN a b) (toIdx a b k) := by
  rw [sigma, sigmaChart, ← Category.assoc, Iso.hom_inv_id_assoc]

/-- The chart isomorphism composed with `sigma k'`. -/
lemma cc_comp_sigma' : (chartIso A a b k').hom ≫ sigma A a b k' =
    Spec.map (CommRingCat.ofHom (segreChart A a b k')) ≫
      Work.DSG4c.chartι A (segreN a b) (toIdx a b k') := by
  rw [sigma, sigmaChart, ← Category.assoc, Iso.hom_inv_id_assoc]

/-- `sigma k`, restricted to the `k`-chart, lands in the `m'`-chart of `ℙ^N`. -/
lemma cc_sigma_preimage_chartOpen :
    (sigma A a b k) ⁻¹ᵁ (Proj.basicOpen (DSMap.PGr A (segreN a b))
        (MvPolynomial.X (toIdx a b k'))) = (V A a b k).ι ⁻¹ᵁ (V A a b k') := by
  have hL : (chartIso A a b k).hom ⁻¹ᵁ ((sigma A a b k) ⁻¹ᵁ
      (Proj.basicOpen (DSMap.PGr A (segreN a b)) (MvPolynomial.X (toIdx a b k')))) =
      PrimeSpectrum.basicOpen (Work.DSG4c.ChartPushout.chartElemAll A a k.1 k'.1 ⊗ₜ[A]
        Work.DSG4c.ChartPushout.chartElemAll A b k.2 k'.2) := by
    rw [← Scheme.Hom.comp_preimage, cc_comp_sigma, Scheme.Hom.comp_preimage,
      cc_chartι_preimage, cc_specMap_preimage_basicOpen,
      cc_segreChart_chartElemAll A a b k (toIdx a b k')]
    simp only [Equiv.symm_apply_apply, segreElemA, segreElemB]
    rfl
  have hR : (chartIso A a b k).hom ⁻¹ᵁ ((V A a b k).ι ⁻¹ᵁ (V A a b k')) =
      PrimeSpectrum.basicOpen (Work.DSG4c.ChartPushout.chartElemAll A a k.1 k'.1 ⊗ₜ[A]
        Work.DSG4c.ChartPushout.chartElemAll A b k.2 k'.2) := by
    rw [← Scheme.Hom.comp_preimage, chartIso_hom_ι, cc_chartIncl_preimage]
  have h2 : (chartIso A a b k).hom ⁻¹ᵁ ((sigma A a b k) ⁻¹ᵁ
      (Proj.basicOpen (DSMap.PGr A (segreN a b)) (MvPolynomial.X (toIdx a b k')))) =
      (chartIso A a b k).hom ⁻¹ᵁ ((V A a b k).ι ⁻¹ᵁ (V A a b k')) := by rw [hL, hR]
  calc (sigma A a b k) ⁻¹ᵁ (Proj.basicOpen (DSMap.PGr A (segreN a b))
          (MvPolynomial.X (toIdx a b k')))
      = ((chartIso A a b k).inv ≫ (chartIso A a b k).hom) ⁻¹ᵁ ((sigma A a b k) ⁻¹ᵁ
          (Proj.basicOpen (DSMap.PGr A (segreN a b)) (MvPolynomial.X (toIdx a b k')))) := by
        rw [Iso.inv_hom_id]; rfl
      _ = (chartIso A a b k).inv ⁻¹ᵁ ((chartIso A a b k).hom ⁻¹ᵁ ((sigma A a b k) ⁻¹ᵁ
          (Proj.basicOpen (DSMap.PGr A (segreN a b)) (MvPolynomial.X (toIdx a b k'))))) := by
        rw [Scheme.Hom.comp_preimage]
      _ = (chartIso A a b k).inv ⁻¹ᵁ ((chartIso A a b k).hom ⁻¹ᵁ
          ((V A a b k).ι ⁻¹ᵁ (V A a b k'))) := by rw [h2]
      _ = ((chartIso A a b k).inv ≫ (chartIso A a b k).hom) ⁻¹ᵁ
          ((V A a b k).ι ⁻¹ᵁ (V A a b k')) := by rw [Scheme.Hom.comp_preimage]
      _ = (V A a b k).ι ⁻¹ᵁ (V A a b k') := by rw [Iso.inv_hom_id]; rfl

/-- `sigma k'`, restricted to the `k'`-chart, lands in the `m`-chart of `ℙ^N`. -/
lemma cc_sigma_preimage_chartOpen' :
    (sigma A a b k') ⁻¹ᵁ (Proj.basicOpen (DSMap.PGr A (segreN a b))
        (MvPolynomial.X (toIdx a b k))) = (V A a b k').ι ⁻¹ᵁ (V A a b k) := by
  have hL : (chartIso A a b k').hom ⁻¹ᵁ ((sigma A a b k') ⁻¹ᵁ
      (Proj.basicOpen (DSMap.PGr A (segreN a b)) (MvPolynomial.X (toIdx a b k)))) =
      PrimeSpectrum.basicOpen (Work.DSG4c.ChartPushout.chartElemAll A a k'.1 k.1 ⊗ₜ[A]
        Work.DSG4c.ChartPushout.chartElemAll A b k'.2 k.2) := by
    rw [← Scheme.Hom.comp_preimage, cc_comp_sigma', Scheme.Hom.comp_preimage,
      cc_chartι_preimage, cc_specMap_preimage_basicOpen,
      cc_segreChart_chartElemAll A a b k' (toIdx a b k)]
    simp only [Equiv.symm_apply_apply, segreElemA, segreElemB]
    rfl
  have hR : (chartIso A a b k').hom ⁻¹ᵁ ((V A a b k').ι ⁻¹ᵁ (V A a b k)) =
      PrimeSpectrum.basicOpen (Work.DSG4c.ChartPushout.chartElemAll A a k'.1 k.1 ⊗ₜ[A]
        Work.DSG4c.ChartPushout.chartElemAll A b k'.2 k.2) := by
    rw [← Scheme.Hom.comp_preimage, chartIso_hom_ι, cc_chartIncl_preimage]
  have h2 : (chartIso A a b k').hom ⁻¹ᵁ ((sigma A a b k') ⁻¹ᵁ
      (Proj.basicOpen (DSMap.PGr A (segreN a b)) (MvPolynomial.X (toIdx a b k)))) =
      (chartIso A a b k').hom ⁻¹ᵁ ((V A a b k').ι ⁻¹ᵁ (V A a b k)) := by rw [hL, hR]
  calc (sigma A a b k') ⁻¹ᵁ (Proj.basicOpen (DSMap.PGr A (segreN a b))
          (MvPolynomial.X (toIdx a b k)))
      = ((chartIso A a b k').inv ≫ (chartIso A a b k').hom) ⁻¹ᵁ ((sigma A a b k') ⁻¹ᵁ
          (Proj.basicOpen (DSMap.PGr A (segreN a b)) (MvPolynomial.X (toIdx a b k)))) := by
        rw [Iso.inv_hom_id]; rfl
      _ = (chartIso A a b k').inv ⁻¹ᵁ ((chartIso A a b k').hom ⁻¹ᵁ ((sigma A a b k') ⁻¹ᵁ
          (Proj.basicOpen (DSMap.PGr A (segreN a b)) (MvPolynomial.X (toIdx a b k))))) := by
        rw [Scheme.Hom.comp_preimage]
      _ = (chartIso A a b k').inv ⁻¹ᵁ ((chartIso A a b k').hom ⁻¹ᵁ
          ((V A a b k').ι ⁻¹ᵁ (V A a b k))) := by rw [h2]
      _ = ((chartIso A a b k').inv ≫ (chartIso A a b k').hom) ⁻¹ᵁ
          ((V A a b k').ι ⁻¹ᵁ (V A a b k)) := by rw [Scheme.Hom.comp_preimage]
      _ = (V A a b k').ι ⁻¹ᵁ (V A a b k) := by rw [Iso.inv_hom_id]; rfl

/-- The intersection of the two chart inclusions is the pullback of the charts. -/
lemma cc_range_fst : Set.range ⇑(pullback.fst (V A a b k).ι (V A a b k').ι) =
    ↑((V A a b k).ι ⁻¹ᵁ (V A a b k')) := by
  rw [IsOpenImmersion.range_pullbackFst (V A a b k').ι (V A a b k).ι,
    Scheme.Opens.opensRange_ι]

/-- The intersection of the two chart inclusions is the pullback of the charts (other order). -/
lemma cc_range_snd : Set.range ⇑(pullback.snd (V A a b k).ι (V A a b k').ι) =
    ↑((V A a b k').ι ⁻¹ᵁ (V A a b k)) := by
  rw [IsOpenImmersion.range_pullbackSnd (V A a b k).ι (V A a b k').ι,
    Scheme.Opens.opensRange_ι]

/-- The coordinate chart of `ℙⁿ` has range the corresponding basic open. -/
lemma cc_range_chartι_gen (A : Type u) [CommRing A] (n : ℕ) (i : Fin (n+1)) :
    Set.range ⇑(Work.DSG4c.chartι A n i) =
      ↑(Proj.basicOpen (DSMap.PGr A n) (MvPolynomial.X i)) := by
  rw [← Scheme.Hom.coe_opensRange (Work.DSG4c.chartι A n i), Proj.opensRange_awayι]

/-- The coordinate chart of `ℙ^N` has range the corresponding basic open. -/
lemma cc_range_chartι (k : Fin (a+1) × Fin (b+1)) :
    Set.range ⇑(Work.DSG4c.chartι A (segreN a b) (toIdx a b k)) =
      ↑(Proj.basicOpen (DSMap.PGr A (segreN a b)) (MvPolynomial.X (toIdx a b k))) :=
  cc_range_chartι_gen A (segreN a b) (toIdx a b k)

/-- The transition relation for the standard charts of `ℙⁿ` (`awayMap` form). -/
lemma cc_awayMap_transition (A : Type u) [CommRing A] (n : ℕ) (i i' p : Fin (n+1)) :
    HomogeneousLocalization.awayMap (DSMap.PGr A n) (Work.DSG4c.X_mem A n i') rfl
        (Work.DSG4c.ChartPushout.chartElemAll A n i p)
      * HomogeneousLocalization.awayMap (DSMap.PGr A n) (Work.DSG4c.X_mem A n i)
          (mul_comm (MvPolynomial.X i) (MvPolynomial.X i'))
          (Work.DSG4c.ChartPushout.chartElemAll A n i' i)
      = HomogeneousLocalization.awayMap (DSMap.PGr A n) (Work.DSG4c.X_mem A n i)
          (mul_comm (MvPolynomial.X i) (MvPolynomial.X i'))
          (Work.DSG4c.ChartPushout.chartElemAll A n i' p) := by
  apply (HomogeneousLocalization.ext_iff_val _ _).mpr
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.awayMap_mk,
    Work.DSG4c.ChartPushout.chartElemAll]
  simp only [HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, one_mul, Submonoid.coe_mul, pow_one]
  ring

/-- The left-hand Segre map lands in the intersection chart of `ℙ^N`. -/
lemma cc_range_F : Set.range ⇑(ccSigmaF A a b k k') ⊆ Set.range ⇑(ccIntι A a b k k') := by
  have hR : Set.range ⇑(ccIntι A a b k k') = ↑(Proj.basicOpen (DSMap.PGr A (segreN a b))
      (ccX2 A a b k k')) := by
    rw [← Scheme.Hom.coe_opensRange (ccIntι A a b k k'), Proj.opensRange_awayι]
  rw [hR, Proj.basicOpen_mul]
  change Set.range ⇑(ccSigmaF A a b k k') ⊆ ↑(Proj.basicOpen (DSMap.PGr A (segreN a b))
      (MvPolynomial.X (toIdx a b k))) ∩ ↑(Proj.basicOpen (DSMap.PGr A (segreN a b))
      (MvPolynomial.X (toIdx a b k')))
  rw [Set.subset_inter_iff]
  refine ⟨?_, ?_⟩
  · refine Set.Subset.trans (Set.range_comp_subset_range
        (⇑(pullback.fst (V A a b k).ι (V A a b k').ι)) (⇑(sigma A a b k))) ?_
    refine Set.Subset.trans (Set.range_comp_subset_range
        (⇑(sigmaChart A a b k)) (⇑(Work.DSG4c.chartι A (segreN a b) (toIdx a b k)))) ?_
    rw [← cc_range_chartι A a b k]
  · intro y hy
    obtain ⟨p, rfl⟩ := hy
    have h : ccSigmaF A a b k k' ⁻¹ᵁ (Proj.basicOpen (DSMap.PGr A (segreN a b))
        (MvPolynomial.X (toIdx a b k'))) = ⊤ := by
      rw [ccSigmaF, Scheme.Hom.comp_preimage, cc_sigma_preimage_chartOpen A a b k k',
        ← Scheme.Hom.comp_preimage]
      have hS : Scheme.Hom.opensRange (pullback.fst (V A a b k).ι (V A a b k').ι) =
          (V A a b k).ι ⁻¹ᵁ (V A a b k') := by
        apply TopologicalSpace.Opens.ext
        rw [Scheme.Hom.coe_opensRange, cc_range_fst]
      rw [Scheme.Hom.comp_preimage, ← hS, Scheme.Hom.preimage_opensRange]
    have hp : p ∈ ccSigmaF A a b k k' ⁻¹ᵁ (Proj.basicOpen (DSMap.PGr A (segreN a b))
        (MvPolynomial.X (toIdx a b k'))) := by rw [h]; trivial
    simpa using hp

/-- The right-hand Segre map lands in the intersection chart of `ℙ^N`. -/
lemma cc_range_G : Set.range ⇑(ccSigmaG A a b k k') ⊆ Set.range ⇑(ccIntι A a b k k') := by
  have hR : Set.range ⇑(ccIntι A a b k k') = ↑(Proj.basicOpen (DSMap.PGr A (segreN a b))
      (ccX2 A a b k k')) := by
    rw [← Scheme.Hom.coe_opensRange (ccIntι A a b k k'), Proj.opensRange_awayι]
  rw [hR, Proj.basicOpen_mul]
  change Set.range ⇑(ccSigmaG A a b k k') ⊆ ↑(Proj.basicOpen (DSMap.PGr A (segreN a b))
      (MvPolynomial.X (toIdx a b k))) ∩ ↑(Proj.basicOpen (DSMap.PGr A (segreN a b))
      (MvPolynomial.X (toIdx a b k')))
  rw [Set.subset_inter_iff]
  refine ⟨?_, ?_⟩
  · intro y hy
    obtain ⟨p, rfl⟩ := hy
    have h : ccSigmaG A a b k k' ⁻¹ᵁ (Proj.basicOpen (DSMap.PGr A (segreN a b))
        (MvPolynomial.X (toIdx a b k))) = ⊤ := by
      rw [ccSigmaG, Scheme.Hom.comp_preimage, cc_sigma_preimage_chartOpen' A a b k k',
        ← Scheme.Hom.comp_preimage]
      have hS : Scheme.Hom.opensRange (pullback.snd (V A a b k).ι (V A a b k').ι) =
          (V A a b k').ι ⁻¹ᵁ (V A a b k) := by
        apply TopologicalSpace.Opens.ext
        rw [Scheme.Hom.coe_opensRange, cc_range_snd]
      rw [Scheme.Hom.comp_preimage, ← hS, Scheme.Hom.preimage_opensRange]
    have hp : p ∈ ccSigmaG A a b k k' ⁻¹ᵁ (Proj.basicOpen (DSMap.PGr A (segreN a b))
        (MvPolynomial.X (toIdx a b k))) := by rw [h]; trivial
    simpa using hp
  · refine Set.Subset.trans (Set.range_comp_subset_range
        (⇑(pullback.snd (V A a b k).ι (V A a b k').ι)) (⇑(sigma A a b k'))) ?_
    refine Set.Subset.trans (Set.range_comp_subset_range
        (⇑(sigmaChart A a b k')) (⇑(Work.DSG4c.chartι A (segreN a b) (toIdx a b k')))) ?_
    rw [← cc_range_chartι A a b k']


/-- The `x`-chart of `ℙ^a`. -/
noncomputable abbrev ccAMa : HomogeneousLocalization.Away (DSMap.PGr A a)
    (MvPolynomial.X k.1) →+* HomogeneousLocalization.Away (DSMap.PGr A a)
    (MvPolynomial.X k.1 * MvPolynomial.X k'.1) :=
  HomogeneousLocalization.awayMap (DSMap.PGr A a) (Work.DSG4c.X_mem A a k'.1) rfl

/-- The other `x`-chart of `ℙ^a`. -/
noncomputable abbrev ccAMa' : HomogeneousLocalization.Away (DSMap.PGr A a)
    (MvPolynomial.X k'.1) →+* HomogeneousLocalization.Away (DSMap.PGr A a)
    (MvPolynomial.X k.1 * MvPolynomial.X k'.1) :=
  HomogeneousLocalization.awayMap (DSMap.PGr A a) (Work.DSG4c.X_mem A a k.1)
    (mul_comm (MvPolynomial.X k.1) (MvPolynomial.X k'.1))

/-- The `y`-chart of `ℙ^b`. -/
noncomputable abbrev ccAMb : HomogeneousLocalization.Away (DSMap.PGr A b)
    (MvPolynomial.X k.2) →+* HomogeneousLocalization.Away (DSMap.PGr A b)
    (MvPolynomial.X k.2 * MvPolynomial.X k'.2) :=
  HomogeneousLocalization.awayMap (DSMap.PGr A b) (Work.DSG4c.X_mem A b k'.2) rfl

/-- The other `y`-chart of `ℙ^b`. -/
noncomputable abbrev ccAMb' : HomogeneousLocalization.Away (DSMap.PGr A b)
    (MvPolynomial.X k'.2) →+* HomogeneousLocalization.Away (DSMap.PGr A b)
    (MvPolynomial.X k.2 * MvPolynomial.X k'.2) :=
  HomogeneousLocalization.awayMap (DSMap.PGr A b) (Work.DSG4c.X_mem A b k.2)
    (mul_comm (MvPolynomial.X k.2) (MvPolynomial.X k'.2))

end Main

end Work.DSG2.Segre

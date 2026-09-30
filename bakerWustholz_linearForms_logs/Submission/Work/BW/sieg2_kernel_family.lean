import Mathlib
import Submission.Work.BW.sieg2Defs
import Submission.Work.BW.siegelCoordFin
import Submission.Work.BW.sieg2KernelDefs
import Submission.Work.BW.sieg2_covolume_transference
import Submission.Work.BW.sieg2_image_covolume
import Submission.Work.BW.sieg2_covolume_pi
import Submission.Work.BW.sieg2_finprod_sup_absNorm
import Submission.Work.BW.sieg2_det_adjoint_le
import Submission.Work.BW.sieg2_covolume_intLatE
import Submission.Work.BW.sieg2_PhiE_surjective
import Submission.Work.BW.sieg2_intLatE_basis
import Submission.Work.BW.kcb_lattice_instances
import Submission.Work.BW.sieg2_kernel_isometry
import Submission.Work.BW.sieg2_kerLatE_family
import Submission.Work.BW.sieg2_arith
import Submission.Work.BW.sieg2_covolume_map_isometry_eq_sqrt_gram_det


open scoped Classical
open NumberField

namespace Work.BW

noncomputable section

set_option maxHeartbeats 1000000 in
theorem sieg2_kernel_family {F : Type*} [Field F] [NumberField F] {M N : ℕ} (hMN : M < N)
    (a : Fin M → Fin N → F) (hli : LinearIndependent F a) :
    ∃ v : Fin (Module.finrank ℚ F * (N - M)) → (Fin N → NumberField.RingOfIntegers F),
      (∀ i n, ∑ m, a n m * (((v i m : NumberField.RingOfIntegers F)) : F) = 0) ∧
      LinearIndependent ℤ (fun i => Work.BW.siegCoord (v i)) ∧
      Work.BW.siegGramDet v ≤
        (((1 / 2 : ℝ) ^ (NumberField.InfinitePlace.nrComplexPlaces F) *
            Real.sqrt |((NumberField.discr F : ℤ) : ℝ)|) ^ (N - M)) *
          (∏ i, (N : ℝ) ^ ((Module.finrank ℚ F : ℝ) / 2) *
            ∏ w : NumberField.InfinitePlace F, (⨆ j : Fin N, w (a i j)) ^ w.mult) *
          (∏ i, ∏ᶠ w : NumberField.FinitePlace F, (⨆ j : Fin N, w (a i j))) := by
  classical
  set c : ℝ := (1 / 2 : ℝ) ^ (NumberField.InfinitePlace.nrComplexPlaces F) *
      Real.sqrt |((NumberField.discr F : ℤ) : ℝ)| with hcdef
  set A : ℝ := (N : ℝ) ^ ((M : ℝ) * (Module.finrank ℚ F : ℝ) / 2) *
      ∏ i : Fin M, ∏ w : NumberField.InfinitePlace F, (⨆ j : Fin N, w (a i j)) ^ w.mult
      with hAdef
  set B : ℝ := ∏ i : Fin M, ∏ᶠ v : NumberField.FinitePlace F, (⨆ j : Fin N, v (a i j))
      with hBdef
  obtain ⟨hdiscL, hspanL, hdiscK, hspanK, hdiscI, hspanI⟩ :=
    kcb_lattice_instances (F := F) hMN a hli
  haveI : DiscreteTopology ↥(intLatE F N) := hdiscL
  haveI : IsZLattice ℝ (intLatE F N) := ⟨hspanL⟩
  haveI : DiscreteTopology ↥(kerLatK (F := F) a) := hdiscK
  haveI : IsZLattice ℝ (kerLatK (F := F) a) := ⟨hspanK⟩
  haveI : DiscreteTopology ↥(imgLatE (F := F) a) := hdiscI
  haveI : IsZLattice ℝ (imgLatE (F := F) a) := ⟨hspanI⟩
  haveI : DiscreteTopology ↥(Submodule.map ((PhiE a).restrictScalars ℤ) (intLatE F N)) := hdiscI
  haveI : IsZLattice ℝ (Submodule.map ((PhiE a).restrictScalars ℤ) (intLatE F N)) := ⟨hspanI⟩
  let Λ : Submodule ℤ ↥(LinearMap.ker (PhiEL a : (EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F)) →ₗ[ℝ]
        (EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F)))) := kerLatK (F := F) a
  haveI : DiscreteTopology ↥Λ := hdiscK
  haveI : IsZLattice ℝ Λ := ⟨hspanK⟩
  have hsurj : Function.Surjective (PhiEL a) :=
    sieg2_PhiE_surjective (F := F) a hli
  obtain ⟨e⟩ := sieg2_kernel_isometry (F := F) hMN a hli
  have hΛmem : ∀ x : ↥(LinearMap.ker (PhiEL a : (EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F)) →ₗ[ℝ]
        (EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F)))),
      x ∈ Λ ↔ (x : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F)) ∈
        intLatE F N := by
    intro x
    change ((LinearMap.ker (PhiEL a : (EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F)) →ₗ[ℝ]
        (EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F)))).subtype.restrictScalars ℤ) x ∈
      kerLatE (F := F) a ↔ (x : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F)) ∈ intLatE F N
    rw [kerLatE, Submodule.mem_inf, Submodule.restrictScalars_mem, LinearMap.mem_ker]
    exact ⟨fun h => h.1, fun h => ⟨h, LinearMap.mem_ker.mp x.2⟩⟩
  have hImg : ∀ y : EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F),
      y ∈ imgLatE (F := F) a ↔
        ∃ x ∈ intLatE F N, PhiEL a x = y := by
    intro y
    constructor
    · intro hy
      rw [imgLatE, Submodule.mem_map] at hy
      obtain ⟨x, hx, hxy⟩ := hy
      exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hx, hxy⟩
      rw [imgLatE, Submodule.mem_map]
      exact ⟨x, hx, hxy⟩
  have htrans := sieg2_covolume_transference (f := PhiEL a) hsurj e
    (intLatE F N) Λ hΛmem (imgLatE (F := F) a) hImg
  have hdiscr : ((NumberField.discr F : ℤ) : ℝ) ≠ 0 := by
    exact_mod_cast NumberField.discr_ne_zero F
  have hcpos : 0 < c := by
    rw [hcdef]
    have h1 : (0 : ℝ) < (1 / 2 : ℝ) ^ (NumberField.InfinitePlace.nrComplexPlaces F) := by
      positivity
    have h2 : (0 : ℝ) < Real.sqrt |((NumberField.discr F : ℤ) : ℝ)| := by
      apply Real.sqrt_pos.mpr
      exact abs_pos.mpr hdiscr
    exact mul_pos h1 h2
  have hne_row : ∀ i : Fin M, ∃ j : Fin N, a i j ≠ 0 := by
    intro i
    by_contra h
    have hzero : a i = 0 := funext fun j => by
      by_contra hj
      exact h ⟨j, hj⟩
    have hrel : ∑ k : Fin M, (if k = i then (1 : F) else 0) • a k = 0 := by
      simp [hzero]
    have h1 := Fintype.linearIndependent_iff.mp hli
      (fun k => if k = i then (1 : F) else 0) hrel i
    rw [if_pos rfl] at h1
    exact one_ne_zero h1
  have hrowpos : ∀ i : Fin M, 0 < ∏ᶠ v : NumberField.FinitePlace F,
      (⨆ j : Fin N, v (a i j)) := by
    intro i
    obtain ⟨j, hj⟩ := hne_row i
    rw [sieg2_finprod_sup_absNorm (F := F) (a := a i) ⟨j, hj⟩]
    refine inv_pos.mpr ?_
    have hz : FractionalIdeal.spanFinset (𝓞 F) Finset.univ (a i) ≠ 0 :=
      FractionalIdeal.spanFinset_ne_zero.mpr ⟨j, Finset.mem_univ j, hj⟩
    have hpos : (0 : ℚ) < FractionalIdeal.absNorm
        (FractionalIdeal.spanFinset (𝓞 F) Finset.univ (a i)) :=
      lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg _)
        (fun h => hz (FractionalIdeal.absNorm_eq_zero_iff.mp h.symm))
    exact_mod_cast hpos
  have hBpos : 0 < B := by
    rw [hBdef]; exact Finset.prod_pos fun i _ => hrowpos i
  have hcovL : ZLattice.covolume (intLatE F N) MeasureTheory.volume = c ^ N := by
    rw [hcdef]; exact sieg2_covolume_intLatE (F := F) N
  have hPhiL : (PhiE a).toContinuousLinearMap = PhiEL a := by
    ext x
    rfl
  have hdet : Real.sqrt (LinearMap.det
      (((PhiEL a).comp (PhiEL a).adjoint :
        EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F) →L[ℝ]
          EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F)) :
        EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F) →ₗ[ℝ]
          EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F))) ≤ A := by
    rw [hAdef, ← hPhiL]
    exact sieg2_det_adjoint_le (F := F) a
  have himg : c ^ M * B⁻¹ ≤ ZLattice.covolume (imgLatE (F := F) a) MeasureTheory.volume := by
    have h := sieg2_image_covolume (F := F) a hli
    rw [hcdef, hBdef, ← Finset.prod_inv_distrib]
    exact h
  have hMvpos : 0 < ZLattice.covolume (imgLatE (F := F) a) MeasureTheory.volume :=
    ZLattice.covolume_pos _ _
  have hΛeq : ZLattice.covolume Λ
        (MeasureTheory.Measure.map e MeasureTheory.volume)
      = ZLattice.covolume (intLatE F N) MeasureTheory.volume *
          Real.sqrt (LinearMap.det
            (((PhiEL a).comp (PhiEL a).adjoint :
              EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F) →L[ℝ]
                EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F)) :
              EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F) →ₗ[ℝ]
                EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F))) /
        ZLattice.covolume (imgLatE (F := F) a) MeasureTheory.volume := by
    rw [eq_div_iff hMvpos.ne']
    exact htrans
  have hb : ZLattice.covolume Λ
        (MeasureTheory.Measure.map e MeasureTheory.volume) ≤ c ^ (N - M) * A * B := by
    rw [hΛeq, hcovL, div_le_iff₀ hMvpos]
    have h1 : c ^ N * Real.sqrt (LinearMap.det
        (((PhiEL a).comp (PhiEL a).adjoint :
          EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F) →L[ℝ]
            EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F)) :
          EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F) →ₗ[ℝ]
            EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F)))
        ≤ c ^ N * A := mul_le_mul_of_nonneg_left hdet (pow_nonneg hcpos.le N)
    have h2 : (c ^ (N - M) * A * B) * (c ^ M * B⁻¹) = c ^ N * A := by
      have hcB : B * B⁻¹ = 1 := mul_inv_cancel₀ hBpos.ne'
      have hcp : c ^ (N - M) * c ^ M = c ^ N := by
        rw [← pow_add, Nat.sub_add_cancel hMN.le]
      calc (c ^ (N - M) * A * B) * (c ^ M * B⁻¹)
          = (c ^ (N - M) * c ^ M) * (A * (B * B⁻¹)) := by ring
        _ = c ^ N * A := by rw [hcB, hcp]; ring
    have h3 : (c ^ (N - M) * A * B) * (c ^ M * B⁻¹) ≤ (c ^ (N - M) * A * B) *
        ZLattice.covolume (imgLatE (F := F) a) MeasureTheory.volume :=
      mul_le_mul_of_nonneg_left himg (by
        have hA0 : 0 ≤ A := by
          rw [hAdef]
          refine mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) ?_
          refine Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun w _ => ?_
          exact pow_nonneg (Real.iSup_nonneg fun j => w.1.nonneg _) _
        exact mul_nonneg (mul_nonneg (pow_nonneg hcpos.le _) hA0) hBpos.le)
    exact le_trans h1 (le_trans (le_of_eq h2.symm) h3)
  haveI : Module.Finite ℤ ↥(kerLatK (F := F) a) := ZLattice.module_finite (K := ℝ) (L := kerLatK (F := F) a)
  haveI : Module.Free ℤ ↥(kerLatK (F := F) a) := ZLattice.module_free (K := ℝ) (L := kerLatK (F := F) a)
  have hkerfr : Module.finrank ℝ ↥(LinearMap.ker (PhiE a : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) →ₗ[ℝ] EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F)))
      = Module.finrank ℚ F * (N - M) := by
    have hsurjE : Function.Surjective (PhiE a : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) →ₗ[ℝ] EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F)) := hsurj
    have hrange : LinearMap.range (PhiE a : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) →ₗ[ℝ] EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F)) = ⊤ :=
      LinearMap.range_eq_top.mpr hsurjE
    have hpk := LinearMap.finrank_range_add_finrank_ker (PhiE a : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) →ₗ[ℝ] EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F))
    have h1 : Module.finrank ℝ (LinearMap.range (PhiE a : EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F) →ₗ[ℝ] EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F))) = Module.finrank ℝ (EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F)) := by
      rw [hrange]; exact Submodule.topEquiv.finrank_eq
    rw [h1] at hpk
    have hcardIdx : Fintype.card (NumberField.mixedEmbedding.index F) = Module.finrank ℚ F := by
      rw [← Module.finrank_eq_card_basis (NumberField.mixedEmbedding.stdBasis F)]
      exact NumberField.mixedEmbedding.finrank F
    have h2 : Module.finrank ℝ (EuclideanSpace ℝ (Fin M × NumberField.mixedEmbedding.index F)) =
        M * Module.finrank ℚ F := by
      rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, hcardIdx]
    have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin N × NumberField.mixedEmbedding.index F)) =
        N * Module.finrank ℚ F := by
      rw [finrank_euclideanSpace, Fintype.card_prod, Fintype.card_fin, hcardIdx]
    rw [h2, h3] at hpk
    have hsub : Module.finrank ℚ F * (N - M) =
        N * Module.finrank ℚ F - M * Module.finrank ℚ F := by
      rw [Nat.mul_sub_left_distrib, mul_comm (Module.finrank ℚ F) N,
        mul_comm (Module.finrank ℚ F) M]
    rw [hsub]
    omega
  have hfin : Module.finrank ℤ ↥(kerLatK (F := F) a) = Module.finrank ℚ F * (N - M) := by
    rw [ZLattice.rank (K := ℝ) (L := kerLatK (F := F) a)]
    exact hkerfr
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ ↥(kerLatK (F := F) a)) =
      Module.finrank ℚ F * (N - M) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, hfin]
  let ee : Module.Free.ChooseBasisIndex ℤ ↥(kerLatK (F := F) a) ≃
      Fin (Module.finrank ℚ F * (N - M)) :=
    Fintype.equivOfCardEq (by rw [hcard, Fintype.card_fin])
  let b : Module.Basis (Fin (Module.finrank ℚ F * (N - M))) ℤ ↥(kerLatK (F := F) a) :=
    (Module.Free.chooseBasis ℤ ↥(kerLatK (F := F) a)).reindex ee
  obtain ⟨v, hv1, hv2, hv3⟩ := sieg2_kerLatE_family (F := F) hMN a hli b
  refine ⟨v, hv1, hv2, ?_⟩
  have hb' : ZLattice.covolume (kerLatK (F := F) a)
        (MeasureTheory.Measure.map e MeasureTheory.volume)
      = Real.sqrt (Matrix.det (Matrix.of (fun i j : Fin (Module.finrank ℚ F * (N - M)) =>
          inner ℝ (kerLatEval (F := F) a (b i)) (kerLatEval (F := F) a (b j))))) := by
    rw [sieg2_covolume_map_isometry_eq_sqrt_gram_det e (kerLatK (F := F) a) b]
    simp only [Submodule.coe_inner, kerLatEval]
  rw [hv3, ← hb']
  refine le_trans hb (le_of_eq ?_)
  rw [hAdef, hBdef]
  rw [mul_assoc (c ^ (N - M))]
  rw [sieg2_arith (F := F) a]
  rw [← mul_assoc]

end

end Work.BW

import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.BoxD1Pair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.C2Pieces

open MeasureTheory
open scoped ENNReal

/-- The `r2 ↔ (y,z)` Fubini rearrangement for a box-measurable kernel `H` and a bounded
box-function `M`.  Everything is bounded on the (finite measure) regions, so the
integrability hypotheses of Fubini are immediate. -/
theorem box_pair_slotMean_swap {N : ℕ} {ℓ : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : MeasurableSet A) (hℓ : 0 < ℓ) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {H : Submission.BoseGases.X N → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    {M : Submission.BoseGases.X N → ℂ}
    (hHm : Measurable (fun q : Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3) ×
      EuclideanSpace ℝ (Fin 3) => H q.1 q.2.1 q.2.2))
    (hHb : ∃ C : ℝ, 0 ≤ C ∧ ∀ r2 ∈ Submission.BoseGases.abox N ℓ,
      ∀ y ∈ A, ∀ z ∈ A, ‖H r2 y z‖ ≤ C)
    (hMm : Measurable M)
    (hMb : ∃ C : ℝ, 0 ≤ C ∧ ∀ r2 ∈ Submission.BoseGases.abox N ℓ, ‖M r2‖ ≤ C) :
    (∫ r2 in Submission.BoseGases.abox N ℓ,
        (∫ y in A, ∫ z in A, H r2 y z) * M r2)
      = ∫ y in A, ∫ z in A, ∫ r2 in Submission.BoseGases.abox N ℓ, H r2 y z * M r2 := by
  classical
  obtain ⟨C1, hC1nn, hHbd⟩ := hHb
  obtain ⟨C2, hC2nn, hMbd⟩ := hMb
  -- ### the relevant (finite) measures
  have hboxm : MeasurableSet (Submission.BoseGases.abox N ℓ) :=
    Submission.BoseGases.abox_measurable N ℓ
  have hboxlt : (volume : Measure (Submission.BoseGases.X N))
      (Submission.BoseGases.abox N ℓ) < ∞ :=
    Submission.BoseGases.abox_lt_top N ℓ hℓ.le
  have hAlt : (volume : Measure (EuclideanSpace ℝ (Fin 3))) A < ∞ :=
    lt_of_le_of_lt (measure_mono hAc) (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
  haveI hfinbox : IsFiniteMeasure
      ((volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hboxlt⟩
  haveI hfinA : IsFiniteMeasure
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hAlt⟩
  -- ### step 1: pull the constant `M r2` inside the double integral over `A × A`
  have hstep1 : (∫ r2 in Submission.BoseGases.abox N ℓ,
        (∫ y in A, ∫ z in A, H r2 y z) * M r2)
      = ∫ r2 in Submission.BoseGases.abox N ℓ,
          ∫ y in A, ∫ z in A, H r2 y z * M r2 := by
    apply integral_congr_ae
    filter_upwards with r2
    simp only [integral_mul_const]
  -- ### joint measurability of the integrand on `(X N × E3) × E3`
  have hFmeas : Measurable (fun w : (Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3)) ×
      EuclideanSpace ℝ (Fin 3) => H w.1.1 w.1.2 w.2 * M w.1.1) := by
    have hmap : Measurable (fun w : (Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3)) ×
        EuclideanSpace ℝ (Fin 3) => (w.1.1, (w.1.2, w.2))) :=
      Measurable.prodMk (measurable_fst.comp measurable_fst)
        (Measurable.prodMk (measurable_snd.comp measurable_fst) measurable_snd)
    exact (hHm.comp hmap).mul (hMm.comp (measurable_fst.comp measurable_fst))
  -- ### the `r2`-marginal is integrable (bounded on a finite measure space)
  have hIntmeas : AEStronglyMeasurable
      (Function.uncurry (fun r2 : Submission.BoseGases.X N => fun y : EuclideanSpace ℝ (Fin 3) =>
        ∫ z in A, H r2 y z * M r2))
      (((volume : Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A)) :=
    (hFmeas.aestronglyMeasurable).integral_prod_right'
      (μ := ((volume : Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A))
      (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A)
      (f := fun w : (Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3)) ×
        EuclideanSpace ℝ (Fin 3) => H w.1.1 w.1.2 w.2 * M w.1.1)
  have hint_ae : ∀ᵐ p ∂(((volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A)),
      ‖Function.uncurry (fun r2 : Submission.BoseGases.X N =>
        fun y : EuclideanSpace ℝ (Fin 3) => ∫ z in A, H r2 y z * M r2) p‖ ≤
        (C1 * C2) * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A := by
    have hmem : ∀ᵐ p ∂(((volume : Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)).prod
          ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A)),
        p ∈ Submission.BoseGases.abox N ℓ ×ˢ A := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (hboxm.prod hA)
    filter_upwards [hmem] with p hp
    have hp1 : p.1 ∈ Submission.BoseGases.abox N ℓ := hp.1
    have hp2 : p.2 ∈ A := hp.2
    show ‖∫ z in A, H p.1 p.2 z * M p.1‖ ≤
      (C1 * C2) * (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A
    refine norm_setIntegral_le_of_norm_le_const hAlt (fun z hz => ?_)
    rw [norm_mul]
    exact mul_le_mul (hHbd p.1 hp1 p.2 hp2 z hz) (hMbd p.1 hp1) (norm_nonneg _) hC1nn
  have hInt : Integrable
      (Function.uncurry (fun r2 : Submission.BoseGases.X N => fun y : EuclideanSpace ℝ (Fin 3) =>
        ∫ z in A, H r2 y z * M r2))
      (((volume : Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A)) :=
    Integrable.of_bound hIntmeas ((C1 * C2) *
      (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A) hint_ae
  -- ### Fubini: swap the `r2`-integral with the `y`-integral
  have hfub : (∫ r2 in Submission.BoseGases.abox N ℓ, ∫ y in A,
        ∫ z in A, H r2 y z * M r2)
      = ∫ y in A, ∫ r2 in Submission.BoseGases.abox N ℓ,
          ∫ z in A, H r2 y z * M r2 :=
    integral_integral_swap
      (μ := (volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ))
      (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A)
      (f := fun r2 y => ∫ z in A, H r2 y z * M r2) hInt
  -- ### for a.e. fixed `y ∈ A`: swap the `r2`- and `z`-integrals
  have hswapzy : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A,
      (∫ r2 in Submission.BoseGases.abox N ℓ, ∫ z in A, H r2 y z * M r2)
        = ∫ z in A, ∫ r2 in Submission.BoseGases.abox N ℓ, H r2 y z * M r2 := by
    rw [ae_restrict_iff' hA]
    filter_upwards with y hy
    have hmeas_y : Measurable (fun p : Submission.BoseGases.X N ×
        EuclideanSpace ℝ (Fin 3) => H p.1 y p.2 * M p.1) := by
      have hg : Measurable (fun p : Submission.BoseGases.X N × EuclideanSpace ℝ (Fin 3) =>
          (p.1, (y, p.2))) :=
        Measurable.prodMk measurable_fst
          ((measurable_prodMk_left (x := y)).comp measurable_snd)
      exact (hHm.comp hg).mul (hMm.comp measurable_fst)
    have hbd_y : ∀ᵐ p ∂(((volume : Measure (Submission.BoseGases.X N)).restrict
          (Submission.BoseGases.abox N ℓ)).prod
          ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A)),
        ‖H p.1 y p.2 * M p.1‖ ≤ C1 * C2 := by
      have hmem : ∀ᵐ p ∂(((volume : Measure (Submission.BoseGases.X N)).restrict
            (Submission.BoseGases.abox N ℓ)).prod
            ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A)),
          p ∈ Submission.BoseGases.abox N ℓ ×ˢ A := by
        rw [Measure.prod_restrict]
        exact ae_restrict_mem (hboxm.prod hA)
      filter_upwards [hmem] with p hp
      have hp1 : p.1 ∈ Submission.BoseGases.abox N ℓ := hp.1
      have hp2 : p.2 ∈ A := hp.2
      rw [norm_mul]
      exact mul_le_mul (hHbd p.1 hp1 y hy p.2 hp2) (hMbd p.1 hp1) (norm_nonneg _) hC1nn
    have hint_y : Integrable (fun p : Submission.BoseGases.X N ×
          EuclideanSpace ℝ (Fin 3) => H p.1 y p.2 * M p.1)
        (((volume : Measure (Submission.BoseGases.X N)).restrict
            (Submission.BoseGases.abox N ℓ)).prod
          ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A)) :=
      Integrable.of_bound hmeas_y.aestronglyMeasurable (C1 * C2) hbd_y
    exact integral_integral_swap
      (μ := (volume : Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N ℓ))
      (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A)
      (f := fun r2 z => H r2 y z * M r2) hint_y
  -- ### assembly
  calc (∫ r2 in Submission.BoseGases.abox N ℓ,
          (∫ y in A, ∫ z in A, H r2 y z) * M r2)
      = ∫ r2 in Submission.BoseGases.abox N ℓ,
          ∫ y in A, ∫ z in A, H r2 y z * M r2 := hstep1
    _ = ∫ y in A, ∫ r2 in Submission.BoseGases.abox N ℓ,
          ∫ z in A, H r2 y z * M r2 := hfub
    _ = ∫ y in A, ∫ z in A,
          ∫ r2 in Submission.BoseGases.abox N ℓ, H r2 y z * M r2 :=
        integral_congr_ae hswapzy

end Work.BoseFixB1.C2Pieces

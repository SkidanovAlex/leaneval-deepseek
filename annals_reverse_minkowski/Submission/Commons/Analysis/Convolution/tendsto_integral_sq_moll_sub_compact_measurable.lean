import Mathlib
import Submission.Commons.Analysis.Convolution.tendsto_lintegral_convolution_sub_sq

namespace Commons.Analysis.Convolution

open MeasureTheory Filter
open scoped Topology ENNReal Pointwise

private lemma norm_sq_ofReal_cast_local (z : ℝ) : ‖(z : ℂ)‖ ^ 2 = z ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring

theorem tendsto_integral_sq_moll_sub_compact_measurable {n : ℕ} {ι : Type*} {l : Filter ι}
    (ρ : ι → EuclideanSpace ℝ (Fin n) → ℝ) (R : ι → ℝ)
    (hρnn : ∀ i x, 0 ≤ ρ i x) (hρi : ∀ i, MeasureTheory.Integrable (ρ i) (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (hρ1 : ∀ i, ∫ x, ρ i x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (hRpos : ∀ i, 0 ≤ R i) (hR : Filter.Tendsto R l (nhds 0))
    (hRs : ∀ i x, R i < ‖x‖ → ρ i x = 0)
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (humeas : MeasureTheory.AEStronglyMeasurable u (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (hu : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      MeasureTheory.IntegrableOn (fun x => u x ^ 2) K (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) :
    Filter.Tendsto (fun i => ∫ x in K,
        ((∫ y, ρ i y • u (x - y) ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) - u x) ^ 2
        ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) l (nhds 0) := by
  classical
  -- A compact neighbourhood of `K`.
  set K' : Set (EuclideanSpace ℝ (Fin n)) :=
    K + Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 with hK'def
  have hK'c : IsCompact K' := by
    rw [hK'def]; exact hK.add (isCompact_closedBall _ _)
  have hK'meas : MeasurableSet K' := hK'c.isClosed.measurableSet
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hKK' : K ⊆ K' := by
    intro x hx
    rw [hK'def]
    exact Set.mem_add.mpr ⟨x, hx, 0, by simp, by simp⟩
  -- The truncated function, which lies in `L²`.
  set w : EuclideanSpace ℝ (Fin n) → ℝ := K'.indicator u with hwdef
  have hw_memLp : MemLp w 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [hwdef, memLp_indicator_iff_restrict hK'meas]
    exact (memLp_two_iff_integrable_sq humeas.restrict).2 (hu K' hK'c)
  have hW_memLp : MemLp (fun x => ((w x : ℝ) : ℂ)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := hw_memLp.ofReal
  -- `L²` convergence of the mollification of `w`.
  have hD := tendsto_lintegral_convolution_sub_sq ρ hρnn hρi hρ1 R hRpos hR hRs
    (fun x => ((w x : ℝ) : ℂ)) hW_memLp
  -- The relevant integrands.
  set gu : ι → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i x => ((∫ y, ρ i y • u (x - y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) - u x) ^ 2
    with hgudef
  set gw : ι → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i x => ((∫ y, ρ i y • w (x - y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) - w x) ^ 2
    with hgwdef
  set D : ι → ℝ≥0∞ :=
    fun i => ∫⁻ x, ENNReal.ofReal (gw i x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
    with hDdef
  -- The complex convolution of the real `w` is the coercion of the real convolution.
  have hconvC : ∀ i x,
      (∫ y, ρ i y • ((w (x - y) : ℝ) : ℂ) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        = ((∫ y, ρ i y • w (x - y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) : ℝ) : ℂ) := by
    intro i x
    rw [show (∫ y, ρ i y • ((w (x - y) : ℝ) : ℂ) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        = ∫ y, ((ρ i y • w (x - y) : ℝ) : ℂ) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) from
      integral_congr_ae (Eventually.of_forall fun y => by
        show ρ i y • ((w (x - y) : ℝ) : ℂ) = ((ρ i y • w (x - y) : ℝ) : ℂ)
        rw [Complex.real_smul, ← Complex.ofReal_mul, smul_eq_mul])]
    exact integral_ofReal
  have hD' : Tendsto D l (nhds 0) := by
    rw [hDdef]
    refine Filter.Tendsto.congr' (Eventually.of_forall fun i => ?_) hD
    apply lintegral_congr
    intro x
    rw [hconvC i x, ← Complex.ofReal_sub, norm_sq_ofReal_cast_local]
  -- Pointwise equality of the two convolutions on `K`, for small enough radii.
  have hconv_eq : ∀ i, R i ≤ 1 → ∀ x ∈ K,
      (∫ y, ρ i y • u (x - y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        = (∫ y, ρ i y • w (x - y) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    intro i hi x hx
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    change ρ i y • u (x - y) = ρ i y • w (x - y)
    by_cases hy : R i < ‖y‖
    · rw [hRs i y hy]; simp
    · have hmem : x - y ∈ K' := by
        rw [hK'def, sub_eq_add_neg]
        refine Set.mem_add.mpr ⟨x, hx, -y, ?_, rfl⟩
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_neg]
        exact le_trans (le_of_not_gt hy) hi
      have : w (x - y) = u (x - y) := by
        rw [hwdef]; exact Set.indicator_of_mem hmem u
      rw [this]
  -- The `K`-integrals agree for small enough radii.
  have hguw : ∀ i, R i ≤ 1 → ∀ x ∈ K, gu i x = gw i x := by
    intro i hi x hx
    simp only [hgudef, hgwdef]
    rw [hconv_eq i hi x hx]
    have : w x = u x := by
      rw [hwdef]; exact Set.indicator_of_mem (hKK' hx) u
    rw [this]
  -- The key bound.
  have hkey : ∀ i, R i ≤ 1 → D i < ⊤ →
      ∫ x in K, gu i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) ≤ (D i).toReal := by
    intro i hi hDfin
    by_cases hmeas : AEStronglyMeasurable (gu i) (volume.restrict K)
    · rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (fun x => sq_nonneg _)) hmeas]
      apply ENNReal.toReal_mono hDfin.ne
      calc ∫⁻ x, ENNReal.ofReal (gu i x) ∂(volume.restrict K)
          = ∫⁻ x in K, ENNReal.ofReal (gu i x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := rfl
        _ = ∫⁻ x in K, ENNReal.ofReal (gw i x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
              setLIntegral_congr_fun hKmeas (fun x hx => by rw [hguw i hi x hx])
        _ ≤ D i := by
              simpa [hDdef] using lintegral_mono_set (Set.subset_univ K)
    · have hz : ∫ x in K, gu i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 0 := by
        rw [show (∫ x in K, gu i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
            = ∫ x, gu i x ∂(volume.restrict K) from rfl]
        exact integral_undef (fun h => hmeas h.aestronglyMeasurable)
      rw [hz]
      exact ENNReal.toReal_nonneg
  -- Eventual finiteness of `D` and smallness of the radius.
  have hDfin : ∀ᶠ i in l, D i < ⊤ :=
    hD'.eventually (isOpen_Iio.mem_nhds (show (0 : ℝ≥0∞) < ⊤ by simp))
  have hR1 : ∀ᶠ i in l, R i ≤ 1 :=
    (hR.eventually (isOpen_Iio.mem_nhds (show (0 : ℝ) < 1 by norm_num))).mono
      (fun i hi => le_of_lt hi)
  have hDreal : Tendsto (fun i => (D i).toReal) l (nhds 0) := by
    have h0 : (0 : ℝ≥0∞) ≠ ∞ := by simp
    have := (ENNReal.tendsto_toReal h0).comp hD'
    simpa only [Function.comp_def, ENNReal.toReal_zero] using this
  change Tendsto (fun i => ∫ x in K, gu i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) l (nhds 0)
  refine squeeze_zero' (Eventually.of_forall (fun i => integral_nonneg (fun x => sq_nonneg _))) ?_ hDreal
  filter_upwards [hR1, hDfin] with i hi hfin
  exact hkey i hi hfin

end Commons.Analysis.Convolution

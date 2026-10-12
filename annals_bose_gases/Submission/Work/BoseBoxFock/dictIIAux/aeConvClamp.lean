import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.dictIIDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.dictIIAux

open MeasureTheory Filter
open scoped Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem aeConvClamp {ℓ : ℝ} {f k : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hkI : MeasureTheory.Integrable (Function.uncurry k) MeasureTheory.volume)
    (hfe : Function.uncurry f =ᵐ[MeasureTheory.volume] Function.uncurry k) :
    ∀ᵐ y ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)),
      ∀ᵐ u ∂((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.acube ℓ)),
        Filter.Tendsto (fun N : ℕ => Work.BoseBoxFock.qmqKR ℓ (Work.BoseBoxFock.clampK N f) u y)
          Filter.atTop (nhds (Work.BoseBoxFock.qmqKR ℓ k u y)) := by
  let A : Set E3 := Submission.BoseGases.acube ℓ
  let ν : Measure E3 := (volume : Measure E3).restrict A
  let A1 : E3 → Prop := fun u => Tendsto (fun N : ℕ => ∫ y in A, Work.BoseBoxFock.clampK N f u y) atTop (𝓝 (∫ y in A, k u y))
  let A2 : E3 → Prop := fun y => Tendsto (fun N : ℕ => ∫ u in A, Work.BoseBoxFock.clampK N f u y) atTop (𝓝 (∫ u in A, k u y))
  let P : E3 × E3 → Prop := fun p => Tendsto (fun N : ℕ => Work.BoseBoxFock.qmqKR ℓ (Work.BoseBoxFock.clampK N f) p.1 p.2) atTop (𝓝 (Work.BoseBoxFock.qmqKR ℓ k p.1 p.2))
  have hkmeas : AEStronglyMeasurable (Function.uncurry k) (volume : Measure (E3 × E3)) := hkI.aestronglyMeasurable
  -- the first `Q M Q` row: `u ↦ ∫_{Λ} clampK N f u ·`
  have hrow1 : ∀ᵐ u ∂ν, A1 u := by
    have hksec_meas : ∀ᵐ u ∂(volume : Measure E3), AEStronglyMeasurable (fun y => k u y) (volume : Measure E3) :=
      AEStronglyMeasurable.prodMk_left hkmeas
    have hksec_int : ∀ᵐ u ∂(volume : Measure E3), Integrable (fun y => k u y) (volume : Measure E3) :=
      hkI.prod_right_ae
    have hfsec : ∀ᵐ u ∂(volume : Measure E3), (fun y => f u y) =ᵐ[(volume : Measure E3)] (fun y => k u y) :=
      Measure.ae_ae_eq_of_ae_eq_uncurry hfe
    filter_upwards [ae_restrict_of_ae hksec_meas, ae_restrict_of_ae hksec_int, ae_restrict_of_ae hfsec] with u hmeas hint heq
    have heqν : ∀ᵐ y ∂ν, f u y = k u y := ae_restrict_of_ae heq
    have hmeasν : AEStronglyMeasurable (fun y => k u y) ν := hmeas.restrict
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun y => ‖k u y‖) ?_ ?_ ?_ ?_
    · intro N
      have hφ : Continuous (fun x : ℝ => max (-(N:ℝ)) (min (N:ℝ) x)) :=
        continuous_const.max (continuous_const.min continuous_id)
      have h1 : AEStronglyMeasurable (fun y => Work.BoseBoxFock.clampK N k u y) ν :=
        hφ.comp_aestronglyMeasurable hmeasν
      refine h1.congr ?_
      filter_upwards [heqν] with y hy
      show Work.BoseBoxFock.clampK N k u y = Work.BoseBoxFock.clampK N f u y
      simp only [Work.BoseBoxFock.clampK, hy]
    · exact hint.norm.mono_measure Measure.restrict_le_self
    · intro N
      filter_upwards [heqν] with y hy
      calc ‖Work.BoseBoxFock.clampK N f u y‖ = |Work.BoseBoxFock.clampK N f u y| := by rw [Real.norm_eq_abs]
        _ ≤ |f u y| := Work.BoseBoxFock.clampK_abs_le N f u y
        _ = |k u y| := by rw [hy]
        _ = ‖k u y‖ := by rw [Real.norm_eq_abs]
    · filter_upwards [heqν] with y hy
      have h := Work.BoseBoxFock.clampK_tendsto f u y
      rw [show f u y = k u y from hy] at h
      exact h
  -- the transposed a.e. equality of the two kernels
  have hfeS : Function.uncurry (fun a b => f b a) =ᵐ[((volume : Measure E3).prod (volume : Measure E3))] Function.uncurry (fun a b => k b a) := by
    have h := (Measure.measurePreserving_swap (μ := (volume : Measure E3)) (ν := (volume : Measure E3))).quasiMeasurePreserving.ae hfe
    filter_upwards [h] with z hz
    simpa [Function.uncurry, Prod.swap] using hz
  -- the second `Q M Q` row: `y ↦ ∫_{Λ} clampK N f · y`
  have hrow2 : ∀ᵐ y ∂ν, A2 y := by
    have hksec_meas : ∀ᵐ y ∂(volume : Measure E3), AEStronglyMeasurable (fun u => k u y) (volume : Measure E3) :=
      hkmeas.prodMk_right
    have hksec_int : ∀ᵐ y ∂(volume : Measure E3), Integrable (fun u => k u y) (volume : Measure E3) :=
      hkI.prod_left_ae
    have hfsec2 : ∀ᵐ y ∂(volume : Measure E3), (fun u => f u y) =ᵐ[(volume : Measure E3)] (fun u => k u y) :=
      Measure.ae_ae_eq_of_ae_eq_uncurry hfeS
    filter_upwards [ae_restrict_of_ae hksec_meas, ae_restrict_of_ae hksec_int, ae_restrict_of_ae hfsec2] with y hmeas hint heq
    have heqν : ∀ᵐ u ∂ν, f u y = k u y := ae_restrict_of_ae heq
    have hmeasν : AEStronglyMeasurable (fun u => k u y) ν := hmeas.restrict
    refine MeasureTheory.tendsto_integral_of_dominated_convergence (fun u => ‖k u y‖) ?_ ?_ ?_ ?_
    · intro N
      have hφ : Continuous (fun x : ℝ => max (-(N:ℝ)) (min (N:ℝ) x)) :=
        continuous_const.max (continuous_const.min continuous_id)
      have h1 : AEStronglyMeasurable (fun u => Work.BoseBoxFock.clampK N k u y) ν :=
        hφ.comp_aestronglyMeasurable hmeasν
      refine h1.congr ?_
      filter_upwards [heqν] with u hu
      show Work.BoseBoxFock.clampK N k u y = Work.BoseBoxFock.clampK N f u y
      simp only [Work.BoseBoxFock.clampK, hu]
    · exact hint.norm.mono_measure Measure.restrict_le_self
    · intro N
      filter_upwards [heqν] with u hu
      calc ‖Work.BoseBoxFock.clampK N f u y‖ = |Work.BoseBoxFock.clampK N f u y| := by rw [Real.norm_eq_abs]
        _ ≤ |f u y| := Work.BoseBoxFock.clampK_abs_le N f u y
        _ = |k u y| := by rw [hu]
        _ = ‖k u y‖ := by rw [Real.norm_eq_abs]
    · filter_upwards [heqν] with u hu
      have h := Work.BoseBoxFock.clampK_tendsto f u y
      rw [show f u y = k u y from hu] at h
      exact h
  have hle : ν.prod ν ≤ (volume : Measure (E3 × E3)) := by
    rw [show (volume : Measure (E3 × E3)) = (volume : Measure E3).prod (volume : Measure E3) from rfl]
    exact Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self
  have hfeν : Function.uncurry f =ᵐ[ν.prod ν] Function.uncurry k :=
    Filter.Eventually.filter_mono (ae_mono hle) hfe
  have hkI2 : Integrable (Function.uncurry k) (ν.prod ν) := hkI.mono_measure hle
  -- the constant `Q M Q` row: the double box average
  have hrow3 : Tendsto (fun N : ℕ => ∫ u in A, ∫ y in A, Work.BoseBoxFock.clampK N f u y) atTop
      (𝓝 (∫ u in A, ∫ y in A, k u y)) := by
    have hASM : ∀ N, AEStronglyMeasurable (Function.uncurry (Work.BoseBoxFock.clampK N f)) (ν.prod ν) := by
      intro N
      have hkASM : AEStronglyMeasurable (Function.uncurry k) (ν.prod ν) := hkI.aestronglyMeasurable.mono_measure hle
      have hφ : Continuous (fun x : ℝ => max (-(N:ℝ)) (min (N:ℝ) x)) :=
        continuous_const.max (continuous_const.min continuous_id)
      have h1 : AEStronglyMeasurable (fun z : E3 × E3 => Work.BoseBoxFock.clampK N k z.1 z.2) (ν.prod ν) :=
        hφ.comp_aestronglyMeasurable hkASM
      refine h1.congr ?_
      filter_upwards [hfeν] with z hz
      have hz' : f z.1 z.2 = k z.1 z.2 := hz
      show Work.BoseBoxFock.clampK N k z.1 z.2 = Work.BoseBoxFock.clampK N f z.1 z.2
      simp only [Work.BoseBoxFock.clampK, hz']
    have hbound : ∀ N, ∀ᵐ z ∂(ν.prod ν), ‖Function.uncurry (Work.BoseBoxFock.clampK N f) z‖ ≤ ‖Function.uncurry k z‖ := by
      intro N
      filter_upwards [hfeν] with z hz
      have hz' : f z.1 z.2 = k z.1 z.2 := hz
      calc ‖Function.uncurry (Work.BoseBoxFock.clampK N f) z‖ = |Work.BoseBoxFock.clampK N f z.1 z.2| := by
              simp only [Function.uncurry, Real.norm_eq_abs]
        _ ≤ |f z.1 z.2| := Work.BoseBoxFock.clampK_abs_le N f z.1 z.2
        _ = |k z.1 z.2| := by rw [hz']
        _ = ‖Function.uncurry k z‖ := by simp only [Function.uncurry, Real.norm_eq_abs]
    have hlim : ∀ᵐ z ∂(ν.prod ν), Tendsto (fun N : ℕ => Function.uncurry (Work.BoseBoxFock.clampK N f) z) atTop (𝓝 (Function.uncurry k z)) := by
      filter_upwards [hfeν] with z hz
      have hz' : f z.1 z.2 = k z.1 z.2 := hz
      have h := Work.BoseBoxFock.clampK_tendsto f z.1 z.2
      rw [hz'] at h
      exact h
    have hprod : Tendsto (fun N : ℕ => ∫ z, Function.uncurry (Work.BoseBoxFock.clampK N f) z ∂(ν.prod ν)) atTop
        (𝓝 (∫ z, Function.uncurry k z ∂(ν.prod ν))) :=
      MeasureTheory.tendsto_integral_of_dominated_convergence (fun z => ‖Function.uncurry k z‖) hASM hkI2.norm hbound hlim
    have hInt_k : ∫ z, Function.uncurry k z ∂(ν.prod ν) = ∫ u in A, ∫ y in A, k u y := by
      rw [MeasureTheory.integral_prod _ hkI2]
      rfl
    have hInt_f : ∀ N, ∫ z, Function.uncurry (Work.BoseBoxFock.clampK N f) z ∂(ν.prod ν) = ∫ u in A, ∫ y in A, Work.BoseBoxFock.clampK N f u y := by
      intro N
      have hintN : Integrable (Function.uncurry (Work.BoseBoxFock.clampK N f)) (ν.prod ν) :=
        Integrable.mono hkI2 (hASM N) (hbound N)
      rw [MeasureTheory.integral_prod _ hintN]
      rfl
    rw [hInt_k] at hprod
    refine Filter.Tendsto.congr' ?_ hprod
    filter_upwards with N
    exact hInt_f N
  -- the vertex row
  have hpoint : ∀ᵐ p ∂(ν.prod ν), Tendsto (fun N : ℕ => Work.BoseBoxFock.clampK N f p.1 p.2) atTop (𝓝 (k p.1 p.2)) := by
    filter_upwards [hfeν] with p hp
    have hp' : f p.1 p.2 = k p.1 p.2 := hp
    have h := Work.BoseBoxFock.clampK_tendsto f p.1 p.2
    rw [hp'] at h
    exact h
  -- assembly on the product measure
  have hmain : ∀ᵐ p ∂(ν.prod ν), P p := by
    rw [MeasureTheory.ae_iff]
    have hB1 : (ν.prod ν) {p : E3 × E3 | ¬ A1 p.1} = 0 := by
      rw [show {p : E3 × E3 | ¬ A1 p.1} = {u : E3 | ¬ A1 u} ×ˢ Set.univ from by ext p; simp]
      rw [Measure.prod_prod, MeasureTheory.ae_iff.mp hrow1, zero_mul]
    have hB2 : (ν.prod ν) {p : E3 × E3 | ¬ A2 p.2} = 0 := by
      rw [show {p : E3 × E3 | ¬ A2 p.2} = Set.univ ×ˢ {y : E3 | ¬ A2 y} from by ext p; simp]
      rw [Measure.prod_prod, MeasureTheory.ae_iff.mp hrow2, mul_zero]
    have hB3 : (ν.prod ν) {p : E3 × E3 | f p.1 p.2 ≠ k p.1 p.2} = 0 := by
      have hthis := MeasureTheory.ae_iff.mp hfeν
      simpa only [Function.uncurry, ne_eq] using hthis
    refine measure_mono_null ?_ (measure_union_null (measure_union_null hB1 hB2) hB3)
    intro p hp
    by_contra hc
    obtain ⟨hA1, hA2, hfk⟩ : A1 p.1 ∧ A2 p.2 ∧ f p.1 p.2 = k p.1 p.2 := by
      simpa only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, ne_eq, and_assoc] using hc
    have hP : P p := by
      show Tendsto (fun N : ℕ => Work.BoseBoxFock.qmqKR ℓ (Work.BoseBoxFock.clampK N f) p.1 p.2) atTop (𝓝 (Work.BoseBoxFock.qmqKR ℓ k p.1 p.2))
      have hT0 : Tendsto (fun N : ℕ => Work.BoseBoxFock.clampK N f p.1 p.2) atTop (𝓝 (k p.1 p.2)) := by
        have h := Work.BoseBoxFock.clampK_tendsto f p.1 p.2
        rw [hfk] at h
        exact h
      have h1 : Tendsto (fun N : ℕ => (ℓ ^ 3)⁻¹ * (∫ y in A, Work.BoseBoxFock.clampK N f p.1 y)) atTop
          (𝓝 ((ℓ ^ 3)⁻¹ * (∫ y in A, k p.1 y))) := hA1.const_mul _
      have h2 : Tendsto (fun N : ℕ => (ℓ ^ 3)⁻¹ * (∫ u in A, Work.BoseBoxFock.clampK N f u p.2)) atTop
          (𝓝 ((ℓ ^ 3)⁻¹ * (∫ u in A, k u p.2))) := hA2.const_mul _
      have h3 : Tendsto (fun N : ℕ => ((ℓ ^ 3)⁻¹) ^ 2 * (∫ u in A, ∫ y in A, Work.BoseBoxFock.clampK N f u y)) atTop
          (𝓝 (((ℓ ^ 3)⁻¹) ^ 2 * (∫ u in A, ∫ y in A, k u y))) := hrow3.const_mul _
      have hcomb := ((hT0.sub h1).sub h2).add h3
      simpa only [Work.BoseBoxFock.qmqKR] using hcomb
    exact hp hP
  -- transfer to the nested a.e. form (`ν ⊗ ν` is swap-invariant)
  have hswap : ∀ᵐ q ∂(ν.prod ν), P q.swap :=
    (Measure.measurePreserving_swap (μ := ν) (ν := ν)).quasiMeasurePreserving.ae hmain
  exact Measure.ae_ae_of_ae_prod hswap

end Work.BoseBoxFock.dictIIAux

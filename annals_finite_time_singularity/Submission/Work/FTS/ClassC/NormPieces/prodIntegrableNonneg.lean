import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.ClassC.NormPieces

theorem prodIntegrableNonneg {f : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hslice : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ : ℝ => f z θ) Work.Spaces.Iθ)
    (hnn : ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ f z θ)
    (hint : MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, f z θ)
      Work.Spaces.Iz) :
    MeasureTheory.Integrable (Function.uncurry f)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
      (∫ p, Function.uncurry f p
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, f z θ := by
  classical
  set S : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) with hSdef
  have hS_open : IsOpen S := isOpen_Ioi.prod isOpen_Ioo
  have hS_meas : MeasurableSet S := hS_open.measurableSet
  -- `S` is contained in `Iz ×ˢ Iθ`
  have hS_sub : S ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
    rintro ⟨z, θ⟩ hz
    simp only [Set.mem_prod, Work.Spaces.Iz, Work.Spaces.Iθ, Set.mem_Ici, Set.mem_Icc,
      Set.mem_Ioi, Set.mem_Ioo, hSdef] at hz ⊢
    exact ⟨le_of_lt hz.1, le_of_lt hz.2.1, le_of_lt hz.2.2⟩
  -- the complement of `S` inside `Iz ×ˢ Iθ` is a null set
  have hdiff_null : (Measure.prod volume volume)
      ((Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) \ S) = 0 := by
    have hA : (Measure.prod volume volume)
        (({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)) = 0 := by
      rw [Measure.prod_prod]; simp
    have hB : (Measure.prod volume volume)
        ((Set.univ : Set ℝ) ×ˢ ({0, Real.pi / 2} : Set ℝ)) = 0 := by
      rw [Measure.prod_prod]
      have h2 : volume ({0, Real.pi / 2} : Set ℝ) = 0 :=
        Set.Finite.measure_zero ((Set.finite_singleton (Real.pi / 2)).insert 0) volume
      rw [h2, mul_zero]
    refine measure_mono_null (fun p hp => ?_) (measure_union_null hA hB)
    obtain ⟨z, θ⟩ := p
    rw [Set.mem_sdiff] at hp
    obtain ⟨hpin, hpnot⟩ := hp
    have hzin := hpin.1
    have hθin := hpin.2
    simp only [Work.Spaces.Iz, Work.Spaces.Iθ, Set.mem_Ici, Set.mem_Icc] at hzin hθin
    rw [hSdef] at hpnot
    simp only [Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at hpnot
    simp only [Set.mem_union, Set.mem_prod, Set.mem_singleton_iff, Set.mem_insert_iff,
      Set.mem_univ, true_and, and_true]
    have hz0 : 0 ≤ z := hzin
    have hθ0 : 0 ≤ θ := hθin.1
    have hθpi : θ ≤ Real.pi / 2 := hθin.2
    have hnot : ¬ (0 < z ∧ 0 < θ ∧ θ < Real.pi / 2) := hpnot
    rcases lt_or_ge 0 z with hz | hz
    · right
      have h2 : ¬ (0 < θ ∧ θ < Real.pi / 2) := fun hc => hnot ⟨hz, hc.1, hc.2⟩
      rcases eq_or_lt_of_le hθ0 with h | h
      · left; exact h.symm
      · right
        exact le_antisymm hθpi (not_lt.mp (fun hlt => h2 ⟨h, hlt⟩))
    · left; exact le_antisymm hz hz0
  have hae_set : Work.Spaces.Iz ×ˢ Work.Spaces.Iθ
      =ᵐ[Measure.prod volume volume] S := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨hdiff_null, ?_⟩
    rw [show S \ (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) = ∅ from by
      rw [Set.sdiff_eq_empty]; exact hS_sub]
    exact measure_empty
  -- rewrite the product measure as the restriction to `S`
  have hμν : (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)
      = (Measure.prod volume volume).restrict S := by
    rw [Measure.prod_restrict Work.Spaces.Iz Work.Spaces.Iθ]
    exact Measure.restrict_congr_set hae_set
  have hsm : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [hμν]
    exact hcont.aestronglyMeasurable hS_meas
  -- almost every `z ∈ Iz` is positive
  have hIzeq : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) := by
    rw [MeasureTheory.ae_eq_set]
    refine ⟨?_, ?_⟩
    · refine measure_mono_null (fun z hz => ?_) (measure_singleton 0)
      simp only [Set.mem_sdiff, Work.Spaces.Iz, Set.mem_Ici, Set.mem_Ioi,
        Set.mem_singleton_iff] at hz ⊢
      exact le_antisymm (not_lt.mp hz.2) hz.1
    · rw [show Set.Ioi (0 : ℝ) \ Work.Spaces.Iz = ∅ from by
        rw [Set.sdiff_eq_empty]
        intro z hz
        simpa [Work.Spaces.Iz] using le_of_lt hz]
      exact measure_empty
  have hpos : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz), 0 < z := by
    rw [Measure.restrict_congr_set hIzeq]
    exact ae_restrict_mem (μ := volume) (s := Set.Ioi (0 : ℝ)) isOpen_Ioi.measurableSet
  have hslice_ae : ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      Integrable (fun θ : ℝ => f z θ) (volume.restrict Work.Spaces.Iθ) :=
    hpos.mono (fun z hz => hslice z hz)
  -- the norm-integral coincides a.e. with the given iterated integral
  have hae_norm : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, f z θ)
      =ᵐ[volume.restrict Work.Spaces.Iz]
      (fun z : ℝ => ∫ θ, ‖f z θ‖ ∂(volume.restrict Work.Spaces.Iθ)) := by
    filter_upwards [hpos] with z hz
    have h1 : (fun θ : ℝ => ‖f z θ‖)
        =ᵐ[volume.restrict Work.Spaces.Iθ] (fun θ : ℝ => f z θ) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
      exact Real.norm_of_nonneg (hnn z θ hz hθ)
    exact (integral_congr_ae h1).symm
  have hint_norm : Integrable
      (fun z : ℝ => ∫ θ, ‖f z θ‖ ∂(volume.restrict Work.Spaces.Iθ))
      (volume.restrict Work.Spaces.Iz) :=
    hint.congr hae_norm
  have hfint : Integrable (Function.uncurry f)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (integrable_prod_iff hsm).mpr ⟨hslice_ae, hint_norm⟩
  refine ⟨hfint, ?_⟩
  exact (MeasureTheory.integral_integral (f := fun z θ => f z θ) hfint).symm

end Work.FTS.ClassC.NormPieces

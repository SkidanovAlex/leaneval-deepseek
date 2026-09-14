import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Commons.Analysis.Measure.tendsto_iSup_closedBall_nhds_zero
import Submission.Commons.Analysis.Convolution.aemeasurable_uncurry_ofReal_mul_enorm_sq
import Submission.Commons.Analysis.Convolution.enorm_convolution_sub_le

namespace Commons.Analysis.Convolution

open MeasureTheory Filter
open scoped Topology ENNReal

/-- `ENNReal.ofReal` of a squared norm is the squared `enorm`. -/
lemma ofReal_norm_sq_eq (z : ℂ) : ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ (2 : ℝ) := by
  rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg z) 2, ofReal_norm]

section Helpers

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The `ℝ≥0∞`-integral of a nonnegative probability density is `1`. -/
lemma lintegral_ofReal_eq_one {ρ : E → ℝ} (hρnn : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ volume)
    (hρ1 : ∫ x, ρ x ∂volume = 1) : ∫⁻ x, ENNReal.ofReal (ρ x) ∂volume = 1 := by
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall hρnn), hρ1]
  simp

/-- **Translation is continuous in `L²`.**  For `u ∈ L²(ℝⁿ)`, the `L²`-mass of the difference
`x ↦ u (x - y) - u x` tends to `0` as `y → 0`. -/
theorem tendsto_lintegral_translate_sub (u : E → ℂ)
    (hu : MemLp u 2 (volume : Measure E)) :
    Tendsto (fun y : E => ∫⁻ x, ‖u (x - y) - u x‖ₑ ^ (2:ℝ) ∂volume) (𝓝 0) (𝓝 0) := by
  classical
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have hcont : Continuous fun y : E => DomAddAct.mk (-y) +ᵥ ((hu.toLp u) : Lp ℂ 2 (volume : Measure E)) := by
    fun_prop
  have hsubmp : ∀ y : E, Measure.QuasiMeasurePreserving (fun x : E => -y +ᵥ x) volume volume :=
    fun y => (measurePreserving_vadd (-y) volume).quasiMeasurePreserving
  have hFae : ∀ y : E, (↑↑(DomAddAct.mk (-y) +ᵥ ((hu.toLp u) : Lp ℂ 2 (volume : Measure E))) : E → ℂ) =ᵐ[volume] fun x => u (x - y) := by
    intro y
    have h1 := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-y)) ((hu.toLp u) : Lp ℂ 2 (volume : Measure E))
    have h2 := (hsubmp y).ae_eq_comp hu.coeFn_toLp
    filter_upwards [h1, h2] with x hx1 hx2
    simp only [Equiv.symm_apply_apply, vadd_eq_add, Function.comp_apply] at hx1 hx2 ⊢
    rw [hx1, hx2]
    congr 1
    abel
  have hdist : Tendsto (fun y : E => dist (DomAddAct.mk (-y) +ᵥ ((hu.toLp u) : Lp ℂ 2 (volume : Measure E))) ((hu.toLp u) : Lp ℂ 2 (volume : Measure E))) (𝓝 0) (𝓝 0) := by
    have hconst : Continuous fun _ : E => ((hu.toLp u) : Lp ℂ 2 (volume : Measure E)) := continuous_const
    have hcd : Continuous fun y : E => dist (DomAddAct.mk (-y) +ᵥ ((hu.toLp u) : Lp ℂ 2 (volume : Measure E))) ((hu.toLp u) : Lp ℂ 2 (volume : Measure E)) :=
      hcont.dist hconst
    have h := hcd.tendsto (0 : E)
    simpa using h
  have hkey : ∀ y : E, dist (DomAddAct.mk (-y) +ᵥ ((hu.toLp u) : Lp ℂ 2 (volume : Measure E))) ((hu.toLp u) : Lp ℂ 2 (volume : Measure E))
      = (eLpNorm (fun x => u (x - y) - u x) 2 volume).toReal := by
    intro y
    rw [Lp.dist_eq_eLpNorm_neg_add]
    congr 1
    have hae : (-(↑↑(DomAddAct.mk (-y) +ᵥ ((hu.toLp u) : Lp ℂ 2 (volume : Measure E)))) + ↑↑((hu.toLp u) : Lp ℂ 2 (volume : Measure E)) : E → ℂ)
        =ᵐ[volume] -(fun x : E => u (x - y) - u x) := by
      filter_upwards [hFae y, hu.coeFn_toLp] with x h3 h4
      simp only [Pi.add_apply, Pi.neg_apply]
      rw [h3, h4]
      ring
    rw [eLpNorm_congr_ae hae, eLpNorm_neg]
  have hG : Tendsto (fun y : E => (eLpNorm (fun x => u (x - y) - u x) 2 volume).toReal) (𝓝 0) (𝓝 0) := by
    rw [show (fun y : E => (eLpNorm (fun x => u (x - y) - u x) 2 volume).toReal)
        = (fun y : E => dist (DomAddAct.mk (-y) +ᵥ ((hu.toLp u) : Lp ℂ 2 (volume : Measure E))) ((hu.toLp u) : Lp ℂ 2 (volume : Measure E))) from
          funext fun y => (hkey y).symm]
    exact hdist
  have hfin : ∀ y : E, eLpNorm (fun x => u (x - y) - u x) 2 volume ≠ ⊤ := by
    intro y
    have h1 : MemLp (fun x : E => u (x - y)) 2 (volume : Measure E) :=
      hu.comp_measurePreserving (measurePreserving_sub_right volume y)
    exact (h1.sub hu).eLpNorm_ne_top
  have hE : Tendsto (fun y : E => eLpNorm (fun x => u (x - y) - u x) 2 volume) (𝓝 0) (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    rcases eq_or_ne ε ⊤ with h | h
    · exact Eventually.of_forall fun y => h ▸ le_top
    · have hpos : 0 < ε.toReal := ENNReal.toReal_pos (ne_of_gt hε) h
      filter_upwards [hG.eventually (isOpen_Iio.mem_nhds (by simpa using hpos))] with y hy
      rw [← ENNReal.ofReal_toReal (hfin y), ← ENNReal.ofReal_toReal h,
        ENNReal.ofReal_le_ofReal_iff hpos.le]
      exact le_of_lt hy
  rw [ENNReal.tendsto_nhds_zero] at hE ⊢
  intro ε hε
  have hmin : (0:ℝ≥0∞) < min ε 1 := lt_min hε one_pos
  filter_upwards [hE (min ε 1) hmin] with y hy
  have hsplit : (∫⁻ x, ‖u (x - y) - u x‖ₑ ^ (2:ℝ) ∂volume)
      = (eLpNorm (fun x => u (x - y) - u x) 2 volume) ^ (2:ℝ) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num)]
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hsplit]
  calc (eLpNorm (fun x => u (x - y) - u x) 2 volume) ^ (2:ℝ)
      ≤ (min ε 1) ^ (2:ℝ) := ENNReal.rpow_le_rpow hy (by norm_num)
    _ ≤ min ε 1 := by
        rw [ENNReal.rpow_two]
        calc (min ε 1) ^ 2 = (min ε 1) * (min ε 1) := pow_two _
          _ ≤ 1 * (min ε 1) := by gcongr; exact min_le_right _ _
          _ = min ε 1 := one_mul _
    _ ≤ ε := min_le_left _ _


end Helpers


/-- **Mollification converges in `L²`.**  If `ρ i` is a family of nonnegative approximate
identities on `ℝⁿ` (`∫ ρ i = 1`) whose supports shrink to `{0}` (`ρ i x = 0` whenever
`R i < ‖x‖`, with `R i → 0`), then convolving with `ρ i` converges to the identity in `L²`. -/
theorem tendsto_lintegral_convolution_sub_sq {n : ℕ} {ι : Type*} {l : Filter ι}
    (ρ : ι → EuclideanSpace ℝ (Fin n) → ℝ) (hρnn : ∀ i x, 0 ≤ ρ i x)
    (hρi : ∀ i, Integrable (ρ i) volume) (hρ1 : ∀ i, ∫ x, ρ i x ∂volume = 1)
    (R : ι → ℝ) (hRpos : ∀ i, 0 ≤ R i) (hR : Tendsto R l (𝓝 0))
    (hRs : ∀ i, ∀ x, R i < ‖x‖ → ρ i x = 0)
    (u : EuclideanSpace ℝ (Fin n) → ℂ) (hu : MemLp u 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Tendsto (fun i => ∫⁻ x, ENNReal.ofReal
        (‖(∫ y, ρ i y • u (x - y) ∂volume) - u x‖ ^ 2) ∂volume) l (𝓝 0) := by
  let G : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun y => ∫⁻ x, ‖u (x - y) - u x‖ₑ ^ (2:ℝ) ∂volume
  have hGtend : Tendsto G (𝓝 0) (𝓝 0) := tendsto_lintegral_translate_sub u hu
  have hS : Tendsto (fun i => ⨆ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R i), G y)
      l (𝓝 0) :=
    Commons.Analysis.Measure.tendsto_iSup_closedBall_nhds_zero hGtend R hR
  have hbound : ∀ i, (∫⁻ x, ENNReal.ofReal
        (‖(∫ y, ρ i y • u (x - y) ∂volume) - u x‖ ^ 2) ∂volume)
      ≤ ⨆ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R i), G y := by
    intro i
    calc (∫⁻ x, ENNReal.ofReal (‖(∫ y, ρ i y • u (x - y) ∂volume) - u x‖ ^ 2) ∂volume)
        = ∫⁻ x, ‖(∫ y, ρ i y • u (x - y) ∂volume) - u x‖ₑ ^ (2:ℝ) ∂volume :=
          lintegral_congr fun x => ofReal_norm_sq_eq _
      _ ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ρ i y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ) ∂volume ∂volume := by
          apply lintegral_mono_ae
          filter_upwards [enorm_convolution_sub_le (hρnn i) (hρi i) (hρ1 i) u hu] with x hx
          simpa only [ENNReal.rpow_two] using hx
      _ = ∫⁻ y, ENNReal.ofReal (ρ i y) * G y ∂volume := by
          rw [MeasureTheory.lintegral_lintegral_swap
            (f := fun x y => ENNReal.ofReal (ρ i y) * ‖u (x - y) - u x‖ₑ ^ (2:ℝ))
            (by
              have h := aemeasurable_uncurry_ofReal_mul_enorm_sq (hρi i) u hu
              simpa only [ENNReal.rpow_two] using h)]
          apply lintegral_congr; intro y
          rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ (∫⁻ y, ENNReal.ofReal (ρ i y) ∂volume) *
            (⨆ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R i), G y) := by
          by_cases hStop : (⨆ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R i), G y) = ⊤
          · rw [hStop, lintegral_ofReal_eq_one (hρnn i) (hρi i) (hρ1 i), one_mul]
            exact le_top
          · rw [← MeasureTheory.lintegral_mul_const' _ _ hStop]
            apply lintegral_mono; intro y
            by_cases h : ρ i y = 0
            · simp [h]
            · have hy : y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R i) := by
                by_contra hcon
                refine h (hRs i y ?_)
                have hle : ¬ dist y 0 ≤ R i := fun hc => hcon (Metric.mem_closedBall.mpr hc)
                have := not_le.mp hle
                simpa [dist_eq_norm] using this
              have hle : G y ≤ ⨆ z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R i), G z :=
                le_iSup₂_of_le y hy le_rfl
              exact mul_le_mul_right hle (ENNReal.ofReal (ρ i y))
      _ = ⨆ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) (R i), G y := by
          rw [lintegral_ofReal_eq_one (hρnn i) (hρi i) (hρ1 i), one_mul]
  rw [ENNReal.tendsto_nhds_zero] at hS ⊢
  intro ε hε
  filter_upwards [hS ε hε] with i hi
  exact le_trans (hbound i) hi

end Commons.Analysis.Convolution
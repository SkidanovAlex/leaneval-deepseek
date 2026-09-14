import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable

namespace Commons.Analysis.Convolution

open MeasureTheory Filter
open scoped Topology ENNReal

/-- `ENNReal.ofReal` of a squared norm is the squared `enorm`. -/
lemma ofReal_norm_sq_eq_enorm {F : Type*} [SeminormedAddCommGroup F] (z : F) :
    ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ (2 : ℝ) := by
  rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg z) 2, ofReal_norm]

section General

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F]

local notation "X" => EuclideanSpace ℝ (Fin n)

/-- **Translation is continuous in `L²`.**  For `u ∈ L²(ℝⁿ, F)` (with `F` a normed
additive group), the `L²`-mass of the difference `x ↦ u (x - y) - u x` tends to `0` as
`y → 0`. -/
theorem tendsto_lintegral_translate_sub_vec_general
    (u : X → F) (hu : MemLp u 2 (volume : Measure X)) :
    Tendsto (fun y : X => ∫⁻ x, ENNReal.ofReal (‖u (x - y) - u x‖ ^ 2)
        ∂(volume : Measure X)) (𝓝 0) (𝓝 0) := by
  classical
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let g : Lp F 2 (volume : Measure X) := hu.toLp u
  have hcongr : (fun y : X => ∫⁻ x, ENNReal.ofReal (‖u (x - y) - u x‖ ^ 2) ∂(volume : Measure X))
      = (fun y : X => ∫⁻ x, ‖u (x - y) - u x‖ₑ ^ (2 : ℝ) ∂(volume : Measure X)) := by
    funext y; exact lintegral_congr (fun x => ofReal_norm_sq_eq_enorm _)
  rw [hcongr]
  have hcont : Continuous fun y : X => DomAddAct.mk (-y) +ᵥ g := by
    fun_prop
  have hsubmp : ∀ y : X, Measure.QuasiMeasurePreserving (fun x : X => -y +ᵥ x)
      (volume : Measure X) (volume : Measure X) :=
    fun y => (measurePreserving_vadd (-y) volume).quasiMeasurePreserving
  have hFae : ∀ y : X, (↑↑(DomAddAct.mk (-y) +ᵥ g) : X → F) =ᵐ[volume] fun x => u (x - y) := by
    intro y
    have h1 := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-y)) g
    have h2 := (hsubmp y).ae_eq_comp hu.coeFn_toLp
    filter_upwards [h1, h2] with x hx1 hx2
    simp only [Equiv.symm_apply_apply, vadd_eq_add, Function.comp_apply] at hx1 hx2 ⊢
    rw [hx1, hx2]
    congr 1
    abel
  have hdist : Tendsto (fun y : X => dist (DomAddAct.mk (-y) +ᵥ g) g) (𝓝 0) (𝓝 0) := by
    have hcd : Continuous fun y : X => dist (DomAddAct.mk (-y) +ᵥ g) g :=
      hcont.dist continuous_const
    have h := hcd.tendsto (0 : X)
    simpa using h
  have hkey : ∀ y : X, dist (DomAddAct.mk (-y) +ᵥ g) g
      = (eLpNorm (fun x => u (x - y) - u x) 2 (volume : Measure X)).toReal := by
    intro y
    rw [Lp.dist_eq_eLpNorm_neg_add]
    congr 1
    have hae : (-(↑↑(DomAddAct.mk (-y) +ᵥ g)) + ↑↑g : X → F)
        =ᵐ[volume] -(fun x : X => u (x - y) - u x) := by
      filter_upwards [hFae y, hu.coeFn_toLp] with x h3 h4
      simp only [Pi.add_apply, Pi.neg_apply]
      rw [h3, h4]
      abel
    rw [eLpNorm_congr_ae hae, eLpNorm_neg]
  have hG : Tendsto (fun y : X =>
      (eLpNorm (fun x => u (x - y) - u x) 2 (volume : Measure X)).toReal) (𝓝 0) (𝓝 0) := by
    rw [show (fun y : X => (eLpNorm (fun x => u (x - y) - u x) 2 (volume : Measure X)).toReal)
        = (fun y : X => dist (DomAddAct.mk (-y) +ᵥ g) g)
        from funext fun y => (hkey y).symm]
    exact hdist
  have hfin : ∀ y : X, eLpNorm (fun x => u (x - y) - u x) 2 (volume : Measure X) ≠ ⊤ := by
    intro y
    have h1 : MemLp (fun x : X => u (x - y)) 2 (volume : Measure X) :=
      hu.comp_measurePreserving (measurePreserving_sub_right volume y)
    exact (h1.sub hu).eLpNorm_ne_top
  have hE : Tendsto (fun y : X => eLpNorm (fun x => u (x - y) - u x) 2 (volume : Measure X))
      (𝓝 0) (𝓝 0) := by
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
  have hmin : (0 : ℝ≥0∞) < min ε 1 := lt_min hε one_pos
  filter_upwards [hE (min ε 1) hmin] with y hy
  have hsplit : (∫⁻ x, ‖u (x - y) - u x‖ₑ ^ (2 : ℝ) ∂(volume : Measure X))
      = (eLpNorm (fun x => u (x - y) - u x) 2 (volume : Measure X)) ^ (2 : ℝ) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num) (by norm_num)]
    rw [← ENNReal.rpow_mul]
    norm_num
  rw [hsplit]
  calc (eLpNorm (fun x => u (x - y) - u x) 2 (volume : Measure X)) ^ (2 : ℝ)
      ≤ (min ε 1) ^ (2 : ℝ) := ENNReal.rpow_le_rpow hy (by norm_num)
    _ ≤ min ε 1 := by
        rw [ENNReal.rpow_two]
        calc (min ε 1) ^ 2 = (min ε 1) * (min ε 1) := pow_two _
          _ ≤ 1 * (min ε 1) := by gcongr; exact min_le_right _ _
          _ = min ε 1 := one_mul _
    _ ≤ ε := min_le_left _ _

end General

theorem tendsto_lintegral_translate_sub_vec {n m : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hu : MeasureTheory.MemLp u 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))) :
    Filter.Tendsto (fun y : EuclideanSpace ℝ (Fin n) =>
      ∫⁻ x, ENNReal.ofReal (‖u (x - y) - u x‖ ^ 2)
        ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))))
      (nhds 0) (nhds 0) :=
  tendsto_lintegral_translate_sub_vec_general u hu

end Commons.Analysis.Convolution

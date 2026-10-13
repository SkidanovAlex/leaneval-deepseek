import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.ClassCHon.CmpSupp.hkSq_le_of_lintegral
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.Honesty.psiTrunc_tendsto_psiSeries

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RouteB

/-- The unweighted square of `Y` on the open quadrant is dominated by `HkSq α 0 Y`: on
`Q0 = Ioi 0 ×ˢ Ioo 0 (π/2)` the level-`0` integrand is `(Y · w z / sin(2θ)^{η/2})²` and the factor
`w z / sin(2θ)^{η/2} ≥ 1` there.  Suggested route: `lintegral_mono` pointwise, then
`lintegral_mono_set` for `Q0 ⊆ Iz ×ˢ Iθ`, then Tonelli (`MeasureTheory.lintegral_prod`, using the
joint a.e.-measurability hypothesis) and
`Work.FTS.ClassCHon.CmpSupp.lintegral_HkIntegrand_eq` together with
`Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici` (the point `z = 0` contributes `0`). -/
theorem lintegral_sq_le_HkSq_zero {α : ℝ} {Y : ℝ → ℝ → ℝ} (hm : Work.Spaces.HkMem α 0 Y)
    (hmeas : AEMeasurable (Function.uncurry Y)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    (∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal ((Y p.1 p.2) ^ 2))
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α 0 Y) := by
  -- The level-`0` integrand is a single square, namely `(Y · w z / sin(2θ)^{η/2})²`.
  have hK : ∀ z θ : ℝ, Work.Spaces.HkIntegrand α 0 Y z θ
      = (Y z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
    fun z θ => by simp [Work.Spaces.HkIntegrand]
  -- The angular weight `w z / sin(2θ)^{η/2}` is (everywhere) measurable, and `hmeas` gives the
  -- a.e. measurability of `Y`; hence the level-`0` integrand is a.e. measurable for
  -- `(volume.restrict Iz).prod (volume.restrict Iθ)`, as Tonelli requires.
  have hw : Measurable (fun p : ℝ × ℝ => Work.Spaces.w p.1) := by
    have h : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
        = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by funext p; rfl
    rw [h]
    exact ((measurable_const.add measurable_fst).pow measurable_const).div
      (measurable_fst.pow measurable_const)
  have hs : Measurable (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) :=
    ((Real.continuous_rpow_const (by norm_num [Work.Spaces.eta])).measurable).comp
      ((Real.continuous_sin.measurable).comp (measurable_snd.const_mul 2))
  have hc : Measurable (fun p : ℝ × ℝ =>
      Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) :=
    hw.div hs
  have hmeas_int : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Y p.1 p.2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    have hY : AEMeasurable (fun p : ℝ × ℝ => Y p.1 p.2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hmeas
    have hfun : (fun p : ℝ × ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Y p.1 p.2))
        = fun p : ℝ × ℝ => ENNReal.ofReal ((Y p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
      funext p; rw [hK]
    rw [hfun]
    exact ((hY.mul hc.aemeasurable).pow measurable_const.aemeasurable).ennreal_ofReal
  -- `Q0` sits inside `Iz ×ˢ Iθ`.
  have hQ0sub : Work.FTS.EllipticEst.Q0 ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    exact Set.mem_prod.mpr ⟨le_of_lt hz, Set.mem_Icc.mpr ⟨le_of_lt hθ0, le_of_lt hθ1⟩⟩
  -- Pointwise on the open quadrant the weight factor is `≥ 1`, hence the plain square is the
  -- smaller one.
  have hpt : ∀ p ∈ Work.FTS.EllipticEst.Q0,
      (Y p.1 p.2) ^ 2 ≤ Work.Spaces.HkIntegrand α 0 Y p.1 p.2 := by
    intro p hp
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    rw [hK p.1 p.2]
    have hsin_pos : 0 < Real.sin (2 * p.2) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
    have hsin_le : Real.sin (2 * p.2) ≤ 1 := Real.sin_le_one _
    have hrpow_pos : 0 < (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) :=
      Real.rpow_pos_of_pos hsin_pos _
    have hrpow_le : (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) ≤ 1 :=
      Real.rpow_le_one (le_of_lt hsin_pos) hsin_le (by norm_num [Work.Spaces.eta])
    have hw1 : 1 ≤ Work.Spaces.w p.1 := by
      rw [Work.Spaces.w]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < p.1 ^ 2)]
      nlinarith [hz]
    have hc1 : 1 ≤ Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) := by
      rw [le_div_iff₀ hrpow_pos]
      linarith
    have hcsq : 1 ≤ (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
      nlinarith
    calc (Y p.1 p.2) ^ 2
        = (Y p.1 p.2) ^ 2 * 1 := by ring
      _ ≤ (Y p.1 p.2) ^ 2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hcsq (sq_nonneg _)
      _ = (Y p.1 p.2
            * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          ring
  -- `Ioi 0` and `Iz = Ici 0` differ by the null set `{0}`.
  have hIoi_eq_Iz : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici
  -- The product measure on `Iz ×ˢ Iθ` is the product of the two restricted measures.
  have hprod : MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.Measure.prod_restrict (μ := MeasureTheory.volume) (ν := MeasureTheory.volume)
      Work.Spaces.Iz Work.Spaces.Iθ).symm
  -- Identification of the real-valued iterated integral with `HkSq`.
  have hSq : (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 Y z θ)
      = Work.Spaces.HkSq α 0 Y := by
    change _ = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 Y z θ)
    rw [← hIoi_eq_Iz]
  calc (∫⁻ p in Work.FTS.EllipticEst.Q0, ENNReal.ofReal ((Y p.1 p.2) ^ 2))
      ≤ ∫⁻ p in Work.FTS.EllipticEst.Q0,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Y p.1 p.2) := by
        refine lintegral_mono_ae ?_
        rw [ae_restrict_iff' Work.FTS.EllipticEst.isOpen_Q0.measurableSet]
        exact Eventually.of_forall fun p hp => ENNReal.ofReal_le_ofReal (hpt p hp)
    _ ≤ ∫⁻ p in Work.Spaces.Iz ×ˢ Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Y p.1 p.2) :=
        lintegral_mono_set hQ0sub
    _ = ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Y p.1 p.2)
          ∂((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
        rw [hprod]
    _ = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Y z θ) :=
        MeasureTheory.lintegral_prod _ hmeas_int
    _ = ∫⁻ z in Set.Ioi (0 : ℝ), ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α 0 Y z θ) := by
        rw [← hIoi_eq_Iz]
    _ = ENNReal.ofReal (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 Y z θ) :=
        Work.FTS.ClassCHon.CmpSupp.lintegral_HkIntegrand_eq (k := 0) hm
    _ = ENNReal.ofReal (Work.Spaces.HkSq α 0 Y) := by rw [hSq]

end Work.FTS.PhiStar.RouteB

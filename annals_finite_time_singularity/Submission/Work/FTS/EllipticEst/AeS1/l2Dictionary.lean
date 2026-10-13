import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.ProductTools
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.HkSq_eq_lintegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeS1

/-- **The `L²`-dictionary**: for a function `f` whose weighted square `(f · w)²` is
a.e.-strongly-measurable for the product measure on `Iz × Iθ`, whose every angular fibre
`θ ↦ (f z θ · w z)²` is integrable on `Iθ`, and whose `∫⁻`-integral
`∫⁻_z ofReal(w z²) · (∫⁻_θ ofReal(f z θ²))` is finite, the iterated Bochner integral
`L2Sq (f · w)` is honest (`L2Mem`) and equals the `toReal` of that `∫⁻`-integral. -/
theorem l2Dictionary {f : ℝ → ℝ → ℝ}
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (f p.1 p.2 * Work.Spaces.w p.1) ^ 2)
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hsl : ∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
      (fun θ => (f z θ * Work.Spaces.w z) ^ 2) Work.Spaces.Iθ)
    (hfin : (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f z θ) ^ 2))) ≠ ⊤) :
    Work.Spaces.L2Mem (fun z θ => f z θ * Work.Spaces.w z) ∧
    Work.Spaces.L2Sq (fun z θ => f z θ * Work.Spaces.w z)
      = (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
        * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f z θ) ^ 2))).toReal := by
  -- ## the a.e. pointwise identity
  have hpt : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2)
        = ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
            * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f z θ) ^ 2)) := by
    rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
    have hne : ∀ᵐ z ∂(MeasureTheory.volume : Measure ℝ), z ≠ 0 := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hne] with z hz hzI
    have hzpos : 0 < z := lt_of_le_of_ne hzI (Ne.symm hz)
    have hwz : Work.Spaces.w z ≠ 0 := by rw [Work.Spaces.w]; positivity
    have hint : MeasureTheory.Integrable (fun θ => (f z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have h1 : MeasureTheory.Integrable (fun θ => (f z θ * Work.Spaces.w z) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hsl z hzI
      refine (h1.div_const ((Work.Spaces.w z) ^ 2)).congr ?_
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ _ => ?_)
      field_simp
    have hval : (∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2)
        = (Work.Spaces.w z) ^ 2 * ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 := by
      rw [show (∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2)
            = ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * (Work.Spaces.w z) ^ 2 from
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => by ring)]
      rw [MeasureTheory.integral_mul_const]
      ring
    rw [hval, ENNReal.ofReal_mul (sq_nonneg (Work.Spaces.w z))]
    congr 1
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun θ => sq_nonneg _)
  -- ## the lintegral identity
  have hLint : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2))
      = ∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f z θ) ^ 2)) :=
    MeasureTheory.lintegral_congr_ae hpt
  have hΦne : (∫⁻ z in Work.Spaces.Iz,
        ENNReal.ofReal (∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2)) ≠ ⊤ := by
    rw [hLint]; exact hfin
  -- ## measurability of the outer integrand
  have hmsl : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have h' := hmeas.integral_prod_right'
    simpa using h'
  -- ## the two conclusions
  have hIntOuter : MeasureTheory.IntegrableOn
      (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ * Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmsl
      (Filter.Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _)).mp hΦne
  have hL2 : Work.Spaces.L2Sq (fun z θ => f z θ * Work.Spaces.w z)
      = (∫⁻ z in Work.Spaces.Iz, ENNReal.ofReal ((Work.Spaces.w z) ^ 2)
          * (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal ((f z θ) ^ 2))).toReal := by
    rw [Work.Spaces.L2Sq, ← hLint]
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _) hmsl
  exact ⟨⟨hsl, hIntOuter⟩, hL2⟩

end Work.FTS.EllipticEst.AeS1

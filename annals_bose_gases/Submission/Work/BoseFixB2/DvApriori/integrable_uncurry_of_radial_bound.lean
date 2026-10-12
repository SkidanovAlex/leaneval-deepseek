import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.swap_p_abox_tBamp
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB2.DvApriori

open MeasureTheory

/-- Integrability of an uncurried kernel `H : E → β → ℝ` which is dominated, for almost every
`x`, by the radial function `p ↦ C / (1 + ‖p‖)^4`.

The proof is Tonelli's theorem: `(1 + ‖p‖)^{-4}` is integrable on `E` as soon as
`dim E < 4` (`finite_integral_one_add_norm`), and the second factor carries finite mass. -/
theorem integrable_uncurry_of_radial_bound_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] [SFinite μ]
    {β : Type*} [MeasurableSpace β] {ν : Measure β} [SFinite ν] (hνfin : ν Set.univ ≠ ⊤)
    {H : E → β → ℝ} (hH : AEStronglyMeasurable (Function.uncurry H) (μ.prod ν))
    {C : ℝ} (hC : 0 ≤ C) (hdim : (Module.finrank ℝ E : ℝ) < 4)
    (hbd : ∀ᵐ x ∂ν, ∀ p : E, ‖H p x‖ ≤ C / (1 + ‖p‖) ^ 4) :
    Integrable (Function.uncurry H) (μ.prod ν) := by
  classical
  -- rewrite the bound with a real power
  have hrpow : ∀ p : E, C / (1 + ‖p‖) ^ 4 = C * (1 + ‖p‖) ^ (-(4 : ℝ)) := by
    intro p
    rw [Real.rpow_neg (show (0 : ℝ) ≤ 1 + ‖p‖ by positivity),
      show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_eq_mul_inv]
  have hbd' : ∀ᵐ x ∂ν, ∀ p : E, ‖H p x‖ ≤ C * (1 + ‖p‖) ^ (-(4 : ℝ)) := by
    filter_upwards [hbd] with x hx
    intro p
    rw [← hrpow p]
    exact hx p
  -- the radial majorant is integrable
  let K : ENNReal := ∫⁻ p : E, ENNReal.ofReal ((1 + ‖p‖) ^ (-(4 : ℝ))) ∂μ
  have hKfin : K < ⊤ := by
    show (∫⁻ p : E, ENNReal.ofReal ((1 + ‖p‖) ^ (-(4 : ℝ))) ∂μ) < ⊤
    exact finite_integral_one_add_norm (r := 4) hdim
  -- the inner (in `p`) integral is bounded, for almost every `x`
  have hinner : ∀ᵐ x ∂ν, ∫⁻ p, ‖H p x‖ₑ ∂μ ≤ ENNReal.ofReal C * K := by
    filter_upwards [hbd'] with x hx
    have hpoint : ∀ p : E, ‖H p x‖ₑ ≤ ENNReal.ofReal (C * (1 + ‖p‖) ^ (-(4 : ℝ))) := by
      intro p
      rw [Real.enorm_eq_ofReal_abs]
      apply ENNReal.ofReal_le_ofReal
      rw [← Real.norm_eq_abs]
      exact hx p
    calc ∫⁻ p, ‖H p x‖ₑ ∂μ
        ≤ ∫⁻ p, ENNReal.ofReal (C * (1 + ‖p‖) ^ (-(4 : ℝ))) ∂μ := lintegral_mono hpoint
      _ = ∫⁻ p, ENNReal.ofReal C * ENNReal.ofReal ((1 + ‖p‖) ^ (-(4 : ℝ))) ∂μ := by
          apply lintegral_congr
          intro p
          exact ENNReal.ofReal_mul hC
      _ = ENNReal.ofReal C * K :=
          lintegral_const_mul' (ENNReal.ofReal C)
            (fun p : E => ENNReal.ofReal ((1 + ‖p‖) ^ (-(4 : ℝ)))) ENNReal.ofReal_ne_top
  -- measurability of the swapped integrand
  have hf : AEMeasurable (fun z : β × E => ‖Function.uncurry H z.swap‖ₑ) (ν.prod μ) :=
    hH.prod_swap.enorm
  have hfin : HasFiniteIntegral (Function.uncurry H) (μ.prod ν) := by
    rw [hasFiniteIntegral_iff_enorm]
    -- Tonelli, in the order `x` then `p`
    have hswap : (∫⁻ z : E × β, ‖Function.uncurry H z‖ₑ ∂μ.prod ν)
        = ∫⁻ z : β × E, ‖Function.uncurry H z.swap‖ₑ ∂ν.prod μ :=
      (lintegral_prod_swap (μ := μ) (ν := ν)
        (f := fun z : E × β => ‖Function.uncurry H z‖ₑ)).symm
    have hstep : (∫⁻ z : β × E, ‖Function.uncurry H z.swap‖ₑ ∂ν.prod μ)
        = ∫⁻ x : β, ∫⁻ p : E, ‖H p x‖ₑ ∂μ ∂ν :=
      lintegral_prod (μ := ν) (ν := μ)
        (f := fun z : β × E => ‖Function.uncurry H z.swap‖ₑ) hf
    have hchain : (∫⁻ z : E × β, ‖Function.uncurry H z‖ₑ ∂μ.prod ν)
        = ∫⁻ x : β, ∫⁻ p : E, ‖H p x‖ₑ ∂μ ∂ν := hswap.trans hstep
    rw [hchain]
    calc ∫⁻ x : β, ∫⁻ p : E, ‖H p x‖ₑ ∂μ ∂ν
        ≤ ∫⁻ x : β, (ENNReal.ofReal C * K) ∂ν := lintegral_mono_ae hinner
      _ = (ENNReal.ofReal C * K) * ν Set.univ := lintegral_const _
      _ < ⊤ := ENNReal.mul_lt_top
          (ENNReal.mul_lt_top (lt_of_le_of_ne le_top ENNReal.ofReal_ne_top) hKfin)
          (lt_of_le_of_ne le_top hνfin)
  exact ⟨hH, hfin⟩

theorem integrable_uncurry_of_radial_bound {n : ℕ} {A : Set (Submission.BoseGases.X n)}
    (hAfin : (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)) A ≠ ⊤)
    {H : EuclideanSpace ℝ (Fin 3) → Submission.BoseGases.X n → ℝ}
    (hH : MeasureTheory.AEStronglyMeasurable (Function.uncurry H)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict A)))
    {C : ℝ} (hC : 0 ≤ C)
    (hbd : ∀ᵐ x ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict A),
      ∀ p : EuclideanSpace ℝ (Fin 3), ‖H p x‖ ≤ C / (1 + ‖p‖) ^ 4) :
    MeasureTheory.Integrable (Function.uncurry H)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict A)) := by
  refine integrable_uncurry_of_radial_bound_aux
    (E := EuclideanSpace ℝ (Fin 3)) (β := Submission.BoseGases.X n)
    (μ := (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    (ν := (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict A)
    ?_ hH hC ?_ hbd
  · rw [Measure.restrict_apply_univ]
    exact hAfin
  · simp [finrank_euclideanSpace]
    norm_num

end Work.BoseFixB2.DvApriori

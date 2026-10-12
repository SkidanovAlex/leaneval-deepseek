import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.Row2.heatFubini`

The **subordination identity** for the `p`-convention Fourier transform used in the row-2
bookkeeping of the lattice Coulomb chapter: for every `f : ℝ³ → ℝ` whose
`p ↦ f p / (2‖p‖²)` is integrable,

    ∫ p, f p / (2‖p‖²) = ½ ∫_{t>0} ∫ p, f p e^{−t‖p‖²} .

This is the integrated form of `∫_{t>0} e^{−t c} dt = 1/c`, obtained by Tonelli/Fubini on
`ℝ³ × (0,∞)`: the only ingredient is the finiteness of `∫⁻ p, ‖f p / (2‖p‖²)‖`, which is
exactly the hypothesis (it makes the joint integral finite, hence the Bochner integral
`∫_{(p,t)} f p e^{−t‖p‖²}` well behaved and the two iterated integrals equal).
-/

namespace Work.BoseRowsL.Row2

open MeasureTheory

/-- `‖x‖ₑ = ENNReal.ofReal ‖x‖` for real `x`. -/
lemma enorm_eq_ofReal_norm_real (x : ℝ) : ‖x‖ₑ = ENNReal.ofReal ‖x‖ := by
  rw [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs]

/-- `2 * (a / (2 * b)) = a / b` (valid also at `b = 0`, by the convention `a / 0 = 0`). -/
lemma two_mul_div_two (a b : ℝ) : 2 * (a / (2 * b)) = a / b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  · field_simp

/-- `∫_{t>0} e^{−tc} dt = 1/c` for `c > 0`. -/
lemma integral_exp_neg_mul_Ioi (c : ℝ) (hc : 0 < c) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(t * c)) = c⁻¹ := by
  have hraw := integral_exp_neg_mul_rpow (p := (1 : ℝ)) (b := c) one_pos hc
  have hb : c ^ (-(1 : ℝ) / 1) = c⁻¹ := by rw [div_one, Real.rpow_neg_one]
  have hg : Real.Gamma ((1 : ℝ) / 1 + 1) = 1 := by
    rw [show (1 : ℝ) / 1 + 1 = 2 by norm_num, Real.Gamma_two]
  rw [hb, hg, mul_one] at hraw
  rw [← hraw]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
  congr 1
  rw [Real.rpow_one]
  ring

/-- The `lintegral` form `∫⁻_{t>0} e^{−tc} = 1/c` for `c > 0`. -/
lemma lintegral_exp_neg_mul_Ioi (c : ℝ) (hc : 0 < c) :
    ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-(t * c))) = ENNReal.ofReal c⁻¹ := by
  have hIntOn : IntegrableOn (fun t : ℝ => Real.exp (-(t * c))) (Set.Ioi (0 : ℝ)) volume := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (0 : ℝ)) (p := (1 : ℝ)) (b := c)
      (by norm_num) one_pos hc
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only []
    rw [Real.rpow_one, Real.rpow_zero, one_mul, mul_comm]
    congr 1
    ring
  have h := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntOn
    (Filter.Eventually.of_forall fun t => (Real.exp_pos _).le)
  rw [← h, integral_exp_neg_mul_Ioi c hc]

/-- **The subordination identity.**  For any `f : ℝ³ → ℝ` with `f / (2‖p‖²) ∈ L¹`,
`∫ f(p)/(2‖p‖²) dp = ½ ∫_{t>0} ∫ f(p) e^{−t‖p‖²} dp dt`. -/
lemma heatFubini_aux {f : ℝ³ → ℝ}
    (hInt : Integrable (fun p : ℝ³ => f p / (2 * ‖p‖ ^ 2))) :
    (∫ p : ℝ³, f p / (2 * ‖p‖ ^ 2))
      = (1 / 2) * ∫ t in Set.Ioi (0 : ℝ), ∫ p : ℝ³, f p * Real.exp (-(t * ‖p‖ ^ 2)) := by
  -- the set `{p : ‖p‖ = 0}` is null
  have hnull : volume {p : ℝ³ | (2 : ℝ) * ‖p‖ ^ 2 = 0} = 0 := by
    have hset : {p : ℝ³ | (2 : ℝ) * ‖p‖ ^ 2 = 0} = {0} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro hp
        have h2 : ‖p‖ ^ 2 = 0 := by
          rcases mul_eq_zero.mp hp with h | h
          · exact absurd h (by norm_num)
          · exact h
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp h2)
      · rintro rfl
        simp
    rw [hset, measure_singleton]
  have hne : ∀ᵐ p ∂(volume : Measure ℝ³), (2 : ℝ) * ‖p‖ ^ 2 ≠ 0 := by
    have hcompl : {p : ℝ³ | ¬ ((2 : ℝ) * ‖p‖ ^ 2 ≠ 0)} = {p : ℝ³ | (2 : ℝ) * ‖p‖ ^ 2 = 0} := by
      ext p
      simp
    rw [ae_iff, hcompl]
    exact hnull
  have hne_norm : ∀ᵐ p ∂(volume : Measure ℝ³), ‖p‖ ≠ 0 := by
    filter_upwards [hne] with p hp h0
    exact hp (by rw [h0]; norm_num)
  -- strong measurability of `f`, from the integrability hypothesis
  have hf_aesm : AEStronglyMeasurable f volume := by
    have hae : f =ᵐ[volume] (fun p : ℝ³ => (f p / (2 * ‖p‖ ^ 2)) * (2 * ‖p‖ ^ 2)) := by
      filter_upwards [hne] with p hp
      exact (div_mul_cancel₀ (f p) hp).symm
    have hprod : AEStronglyMeasurable
        (fun p : ℝ³ => (f p / (2 * ‖p‖ ^ 2)) * (2 * ‖p‖ ^ 2)) volume :=
      hInt.aestronglyMeasurable.mul
        ((continuous_const.mul (continuous_norm.pow 2)).aestronglyMeasurable)
    exact hprod.congr hae.symm
  -- the joint integrand on `ℝ³ × (0,∞)`
  set F : ℝ³ × ℝ → ℝ := fun z => f z.1 * Real.exp (-(z.2 * ‖z.1‖ ^ 2)) with hFdef
  have hF_aesm : AEStronglyMeasurable F (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    rw [hFdef]
    have hcont : Continuous (fun z : ℝ³ × ℝ => Real.exp (-(z.2 * ‖z.1‖ ^ 2))) := by
      have h1 : Continuous (fun z : ℝ³ × ℝ => ‖z.1‖) := continuous_norm.comp continuous_fst
      have h2 : Continuous (fun z : ℝ³ × ℝ => ‖z.1‖ ^ 2) := h1.pow 2
      have h3 : Continuous (fun z : ℝ³ × ℝ => z.2 * ‖z.1‖ ^ 2) := continuous_snd.mul h2
      have h4 : Continuous (fun z : ℝ³ × ℝ => -(z.2 * ‖z.1‖ ^ 2)) := h3.neg
      exact Real.continuous_exp.comp h4
    exact hf_aesm.comp_fst.mul hcont.aestronglyMeasurable
  have hF_enorm : AEMeasurable (fun z : ℝ³ × ℝ => ‖F z‖ₑ)
      (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := hF_aesm.enorm
  -- the inner `t`-integral, for a.e. `p`
  have hinner : ∀ᵐ p ∂(volume : Measure ℝ³),
      (∫⁻ t : ℝ, ‖F (p, t)‖ₑ ∂(volume.restrict (Set.Ioi (0 : ℝ))))
        = ENNReal.ofReal (‖f p‖ / ‖p‖ ^ 2) := by
    filter_upwards [hne_norm] with p hp
    have hc : (0 : ℝ) < ‖p‖ ^ 2 := sq_pos_of_ne_zero hp
    have hpt : ∀ t : ℝ, ‖F (p, t)‖ₑ
        = ENNReal.ofReal ‖f p‖ * ENNReal.ofReal (Real.exp (-(t * ‖p‖ ^ 2))) := by
      intro t
      change ‖f p * Real.exp (-(t * ‖p‖ ^ 2))‖ₑ = _
      rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal (Real.exp_pos _).le]
      congr 1
    rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_exp_neg_mul_Ioi _ hc, ← ENNReal.ofReal_mul (norm_nonneg (f p))]
    congr 1
  have hA_lt : (∫⁻ p : ℝ³, ENNReal.ofReal ‖f p / (2 * ‖p‖ ^ 2)‖) < ⊤ :=
    (hasFiniteIntegral_iff_norm (fun p : ℝ³ => f p / (2 * ‖p‖ ^ 2))).mp hInt.hasFiniteIntegral
  -- the joint `lintegral` is finite
  have hlin : (∫⁻ z : ℝ³ × ℝ, ‖F z‖ₑ ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
      = ENNReal.ofReal 2 * ∫⁻ p : ℝ³, ENNReal.ofReal ‖f p / (2 * ‖p‖ ^ 2)‖ := by
    rw [lintegral_prod _ hF_enorm, lintegral_congr_ae hinner,
      ← lintegral_const_mul' (ENNReal.ofReal 2) _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun p => ?_)
    have hden : ‖(2 : ℝ) * ‖p‖ ^ 2‖ = 2 * ‖p‖ ^ 2 := by
      rw [Real.norm_of_nonneg (by positivity)]
    have hnorm : ‖f p / (2 * ‖p‖ ^ 2)‖ = ‖f p‖ / (2 * ‖p‖ ^ 2) := by rw [norm_div, hden]
    rw [hnorm, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num), two_mul_div_two]
  have hF_fin : HasFiniteIntegral F (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) := by
    rw [hasFiniteIntegral_iff_norm]
    have hlow : (∫⁻ z : ℝ³ × ℝ,
          ENNReal.ofReal ‖F z‖ ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
        = ∫⁻ z : ℝ³ × ℝ, ‖F z‖ₑ ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) :=
      lintegral_congr (fun z => (enorm_eq_ofReal_norm_real (F z)).symm)
    rw [hlow, hlin]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA_lt
  have hFint : Integrable F (volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))) :=
    ⟨hF_aesm, hF_fin⟩
  -- Fubini in both orders
  have hFub1 : (∫ z : ℝ³ × ℝ, F z ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
      = ∫ p : ℝ³, ∫ t : ℝ, F (p, t) ∂(volume.restrict (Set.Ioi (0 : ℝ))) ∂volume :=
    integral_prod F hFint
  have hFub2 : (∫ z : ℝ³ × ℝ, F z ∂(volume.prod (volume.restrict (Set.Ioi (0 : ℝ)))))
      = ∫ t : ℝ, ∫ p : ℝ³, F (p, t) ∂volume ∂(volume.restrict (Set.Ioi (0 : ℝ))) :=
    integral_prod_symm F hFint
  -- the inner Bochner integral `∫_{t>0} f(p) e^{−t‖p‖²} dt = f(p)/‖p‖²`, for a.e. `p`
  have hinner_int : (fun p : ℝ³ => ∫ t : ℝ, F (p, t) ∂(volume.restrict (Set.Ioi (0 : ℝ))))
      =ᵐ[volume] (fun p : ℝ³ => f p / ‖p‖ ^ 2) := by
    filter_upwards [hne_norm] with p hp
    have hc : (0 : ℝ) < ‖p‖ ^ 2 := sq_pos_of_ne_zero hp
    change (∫ t : ℝ, f p * Real.exp (-(t * ‖p‖ ^ 2))
        ∂(volume.restrict (Set.Ioi (0 : ℝ)))) = f p / ‖p‖ ^ 2
    rw [integral_const_mul, integral_exp_neg_mul_Ioi _ hc, div_eq_mul_inv]
  have hchain : (∫ p : ℝ³, ∫ t : ℝ, F (p, t) ∂(volume.restrict (Set.Ioi (0 : ℝ))) ∂volume)
      = 2 * ∫ p : ℝ³, f p / (2 * ‖p‖ ^ 2) := by
    rw [integral_congr_ae hinner_int, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun p => (two_mul_div_two (f p) (‖p‖ ^ 2)).symm))
  have hkey : (∫ t in Set.Ioi (0 : ℝ), ∫ p : ℝ³, f p * Real.exp (-(t * ‖p‖ ^ 2)))
      = 2 * ∫ p : ℝ³, f p / (2 * ‖p‖ ^ 2) := hFub2.symm.trans (hFub1.trans hchain)
  rw [hkey]
  ring

theorem heatFubini {h : ℝ³ → ℝ}
    (hInt : MeasureTheory.Integrable (fun p : ℝ³ => Work.BoseFixR.chat h p / (2 * ‖p‖ ^ 2))) :
    (∫ p : ℝ³, Work.BoseFixR.chat h p / (2 * ‖p‖ ^ 2))
      = (1 / 2) * ∫ t in Set.Ioi (0 : ℝ),
          ∫ p : ℝ³, Work.BoseFixR.chat h p * Real.exp (-(t * ‖p‖ ^ 2)) :=
  heatFubini_aux hInt

end Work.BoseRowsL.Row2

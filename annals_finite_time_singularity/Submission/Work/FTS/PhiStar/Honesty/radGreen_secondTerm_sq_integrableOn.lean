import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.EllExist.Closers.aesm_tailPrim_Ioi
import Submission.Work.FTS.PhiStar.Honesty.psi_cs_of_aesm
import Submission.Work.FTS.PhiStar.Honesty.lintegral_ofReal_rpow_Ioo
import Submission.Work.FTS.PhiStar.Honesty.lintegral_tail_swap_Ioi_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter
open scoped ENNReal

/-- `ENNReal.ofReal` of a set integral of a nonnegative a.e.-strongly-measurable function is at
most the set lintegral of `ENNReal.ofReal` of the integrand. -/
lemma ofReal_setIntegral_le_setLIntegral' {f : ℝ → ℝ} {s : Set ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict s)) (hnn : 0 ≤ᵐ[volume.restrict s] f) :
    ENNReal.ofReal (∫ t in s, f t) ≤ ∫⁻ t in s, ENNReal.ofReal (f t) := by
  rw [integral_eq_lintegral_of_nonneg_ae hnn hf]
  exact ENNReal.ofReal_toReal_le

/-- **Far-field weighted Hardy bound for the `z^p` branch of the radial Green function.**
For `p > 0` and `c` with `c²` integrable on `(1,∞)`, the function
`z ↦ (z^p ∫_z^∞ c t · t^{-p-1} dt)²` is integrable on `(1,∞)`. -/
theorem radGreen_secondTerm_sq_integrableOn_aux {p : ℝ} (hp : 0 < p) {c : ℝ → ℝ}
    (hint : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    IntegrableOn (fun z : ℝ => (z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2)
      (Set.Ioi 1) := by
  set W : ℝ → ℝ := fun t => (c t) ^ 2 * t ^ (-p - 1) with hW
  have hWt : ∀ t : ℝ, W t = (c t) ^ 2 * t ^ (-p - 1) := fun t => rfl
  -- (0) measurability of the weight and of `W` on `(1,∞)`
  have hpow_aesm : AEStronglyMeasurable (fun t : ℝ => t ^ (-p - 1))
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    (continuous_id.continuousOn.rpow_const
      (fun t ht => Or.inl (ne_of_gt (lt_trans zero_lt_one ht)))).aestronglyMeasurable
      measurableSet_Ioi
  have hW_aesm : AEStronglyMeasurable W (volume.restrict (Set.Ioi (1 : ℝ))) :=
    hint.aestronglyMeasurable.mul hpow_aesm
  -- (1) the pointwise (weighted Cauchy–Schwarz) bound, valid for every `z > 1`
  have hpt : ∀ z ∈ Set.Ioi (1 : ℝ),
      (z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2
        ≤ (1 / p) * z ^ p * (∫ t in Set.Ioi z, W t) := by
    intro z hz
    have hz1 : (1 : ℝ) ≤ z := le_of_lt hz
    have hz0 : (0 : ℝ) < z := lt_trans zero_lt_one hz
    have hsub : Set.Ioi z ⊆ Set.Ioi (1 : ℝ) := Set.Ioi_subset_Ioi hz1
    have h2 : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi z) := hint.mono_set hsub
    have hWnn : 0 ≤ ∫ t in Set.Ioi z, W t := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [hWt]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (lt_trans hz0 ht)) _)
    by_cases hc : AEStronglyMeasurable c (volume.restrict (Set.Ioi z))
    · -- good case: weighted Cauchy–Schwarz
      have hcs : (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2
          ≤ (1 / p) * z ^ (-p) * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1) :=
        psi_cs_of_aesm hp hz0 hc h2
      have hcs' : (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2
          ≤ (1 / p) * z ^ (-p) * ∫ t in Set.Ioi z, W t := by
        simpa only [hWt] using hcs
      have hzp2 : (z ^ p) ^ 2 = z ^ (2 * p) := by
        rw [sq, ← Real.rpow_add hz0, show p + p = 2 * p by ring]
      have hzpm : z ^ (2 * p) * z ^ (-p) = z ^ p := by
        rw [← Real.rpow_add hz0, show 2 * p + -p = p by ring]
      calc (z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2
          = z ^ (2 * p) * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2 := by
            rw [mul_pow, hzp2]
        _ ≤ z ^ (2 * p) * ((1 / p) * z ^ (-p) * ∫ t in Set.Ioi z, W t) :=
            mul_le_mul_of_nonneg_left hcs' (by positivity)
        _ = (1 / p) * z ^ p * (∫ t in Set.Ioi z, W t) := by
            calc z ^ (2 * p) * ((1 / p) * z ^ (-p) * ∫ t in Set.Ioi z, W t)
                = (1 / p) * (∫ t in Set.Ioi z, W t) * (z ^ (2 * p) * z ^ (-p)) := by ring
              _ = (1 / p) * (∫ t in Set.Ioi z, W t) * z ^ p := by rw [hzpm]
              _ = (1 / p) * z ^ p * (∫ t in Set.Ioi z, W t) := by ring
    · -- bad case: the integrand is not a.e. strongly measurable, so the junk integral is `0`
      have hnaesm : ¬ AEStronglyMeasurable (fun t : ℝ => c t * t ^ (-p - 1))
          (volume.restrict (Set.Ioi z)) := by
        intro hf
        have hmult : AEStronglyMeasurable
            (fun t : ℝ => (c t * t ^ (-p - 1)) * t ^ (p + 1))
            (volume.restrict (Set.Ioi z)) :=
          hf.mul ((continuous_id.continuousOn.rpow_const
            (fun t ht => Or.inl (ne_of_gt (lt_trans hz0 ht)))).aestronglyMeasurable
              measurableSet_Ioi)
        have heq : (fun t : ℝ => (c t * t ^ (-p - 1)) * t ^ (p + 1))
            =ᵐ[volume.restrict (Set.Ioi z)] c := by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht0 : (0 : ℝ) < t := lt_trans hz0 ht
          rw [mul_assoc, ← Real.rpow_add ht0, show -p - 1 + (p + 1) = 0 by ring,
            Real.rpow_zero, mul_one]
        exact hc (hmult.congr heq)
      have hzero : (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) = 0 :=
        integral_undef (fun hf => hnaesm hf.aestronglyMeasurable)
      rw [hzero]
      have hz2 : (z ^ p * 0) ^ 2 = (0 : ℝ) := by ring
      rw [hz2]
      exact mul_nonneg (mul_nonneg (div_nonneg zero_le_one hp.le) (Real.rpow_nonneg hz0.le p))
        hWnn
  -- (2) the outer lintegral bound
  have hpow_aem : AEMeasurable (fun z : ℝ => ENNReal.ofReal (z ^ p))
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuous_id.continuousOn.rpow_const
        (fun t ht => Or.inl (ne_of_gt (lt_trans zero_lt_one ht)))).aemeasurable
          measurableSet_Ioi)
  have hW_aem : AEMeasurable (fun t : ℝ => ENNReal.ofReal (W t))
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hW_aesm.aemeasurable
  have hswap : ∫⁻ z in Set.Ioi (1 : ℝ), ENNReal.ofReal (z ^ p) * (∫⁻ t in Set.Ioi z, ENNReal.ofReal (W t))
      = ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (W t)
          * (∫⁻ z in (Set.Ioi (1 : ℝ) ∩ Set.Iio t), ENNReal.ofReal (z ^ p)) :=
    lintegral_tail_swap_Ioi_one hpow_aem hW_aem
      (fun z => ENNReal.ofReal_lt_top.ne) (fun t => ENNReal.ofReal_lt_top.ne)
  have hA : ∫⁻ z in Set.Ioi (1 : ℝ),
        ENNReal.ofReal ((z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2)
      ≤ ∫⁻ z in Set.Ioi (1 : ℝ),
        ENNReal.ofReal ((1 / p) * z ^ p * (∫ t in Set.Ioi z, W t)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact ENNReal.ofReal_le_ofReal (hpt z hz)
  have hB : ∫⁻ z in Set.Ioi (1 : ℝ),
        ENNReal.ofReal ((1 / p) * z ^ p * (∫ t in Set.Ioi z, W t))
      = ENNReal.ofReal (1 / p) * ∫⁻ z in Set.Ioi (1 : ℝ),
        ENNReal.ofReal (z ^ p) * ENNReal.ofReal (∫ t in Set.Ioi z, W t) := by
    rw [← lintegral_const_mul' (ENNReal.ofReal (1 / p)) _ ENNReal.ofReal_lt_top.ne]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hz0 : (0 : ℝ) < z := lt_trans zero_lt_one hz
    rw [ENNReal.ofReal_mul
        (mul_nonneg (div_nonneg zero_le_one hp.le) (Real.rpow_nonneg hz0.le p)),
      ENNReal.ofReal_mul (div_nonneg zero_le_one hp.le), mul_assoc]
  have hC : ∫⁻ z in Set.Ioi (1 : ℝ),
        ENNReal.ofReal (z ^ p) * ENNReal.ofReal (∫ t in Set.Ioi z, W t)
      ≤ ∫⁻ z in Set.Ioi (1 : ℝ),
        ENNReal.ofReal (z ^ p) * (∫⁻ t in Set.Ioi z, ENNReal.ofReal (W t)) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    refine mul_le_mul' le_rfl ?_
    refine ofReal_setIntegral_le_setLIntegral' ?_ ?_
    · have hz1 : (1 : ℝ) ≤ z := le_of_lt hz
      have hz0 : (0 : ℝ) < z := lt_trans zero_lt_one hz
      have hsub : Set.Ioi z ⊆ Set.Ioi (1 : ℝ) := Set.Ioi_subset_Ioi hz1
      exact (hint.mono_set hsub).aestronglyMeasurable.mul
        ((continuous_id.continuousOn.rpow_const
          (fun t ht => Or.inl (ne_of_gt (lt_trans hz0 ht)))).aestronglyMeasurable
            measurableSet_Ioi)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := lt_trans (lt_trans zero_lt_one hz) ht
      rw [hWt]
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht0.le _)
  have hD : ∫⁻ t in Set.Ioi (1 : ℝ),
        ENNReal.ofReal (W t) * (∫⁻ z in (Set.Ioi (1 : ℝ) ∩ Set.Iio t), ENNReal.ofReal (z ^ p))
      ≤ ENNReal.ofReal (1 / (p + 1))
        * ∫⁻ t in Set.Ioi (1 : ℝ),
            ENNReal.ofReal (W t) * ENNReal.ofReal (t ^ (p + 1)) := by
    rw [← lintegral_const_mul' (ENNReal.ofReal (1 / (p + 1))) _ ENNReal.ofReal_lt_top.ne]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    have hinner : (∫⁻ z in (Set.Ioi (1 : ℝ) ∩ Set.Iio t), ENNReal.ofReal (z ^ p))
        ≤ ENNReal.ofReal (t ^ (p + 1) / (p + 1)) := by
      rw [show Set.Ioi (1 : ℝ) ∩ Set.Iio t = Set.Ioo 1 t from rfl]
      have hval : ∫⁻ z in Set.Ioo (1 : ℝ) t, ENNReal.ofReal (z ^ p)
          = ENNReal.ofReal ((t ^ (p + 1) - 1) / (p + 1)) :=
        lintegral_ofReal_rpow_Ioo p t hp ht1
      refine hval.trans_le ?_
      refine ENNReal.ofReal_le_ofReal ?_
      rw [div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < p + 1)]
      have h1 : (1 : ℝ) ≤ t ^ (p + 1) := Real.one_le_rpow ht1 (by linarith)
      linarith
    have hof : ENNReal.ofReal (t ^ (p + 1) / (p + 1))
        = ENNReal.ofReal (1 / (p + 1)) * ENNReal.ofReal (t ^ (p + 1)) := by
      rw [show t ^ (p + 1) / (p + 1) = (1 / (p + 1)) * t ^ (p + 1) by ring,
        ENNReal.ofReal_mul (div_nonneg zero_le_one (by linarith : (0 : ℝ) ≤ p + 1))]
    calc ENNReal.ofReal (W t) * (∫⁻ z in (Set.Ioi (1 : ℝ) ∩ Set.Iio t), ENNReal.ofReal (z ^ p))
        ≤ ENNReal.ofReal (W t) * ENNReal.ofReal (t ^ (p + 1) / (p + 1)) :=
          mul_le_mul' le_rfl hinner
      _ = ENNReal.ofReal (1 / (p + 1))
            * (ENNReal.ofReal (W t) * ENNReal.ofReal (t ^ (p + 1))) := by
          rw [hof]
          ring
  have hE : ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal (W t) * ENNReal.ofReal (t ^ (p + 1))
      = ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c t) ^ 2) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    rw [← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht0.le _))]
    congr 1
    show (c t) ^ 2 * t ^ (-p - 1) * t ^ (p + 1) = (c t) ^ 2
    rw [mul_assoc, ← Real.rpow_add ht0, show -p - 1 + (p + 1) = 0 by ring, Real.rpow_zero,
      mul_one]
  have hchain : ∫⁻ z in Set.Ioi (1 : ℝ),
        ENNReal.ofReal ((z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2)
      ≤ ENNReal.ofReal (1 / p)
        * (ENNReal.ofReal (1 / (p + 1))
            * ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c t) ^ 2)) := by
    calc ∫⁻ z in Set.Ioi (1 : ℝ),
          ENNReal.ofReal ((z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2)
        ≤ ∫⁻ z in Set.Ioi (1 : ℝ),
            ENNReal.ofReal ((1 / p) * z ^ p * (∫ t in Set.Ioi z, W t)) := hA
      _ = ENNReal.ofReal (1 / p) * ∫⁻ z in Set.Ioi (1 : ℝ),
            ENNReal.ofReal (z ^ p) * ENNReal.ofReal (∫ t in Set.Ioi z, W t) := hB
      _ ≤ ENNReal.ofReal (1 / p) * ∫⁻ z in Set.Ioi (1 : ℝ),
            ENNReal.ofReal (z ^ p) * (∫⁻ t in Set.Ioi z, ENNReal.ofReal (W t)) :=
          mul_le_mul' le_rfl hC
      _ = ENNReal.ofReal (1 / p) * ∫⁻ t in Set.Ioi (1 : ℝ),
            ENNReal.ofReal (W t)
              * (∫⁻ z in (Set.Ioi (1 : ℝ) ∩ Set.Iio t), ENNReal.ofReal (z ^ p)) := by
          rw [hswap]
      _ ≤ ENNReal.ofReal (1 / p) * (ENNReal.ofReal (1 / (p + 1))
            * ∫⁻ t in Set.Ioi (1 : ℝ),
                ENNReal.ofReal (W t) * ENNReal.ofReal (t ^ (p + 1))) :=
          mul_le_mul' le_rfl hD
      _ = ENNReal.ofReal (1 / p) * (ENNReal.ofReal (1 / (p + 1))
            * ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c t) ^ 2)) := by rw [hE]
  -- (3) the right-hand side is finite
  have hcf : ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c t) ^ 2)
      = ENNReal.ofReal (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall (fun t => sq_nonneg (c t)))).symm
  have hne : ∫⁻ z in Set.Ioi (1 : ℝ),
        ENNReal.ofReal ((z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt hchain ?_)
    rw [hcf]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  -- (4) a.e. strong measurability of the target, then `IntegrableOn`
  have htail : AEStronglyMeasurable (fun z : ℝ => ∫ t in Set.Ioi z, c t * t ^ (-p - 1))
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    (Work.FTS.EllExist.Closers.aesm_tailPrim_Ioi (fun t : ℝ => c t * t ^ (-p - 1))).mono_measure
      (Measure.restrict_mono (Set.Ioi_subset_Ioi (zero_le_one)) le_rfl)
  have hzp_aesm : AEStronglyMeasurable (fun z : ℝ => z ^ p)
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    (continuous_id.continuousOn.rpow_const
      (fun t ht => Or.inl (ne_of_gt (lt_trans zero_lt_one ht)))).aestronglyMeasurable
      measurableSet_Ioi
  have hT_aesm : AEStronglyMeasurable
      (fun z : ℝ => (z ^ p * (∫ t in Set.Ioi z, c t * t ^ (-p - 1))) ^ 2)
      (volume.restrict (Set.Ioi (1 : ℝ))) := (hzp_aesm.mul htail).pow 2
  exact (lintegral_ofReal_ne_top_iff_integrable hT_aesm
    (Eventually.of_forall (fun z => sq_nonneg _))).mp hne

theorem radGreen_secondTerm_sq_integrableOn {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hm : 1 ≤ m)
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (z ^ (2 * (m : ℝ) / α)
          * (∫ t in Set.Ioi z, c t * t ^ (-(2 * (m : ℝ) / α) - 1))) ^ 2)
      (Set.Ioi 1) := by
  have hmr : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hm)
  have hp : 0 < 2 * (m : ℝ) / α := div_pos (by linarith) hα
  exact radGreen_secondTerm_sq_integrableOn_aux hp hint

end Work.FTS.PhiStar.Honesty

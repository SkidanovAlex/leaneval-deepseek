import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Honesty.lintegral_Ioo_triangle
import Submission.Work.FTS.PhiStar.Honesty.lintegral_Ioo_tail_swap
import Submission.Work.FTS.PhiStar.Honesty.lintegral_ofReal_rpow_Ioo_zero_min
import Submission.Work.FTS.PhiStar.Honesty.sq_integrableOn_Ioi_of
import Submission.Work.FTS.PhiStar.Honesty.psi_cs_of_aesm
import Submission.Work.FTS.EllExist.Closers.aesm_tailPrim_Ioi
import Submission.Work.FTS.PhiStar.Honesty.radGreen_secondTerm_sq_integrableOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped ENNReal

namespace Work.FTS.PhiStar.Honesty

-- ================================ the main auxiliary estimate ================================

/-- Abstract form of the target: for `p > 3`,
`z ↦ z^{2p-4} (∫_{t > z} c t t^{-p-1})²` is integrable on `(0,1)`. -/
private theorem key_tail {p : ℝ} (hp : 0 < p) (hp3 : 3 < p) {c : ℝ → ℝ} (hc : AEMeasurable c)
    (hnear : IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    IntegrableOn
      (fun z : ℝ => z ^ (2 * p - 4) * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2)
      (Set.Ioo 0 1) := by
  have hr : (-1 : ℝ) < p - 4 := by linarith
  have hc_aesm : AEStronglyMeasurable c volume := hc.aestronglyMeasurable
  -- ### (1) weighted Cauchy–Schwarz on the tail `(z,∞)`
  have hcs : ∀ z : ℝ, 0 < z →
      (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2
        ≤ (1 / p) * z ^ (-p) * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1) := by
    intro z hz
    exact psi_cs_of_aesm hp hz (hc_aesm.mono_measure Measure.restrict_le_self)
      (sq_integrableOn_Ioi_of hz hnear hfar)
  -- ### (2) the pointwise `ENNReal` bound
  have hstep : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal (z ^ (2 * p - 4) * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2)
        ≤ ENNReal.ofReal (1 / p)
            * (ENNReal.ofReal (z ^ (p - 4))
                * ∫⁻ t in Set.Ioi z, ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))) := by
    intro z hz
    have hz0 : 0 < z := hz.1
    have hzp : ENNReal.ofReal (z ^ (2 * p - 4)) * ENNReal.ofReal (z ^ (-p))
        = ENNReal.ofReal (z ^ (p - 4)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hz0.le _)]
      congr 1
      rw [← Real.rpow_add hz0]
      congr 1
      ring
    have hA : ENNReal.ofReal ((1 / p) * z ^ (-p)
          * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1))
        = ENNReal.ofReal (1 / p) * (ENNReal.ofReal (z ^ (-p))
            * ENNReal.ofReal (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1))) := by
      rw [ENNReal.ofReal_mul (mul_nonneg (by positivity) (Real.rpow_nonneg hz0.le _)),
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / p), mul_assoc]
    have hWaesm : AEStronglyMeasurable (fun t : ℝ => (c t) ^ 2 * t ^ (-p - 1))
        (volume.restrict (Set.Ioi z)) := by
      have h1 : AEStronglyMeasurable (fun t : ℝ => (c t) ^ 2)
          (volume.restrict (Set.Ioi z)) :=
        (hc_aesm.pow 2).mono_measure Measure.restrict_le_self
      have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ (-p - 1))
          (volume.restrict (Set.Ioi z)) :=
        (continuousOn_id.rpow_const
          (fun t ht => Or.inl (ne_of_gt (lt_trans hz0 ht)))).aestronglyMeasurable measurableSet_Ioi
      exact h1.mul h2
    have hWnn : 0 ≤ᵐ[volume.restrict (Set.Ioi z)]
        (fun t : ℝ => (c t) ^ 2 * t ^ (-p - 1)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (lt_trans hz0 ht)) _)
    calc ENNReal.ofReal (z ^ (2 * p - 4) * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2)
        = ENNReal.ofReal (z ^ (2 * p - 4))
            * ENNReal.ofReal ((∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2) := by
          rw [ENNReal.ofReal_mul (Real.rpow_nonneg hz0.le _)]
      _ ≤ ENNReal.ofReal (z ^ (2 * p - 4))
            * ENNReal.ofReal ((1 / p) * z ^ (-p)
                * ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1)) :=
          mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hcs z hz0))
      _ = ENNReal.ofReal (z ^ (2 * p - 4))
            * (ENNReal.ofReal (1 / p) * (ENNReal.ofReal (z ^ (-p))
                * ENNReal.ofReal (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-p - 1)))) := by
          rw [hA]
      _ ≤ ENNReal.ofReal (z ^ (2 * p - 4))
            * (ENNReal.ofReal (1 / p) * (ENNReal.ofReal (z ^ (-p))
                * ∫⁻ t in Set.Ioi z, ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1)))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl
            (ofReal_setIntegral_le_setLIntegral' hWaesm hWnn)))
      _ = ENNReal.ofReal (1 / p)
            * (ENNReal.ofReal (z ^ (p - 4))
                * ∫⁻ t in Set.Ioi z, ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))) := by
          rw [← hzp]; ring
  -- ### (3) the two measurability inputs of the swap lemma
  have hF_aem : AEMeasurable (fun z : ℝ => ENNReal.ofReal (z ^ (p - 4)))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz.1))).aemeasurable
        measurableSet_Ioo)
  have hG_aem : AEMeasurable (fun t : ℝ => ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1)))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h1 : AEMeasurable (fun t : ℝ => (c t) ^ 2) (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (hc.pow aemeasurable_const).mono_measure Measure.restrict_le_self
    have h2 : AEMeasurable (fun t : ℝ => t ^ (-p - 1)) (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht))).aemeasurable measurableSet_Ioi
    exact ENNReal.measurable_ofReal.comp_aemeasurable (h1.mul h2)
  have hswap := lintegral_Ioo_tail_swap
    (F := fun z : ℝ => ENNReal.ofReal (z ^ (p - 4)))
    (G := fun t : ℝ => ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))) hF_aem hG_aem
  -- ### (4) the factor `ofReal (1/(p-3))`
  have hfac : (∫⁻ t in Set.Ioi (0 : ℝ), (ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))
        * ENNReal.ofReal (t ^ (p - 3) / (p - 3))))
      = ENNReal.ofReal (1 / (p - 3))
        * ∫⁻ t in Set.Ioi (0 : ℝ), (ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))
            * ENNReal.ofReal (t ^ (p - 3))) := by
    rw [← lintegral_const_mul' (ENNReal.ofReal (1 / (p - 3))) _
      ENNReal.ofReal_lt_top.ne]
    refine lintegral_congr_ae ?_
    filter_upwards with t
    rw [show t ^ (p - 3) / (p - 3) = (1 / (p - 3)) * t ^ (p - 3) from by ring]
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (p - 3))]
    ring
  -- ### (5) the exponent identity `(c t)² t^{-p-1} t^{p-3} = (c t)²/t⁴`
  have hident : (∫⁻ t in Set.Ioi (0 : ℝ), (ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))
        * ENNReal.ofReal (t ^ (p - 3))))
      = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ((c t) ^ 2 / t ^ 4) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    rw [← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht0.le _))]
    congr 1
    have hpw : t ^ (-4 : ℝ) = (t ^ 4)⁻¹ := by
      rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) from by norm_num, Real.rpow_neg ht0.le,
        Real.rpow_natCast t 4]
    rw [mul_assoc, ← Real.rpow_add ht0, show -p - 1 + (p - 3) = -4 by ring, div_eq_mul_inv, hpw]
  -- ### (6) finiteness of `∫⁻_{t>0} ofReal ((c t)²/t⁴)`
  have hfin' : (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
      ≤ ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4)
        + ENNReal.ofReal (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by
    have hnn1 : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) 1)] (fun t : ℝ => (c t) ^ 2 / t ^ 4) :=
      Eventually.of_forall fun t => div_nonneg (sq_nonneg _) (by positivity)
    have hnn2 : 0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))] (fun t : ℝ => (c t) ^ 2) :=
      Eventually.of_forall fun t => sq_nonneg _
    have hfirst : (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
        = ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4) :=
      (ofReal_integral_eq_lintegral_ofReal hnear hnn1).symm
    have hsecond : (∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c t) ^ 2))
        = ENNReal.ofReal (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) :=
      (ofReal_integral_eq_lintegral_ofReal hfar hnn2).symm
    have hsub : Set.Ioi (0 : ℝ) ⊆ Set.Ioo (0 : ℝ) 1 ∪ Set.Ici 1 := by
      intro t ht
      rcases lt_or_ge t 1 with h | h
      · exact Or.inl ⟨ht, h⟩
      · exact Or.inr h
    have hdisj : Disjoint (Set.Ioo (0 : ℝ) 1) (Set.Ici 1) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      exact absurd ht2 (not_le.mpr ht1.2)
    have hdisj2 : Disjoint ({1} : Set ℝ) (Set.Ioi 1) := by
      rw [Set.disjoint_left]
      intro t ht1 ht2
      simp only [Set.mem_singleton_iff] at ht1
      rw [ht1] at ht2
      simp only [Set.mem_Ioi] at ht2
      exact lt_irrefl 1 ht2
    have hIci : (∫⁻ t in Set.Ici (1 : ℝ), ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
        = ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c t) ^ 2 / t ^ 4) := by
      rw [show Set.Ici (1 : ℝ) = ({1} : Set ℝ) ∪ Set.Ioi 1 from by
            ext t
            simp only [Set.mem_Ici, Set.mem_union, Set.mem_singleton_iff, Set.mem_Ioi]
            constructor
            · intro h
              rcases eq_or_lt_of_le h with h' | h'
              · exact Or.inl h'.symm
              · exact Or.inr h'
            · rintro (h | h)
              · exact le_of_eq h.symm
              · exact le_of_lt h,
        lintegral_union measurableSet_Ioi hdisj2,
        lintegral_singleton, measure_singleton, mul_zero, zero_add]
    have hIoi_le : (∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
        ≤ ∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c t) ^ 2) := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      refine ENNReal.ofReal_le_ofReal ?_
      have ht1 : (1 : ℝ) ≤ t ^ 4 := one_le_pow₀ (le_of_lt ht)
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg (c t)]
    calc (∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
        ≤ ∫⁻ t in (Set.Ioo (0 : ℝ) 1 ∪ Set.Ici 1), ENNReal.ofReal ((c t) ^ 2 / t ^ 4) :=
          lintegral_mono_set hsub
      _ = (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
            + (∫⁻ t in Set.Ici (1 : ℝ), ENNReal.ofReal ((c t) ^ 2 / t ^ 4)) :=
          lintegral_union measurableSet_Ici hdisj
      _ = (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
            + (∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c t) ^ 2 / t ^ 4)) := by rw [hIci]
      _ ≤ (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
            + (∫⁻ t in Set.Ioi (1 : ℝ), ENNReal.ofReal ((c t) ^ 2)) :=
          add_le_add le_rfl hIoi_le
      _ = ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4)
            + ENNReal.ofReal (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2) := by rw [hfirst, hsecond]
  -- ### (7) the chain
  have hbdd : (∫⁻ z in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (z ^ (2 * p - 4) * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2))
      ≤ ENNReal.ofReal (1 / p) * (ENNReal.ofReal (1 / (p - 3))
          * (ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4)
              + ENNReal.ofReal (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2))) := by
    calc (∫⁻ z in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal (z ^ (2 * p - 4) * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2))
        ≤ ∫⁻ z in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (1 / p)
            * (ENNReal.ofReal (z ^ (p - 4))
                * ∫⁻ t in Set.Ioi z, ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
          exact hstep z hz
      _ = ENNReal.ofReal (1 / p)
            * ∫⁻ z in Set.Ioo (0 : ℝ) 1, (ENNReal.ofReal (z ^ (p - 4))
                * ∫⁻ t in Set.Ioi z, ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_lt_top.ne]
      _ = ENNReal.ofReal (1 / p)
            * ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))
                * (∫⁻ z in (Set.Ioo (0 : ℝ) 1 ∩ Set.Iio t),
                    ENNReal.ofReal (z ^ (p - 4))) := by
          rw [hswap]
      _ ≤ ENNReal.ofReal (1 / p)
            * ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))
                * ENNReal.ofReal (t ^ (p - 3) / (p - 3)) := by
          refine mul_le_mul' le_rfl ?_
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have h := lintegral_ofReal_rpow_Ioo_zero_min (r := p - 4) (t := t) hr ht
          rw [show (p - 4) + 1 = p - 3 by ring] at h
          exact mul_le_mul' le_rfl h
      _ = ENNReal.ofReal (1 / p) * (ENNReal.ofReal (1 / (p - 3))
            * ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ((c t) ^ 2 * t ^ (-p - 1))
                * ENNReal.ofReal (t ^ (p - 3))) := by
          rw [hfac]
      _ = ENNReal.ofReal (1 / p) * (ENNReal.ofReal (1 / (p - 3))
            * ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal ((c t) ^ 2 / t ^ 4)) := by
          rw [hident]
      _ ≤ ENNReal.ofReal (1 / p) * (ENNReal.ofReal (1 / (p - 3))
            * (ENNReal.ofReal (∫ t in Set.Ioo (0 : ℝ) 1, (c t) ^ 2 / t ^ 4)
                + ENNReal.ofReal (∫ t in Set.Ioi (1 : ℝ), (c t) ^ 2))) :=
          mul_le_mul' le_rfl (mul_le_mul' le_rfl hfin')
  -- ### (8) measurability and conclusion
  have hne : (∫⁻ z in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (z ^ (2 * p - 4) * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2))
      ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt hbdd ?_)
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩))
  have hT_aesm : AEStronglyMeasurable
      (fun z : ℝ => z ^ (2 * p - 4) * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2)
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) := by
    have h1 : AEStronglyMeasurable (fun z : ℝ => ∫ t in Set.Ioi z, c t * t ^ (-p - 1))
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      (Work.FTS.EllExist.Closers.aesm_tailPrim_Ioi (fun t : ℝ => c t * t ^ (-p - 1))).mono_measure
        (Measure.restrict_mono Set.Ioo_subset_Ioi_self le_rfl)
    have h2 : AEStronglyMeasurable (fun z : ℝ => z ^ (2 * p - 4))
        (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
      (continuousOn_id.rpow_const (fun z hz => Or.inl (ne_of_gt hz.1))).aestronglyMeasurable
        measurableSet_Ioo
    exact h2.mul (h1.pow 2)
  exact (lintegral_ofReal_ne_top_iff_integrable hT_aesm
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
      exact mul_nonneg (Real.rpow_nonneg hz.1.le _) (sq_nonneg _))).mp hne

/-- **Near-zero weighted square bound for the growing Green branch.**

With `rgG2 α m c z = z^p * ∫_{Ioi z} c t * t^{-p-1} dt`, `p = rgP α m ≥ 8`, the function
`z ↦ (rgG2 α m c z)² / z⁴` is integrable on `(0,1)`.

HINT (verified by two reviewers).  For `z ∈ (0,1)` write `B z = ∫ t in Set.Ioi z, rgF2 α m c t`,
so `rgG2 α m c z = z^{p} * B z` and `rgG2 z / z² = z^{p-2} B z`.
* First `∫ t in Set.Ioi z, f2 = ∫ t in z..1, f2 t + C₁` with `C₁ = ∫ t in Set.Ioi 1, rgF2 α m c t`,
  a finite constant: `|C₁| ≤ (1/2)∫_1^∞ (c t)² + (1/2)∫_1^∞ t^{-2p-2}` using `hfar` and
  `integrableOn_Ioi_rpow_of_lt`.  The `C₁`-part contributes
  `C₁² ∫_0^1 z^{2p-4} dz = C₁²/(2p-3)` (as `2p - 4 ≥ 12 > -1`).
* For the first part: split `c t * t^{-p-1} = (c t * t^{-5/2}) * t^{-p+3/2}`, so
  Cauchy–Schwarz on `z..1` gives
  `(∫ t in z..1, c t * t^{-p-1})² ≤ (∫ t in z..1, (c t)² t^{-5}) * (∫ t in z..1, t^{-2p+3})`
  and `∫ t in z..1, t^{-2p+3} = (z^{-2p+4} - 1)/(2p-4) ≤ z^{-2p+4}/(2p-4)` (`2p-3 > 1`).
  Multiplying by `z^{2p-4}` cancels, giving
  `(z^{p-2} ∫ t in z..1, c t t^{-p-1})² ≤ (1/(2p-4)) * ∫ t in z..1, (c t)² t^{-5}`.
  Tonelli on the triangle `0 < z < t < 1` (`Work.FTS.PhiStar.Honesty.lintegral_Ioo_triangle`,
  with the roles of `F`/`G` interchanged) gives
  `∫_0^1 ∫_z^1 (c t)² t^{-5} dt dz = ∫_0^1 (c t)² t^{-5} * t dt = ∫_0^1 (c t)² t^{-4} dt < ∞`.

You must also check that `∫ t in Set.Ioi z, rgF2 α m c t` is an honest (non-junk) number for
`z ∈ (0,1)`: `f2 = c t t^{-p-1}` is integrable on `(z,1)` by Cauchy–Schwarz
`|c t| t^{-p-1} = (|c t|/t²) t^{1-p} ≤ (1/2)((c t)²/t⁴) + (1/2) t^{2-2p}` — note the last term
is NOT integrable on `(0,1)`, so use
`∫_z^1 |c| t^{-p-1} ≤ ‖c/t²‖_{L²(z,1)} * (∫_z^1 t^{2-2p})^{1/2}` instead
(`∫_z^1 t^{2-2p} = (z^{3-2p}-1)/(3-2p) < ∞` for `z > 0`).
Finally `∫ t in Set.Ioi z, f2 = ∫ t in z..1, f2 + ∫ t in Set.Ioi 1, f2` for `z ∈ (0,1)` by
`setIntegral_union` / `integral_add_compl` on the disjoint union
`Ioi z = Ioc z 1 ∪ Ioi 1` (or use `∫ t in Ioi 1, f2 = C₁`).
`AEStronglyMeasurable` of the target: `z ↦ ∫ t in Ioi z, f2` can be written as
`z ↦ C₁ + ∫ t in 1..z, f2 t`, a sum of a constant and a primitive, hence continuous on `(0,1)`. -/
theorem rgG2_sq_div_z4_Ioo {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.EllExist.rgG2 α m c z) ^ 2 / z ^ 4) (Set.Ioo 0 1) := by
  have hp8 : 8 ≤ Work.FTS.EllExist.rgP α m := Work.FTS.EllExist.rgP_ge hα hα4 hm
  have hp0 : 0 < Work.FTS.EllExist.rgP α m := by linarith
  have hp3 : 3 < Work.FTS.EllExist.rgP α m := by linarith
  have hkey := key_tail (p := Work.FTS.EllExist.rgP α m) hp0 hp3 hc hnear hfar
  refine hkey.congr_fun ?_ measurableSet_Ioo
  intro z hz
  have hz0 : 0 < z := hz.1
  simp only [Work.FTS.EllExist.rgG2, Work.FTS.EllExist.rgB, Work.FTS.EllExist.rgF2]
  have h1 : (z ^ Work.FTS.EllExist.rgP α m) ^ 2 = z ^ (2 * Work.FTS.EllExist.rgP α m) := by
    rw [sq, ← Real.rpow_add hz0]
    congr 1
    ring
  have h2 : (z ^ 4)⁻¹ = z ^ (-4 : ℝ) := by
    have h4 : z ^ (4 : ℝ) = z ^ 4 := Real.rpow_natCast z 4
    rw [← h4, ← Real.rpow_neg hz0.le (4 : ℝ)]
  have h3 : z ^ (2 * Work.FTS.EllExist.rgP α m) * z ^ (-4 : ℝ)
      = z ^ (2 * Work.FTS.EllExist.rgP α m - 4) := by
    have he : 2 * Work.FTS.EllExist.rgP α m + (-4) = 2 * Work.FTS.EllExist.rgP α m - 4 := by
      ring
    rw [← Real.rpow_add hz0, he]
  rw [mul_pow, div_eq_mul_inv, h1, h2, ← h3]
  ring

end Work.FTS.PhiStar.Honesty

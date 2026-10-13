import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.Spaces.sin_rpow_le_majorant_pi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set
open scoped Real

namespace Work.FTS.EllipticEst.TT

noncomputable section

/-- The constant produced by `lightInvBounds`.  It depends only on `a`:

`(π/4)^a · (1/(1-a) + max 1 (2^(1-a)/(1-a)))`.

The first summand bounds `∫_(0,θ) t^{-a}` and the second the reflected tail; the
`2^(1-a)/(1-a)` is `(π/2)^(1-a)/(1-a) · (4/π)^(1-a)` rearranged. -/
def lightC (a : ℝ) : ℝ :=
  (Real.pi / 4) ^ a * (1 / (1 - a) + max 1 ((2 : ℝ) ^ (1 - a) / (1 - a)))

theorem lightC_pos (a : ℝ) (_ha : 0 < a) (ha1 : a < 1) : 0 < lightC a := by
  have h1 : (0 : ℝ) < (Real.pi / 4) ^ a := Real.rpow_pos_of_pos (by positivity) a
  have h2 : (0 : ℝ) < 1 / (1 - a) := one_div_pos.mpr (by linarith)
  have h3 : (0 : ℝ) < max 1 ((2 : ℝ) ^ (1 - a) / (1 - a)) :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  rw [lightC]
  exact mul_pos h1 (by linarith)

/-- Change of variables `x ↦ c - x` for integrals over open intervals. -/
private lemma integral_Ioo_sub_left (f : ℝ → ℝ) (c a b : ℝ) (hab : a ≤ b) :
    ∫ x in Set.Ioo a b, f (c - x) = ∫ x in Set.Ioo (c - b) (c - a), f x := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo (x := a) (y := b) (f := fun x => f (c - x)),
    ← intervalIntegral.integral_of_le hab, intervalIntegral.integral_comp_sub_left f c,
    intervalIntegral.integral_of_le (by linarith : c - b ≤ c - a),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- `∫_(c,d) x^{-a} = (d^{1-a} - c^{1-a})/(1-a)` for `a < 1`. -/
private lemma integral_Ioo_rpow_neg (a c d : ℝ) (ha1 : a < 1) (hcd : c ≤ d) :
    ∫ x in Set.Ioo c d, x ^ (-a) = (d ^ (1 - a) - c ^ (1 - a)) / (1 - a) := by
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo (x := c) (y := d) (f := fun x => x ^ (-a)),
    ← intervalIntegral.integral_of_le hcd,
    integral_rpow (Or.inl (by linarith : -1 < (-a : ℝ))),
    show -a + 1 = 1 - a by ring]

/-- `∫_(0,θ) (π/2 - x)^{-a} = ((π/2)^{1-a} - (π/2 - θ)^{1-a})/(1-a)`. -/
private lemma integral_Ioo_pi_div_two_sub_rpow_neg (a θ : ℝ) (ha1 : a < 1) (hθ : 0 ≤ θ) :
    ∫ x in Set.Ioo (0 : ℝ) θ, (Real.pi / 2 - x) ^ (-a)
      = ((Real.pi / 2) ^ (1 - a) - (Real.pi / 2 - θ) ^ (1 - a)) / (1 - a) := by
  have h := integral_Ioo_sub_left (fun x : ℝ => x ^ (-a)) (Real.pi / 2) 0 θ hθ
  have h' : ∫ x in Set.Ioo (0 : ℝ) θ, (Real.pi / 2 - x) ^ (-a)
      = ∫ x in Set.Ioo (Real.pi / 2 - θ) (Real.pi / 2), x ^ (-a) := by
    simpa only [sub_zero] using h
  rw [h', integral_Ioo_rpow_neg a (Real.pi / 2 - θ) (Real.pi / 2) ha1
    (by linarith [Real.pi_pos])]

/-- `x ↦ x^{-a}` is integrable on `(c,d)` when `a < 1`. -/
private lemma integrableOn_rpow_neg_Ioo (a c d : ℝ) (ha1 : a < 1) (hcd : c ≤ d) :
    MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-a)) (Set.Ioo c d) := by
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le hcd]
  exact intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < (-a : ℝ))

/-- `x ↦ (π/2 - x)^{-a}` is integrable on `(c,d)`. -/
private lemma integrableOn_pi_div_two_sub_rpow_neg_Ioo (a c d : ℝ) (ha1 : a < 1) (hcd : c ≤ d) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (Real.pi / 2 - t) ^ (-a)) (Set.Ioo c d) := by
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le hcd]
  have h := (IntervalIntegrable.comp_sub_left_iff (f := fun u : ℝ => u ^ (-a)) (Real.pi / 2)
    (a := Real.pi / 2 - c) (b := Real.pi / 2 - d)).mpr
    (intervalIntegral.intervalIntegrable_rpow' (show -1 < (-a : ℝ) by linarith))
  simpa only [sub_sub_cancel] using h

/-- `t ↦ ((sin (2t))^a)^{-1}` is integrable on `(c,d)` for `0 ≤ c ≤ d ≤ π/2` and `0 < a < 1`. -/
private lemma integrableOn_sin_two_inv_rpow (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) (hd : d ≤ Real.pi / 2) :
    MeasureTheory.IntegrableOn (fun t : ℝ => ((Real.sin (2 * t)) ^ a)⁻¹) (Set.Ioo c d) := by
  have hP := integrableOn_rpow_neg_Ioo a c d ha1 hcd
  have hQ := integrableOn_pi_div_two_sub_rpow_neg_Ioo a c d ha1 hcd
  have hM : MeasureTheory.Integrable
      (fun t : ℝ => (Real.pi / 4) ^ a * (t ^ (-a) + (Real.pi / 2 - t) ^ (-a)))
      (MeasureTheory.volume.restrict (Set.Ioo c d)) :=
    MeasureTheory.Integrable.const_mul (MeasureTheory.Integrable.add hP hQ) _
  refine MeasureTheory.Integrable.mono' hM ?_ ?_
  · exact (by fun_prop : Measurable fun t : ℝ => ((Real.sin (2 * t)) ^ a)⁻¹).aestronglyMeasurable
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => ?_)
    have ht0 : 0 ≤ Real.sin (2 * t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1, hc])
        (by linarith [ht.2, hd, Real.pi_pos])
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.rpow_nonneg ht0 a)),
      ← Real.rpow_neg ht0 a]
    exact Work.Spaces.sin_rpow_le_majorant_pi a t ha
      ⟨by linarith [ht.1, hc], by linarith [ht.2, hd]⟩

/-- Reflection identity: if `F (π/2 - t) = F t` then the integral over `(θ, π/2)` equals the
integral over `(0, π/2 - θ)`. -/
private lemma integral_Ioo_pi_div_two_reflect (F : ℝ → ℝ)
    (hF : ∀ t : ℝ, F (Real.pi / 2 - t) = F t) {θ : ℝ} (_hθ : 0 ≤ θ)
    (hθ2 : θ ≤ Real.pi / 2) :
    ∫ t in Set.Ioo θ (Real.pi / 2), F t = ∫ t in Set.Ioo (0 : ℝ) (Real.pi / 2 - θ), F t := by
  have h1 : ∫ t in Set.Ioo θ (Real.pi / 2), F t
      = ∫ t in Set.Ioo θ (Real.pi / 2), F (Real.pi / 2 - t) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioo (fun t _ => (hF t).symm)
  rw [h1, integral_Ioo_sub_left F (Real.pi / 2) θ (Real.pi / 2) hθ2]
  simp only [sub_self]

/-- The main estimate: `∫_(0,θ) (sin 2t)^{-a} ≤ lightC a · θ^{1-a}`. -/
private lemma integral_Ioo_sin_two_inv_rpow_le (a θ : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    ∫ t in Set.Ioo (0 : ℝ) θ, ((Real.sin (2 * t)) ^ a)⁻¹ ≤ lightC a * θ ^ (1 - a) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hδ : 0 < Real.pi / 2 - θ := by linarith [hθ.2]
  have h1a : 0 < 1 - a := by linarith
  have hθp : 0 < θ ^ (1 - a) := Real.rpow_pos_of_pos hθ.1 _
  -- the pointwise majorant
  have hFle : ∀ t ∈ Set.Ioo (0 : ℝ) θ,
      ((Real.sin (2 * t)) ^ a)⁻¹ ≤ (Real.pi / 4) ^ a * (t ^ (-a) + (Real.pi / 2 - t) ^ (-a)) := by
    intro t ht
    have ht0 : 0 ≤ Real.sin (2 * t) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [ht.1]) (by linarith [ht.2, hθ.2, hpi])
    rw [← Real.rpow_neg ht0 a]
    exact Work.Spaces.sin_rpow_le_majorant_pi a t ha
      ⟨le_of_lt ht.1, by linarith [ht.2, hθ.2]⟩
  -- integrability
  have hPint : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-a)) (Set.Ioo (0 : ℝ) θ) :=
    integrableOn_rpow_neg_Ioo a 0 θ ha1 (le_of_lt hθ.1)
  have hQint : MeasureTheory.IntegrableOn (fun t : ℝ => (Real.pi / 2 - t) ^ (-a))
      (Set.Ioo (0 : ℝ) θ) :=
    integrableOn_pi_div_two_sub_rpow_neg_Ioo a 0 θ ha1 (le_of_lt hθ.1)
  have hMint : MeasureTheory.Integrable
      (fun t : ℝ => (Real.pi / 4) ^ a * (t ^ (-a) + (Real.pi / 2 - t) ^ (-a)))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) θ)) :=
    MeasureTheory.Integrable.const_mul (MeasureTheory.Integrable.add hPint hQint) _
  -- step 1: compare with the majorant
  have hstep1 : ∫ t in Set.Ioo (0 : ℝ) θ, ((Real.sin (2 * t)) ^ a)⁻¹
      ≤ ∫ t in Set.Ioo (0 : ℝ) θ,
          (Real.pi / 4) ^ a * (t ^ (-a) + (Real.pi / 2 - t) ^ (-a)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hMint ?_
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun t ht => ?_)
      exact inv_nonneg.mpr (Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
        (by linarith [ht.1]) (by linarith [ht.2, hθ.2, hpi])) a)
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hFle
  -- step 2: the value of the majorant integral
  have hMval : ∫ t in Set.Ioo (0 : ℝ) θ,
        (Real.pi / 4) ^ a * (t ^ (-a) + (Real.pi / 2 - t) ^ (-a))
      = (Real.pi / 4) ^ a * (θ ^ (1 - a) / (1 - a)
          + ((Real.pi / 2) ^ (1 - a) - (Real.pi / 2 - θ) ^ (1 - a)) / (1 - a)) := by
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (f := fun t : ℝ => t ^ (-a))
        (g := fun t : ℝ => (Real.pi / 2 - t) ^ (-a)) hPint hQint,
      integral_Ioo_rpow_neg a 0 θ ha1 (le_of_lt hθ.1),
      Real.zero_rpow (show (1 : ℝ) - a ≠ 0 by linarith),
      integral_Ioo_pi_div_two_sub_rpow_neg a θ ha1 (le_of_lt hθ.1)]
    ring
  -- step 3: the reflected part
  have hQle : ((Real.pi / 2) ^ (1 - a) - (Real.pi / 2 - θ) ^ (1 - a)) / (1 - a)
      ≤ max 1 ((2 : ℝ) ^ (1 - a) / (1 - a)) * θ ^ (1 - a) := by
    rcases le_total θ (Real.pi / 4) with hcase | hcase
    · -- small `θ`: the reflected part is dominated by the `t^{-a}` part
      have hpt : ∀ t ∈ Set.Ioo (0 : ℝ) θ, (Real.pi / 2 - t) ^ (-a) ≤ t ^ (-a) := by
        intro t ht
        exact Real.rpow_le_rpow_of_nonpos ht.1 (by linarith [ht.2, hcase])
          (by linarith : (-a : ℝ) ≤ 0)
      have hmono := MeasureTheory.setIntegral_mono_on hQint hPint measurableSet_Ioo hpt
      have hPval : ∫ t in Set.Ioo (0 : ℝ) θ, t ^ (-a) = θ ^ (1 - a) / (1 - a) := by
        rw [integral_Ioo_rpow_neg a 0 θ ha1 (le_of_lt hθ.1),
          Real.zero_rpow (show (1 : ℝ) - a ≠ 0 by linarith)]
        ring
      have hQval := integral_Ioo_pi_div_two_sub_rpow_neg a θ ha1 (le_of_lt hθ.1)
      rw [hQval, hPval] at hmono
      have hb : θ ^ (1 - a) / (1 - a)
          ≤ max 1 ((2 : ℝ) ^ (1 - a) / (1 - a)) * θ ^ (1 - a) := by
        have hA : (1 : ℝ) ≤ (2 : ℝ) ^ (1 - a) := by
          simpa only [Real.one_rpow] using
            Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 2)
              (le_of_lt h1a)
        have hB : (1 : ℝ) / (1 - a) ≤ (2 : ℝ) ^ (1 - a) / (1 - a) :=
          div_le_div_of_nonneg_right hA (le_of_lt h1a)
        have hC : (2 : ℝ) ^ (1 - a) / (1 - a) ≤ max 1 ((2 : ℝ) ^ (1 - a) / (1 - a)) :=
          le_max_right _ _
        have hD : θ ^ (1 - a) / (1 - a) = (1 / (1 - a)) * θ ^ (1 - a) := by ring
        have hE : (1 / (1 - a)) * θ ^ (1 - a)
            ≤ (max 1 ((2 : ℝ) ^ (1 - a) / (1 - a))) * θ ^ (1 - a) :=
          mul_le_mul_of_nonneg_right (hB.trans hC) (le_of_lt hθp)
        linarith [hD, hE]
      exact hmono.trans hb
    · -- large `θ`: the reflected part is bounded by its total mass
      have h2 : 0 ≤ (Real.pi / 2 - θ) ^ (1 - a) := Real.rpow_nonneg (by linarith) _
      have h1step : ((Real.pi / 2) ^ (1 - a) - (Real.pi / 2 - θ) ^ (1 - a)) / (1 - a)
          ≤ (Real.pi / 2) ^ (1 - a) / (1 - a) := by
        have he : ((Real.pi / 2) ^ (1 - a) - (Real.pi / 2 - θ) ^ (1 - a)) / (1 - a)
            = (Real.pi / 2) ^ (1 - a) / (1 - a)
              - (Real.pi / 2 - θ) ^ (1 - a) / (1 - a) := by ring
        have h3 : 0 ≤ (Real.pi / 2 - θ) ^ (1 - a) / (1 - a) := div_nonneg h2 (le_of_lt h1a)
        linarith [he, h3]
      have h2step : (Real.pi / 2) ^ (1 - a) / (1 - a)
          ≤ (2 : ℝ) ^ (1 - a) * θ ^ (1 - a) / (1 - a) := by
        have hA : (Real.pi / 2) ^ (1 - a) ≤ (2 * θ) ^ (1 - a) :=
          Real.rpow_le_rpow (by positivity) (by linarith [hcase]) (le_of_lt h1a)
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hθ.1)] at hA
        exact div_le_div_of_nonneg_right hA (le_of_lt h1a)
      have h3step : (2 : ℝ) ^ (1 - a) * θ ^ (1 - a) / (1 - a)
          ≤ max 1 ((2 : ℝ) ^ (1 - a) / (1 - a)) * θ ^ (1 - a) := by
        have := mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) ((2 : ℝ) ^ (1 - a) / (1 - a)))
          (le_of_lt hθp)
        rwa [div_mul_eq_mul_div] at this
      exact h1step.trans (h2step.trans h3step)
  -- step 4: assemble
  have hfin : (Real.pi / 4) ^ a * (θ ^ (1 - a) / (1 - a)
        + ((Real.pi / 2) ^ (1 - a) - (Real.pi / 2 - θ) ^ (1 - a)) / (1 - a))
      ≤ lightC a * θ ^ (1 - a) := by
    have hsum : θ ^ (1 - a) / (1 - a)
          + ((Real.pi / 2) ^ (1 - a) - (Real.pi / 2 - θ) ^ (1 - a)) / (1 - a)
        ≤ (1 / (1 - a) + max 1 ((2 : ℝ) ^ (1 - a) / (1 - a))) * θ ^ (1 - a) := by
      have h1 : θ ^ (1 - a) / (1 - a) = (1 / (1 - a)) * θ ^ (1 - a) := by ring
      have h2 : (1 / (1 - a)) * θ ^ (1 - a)
          ≤ (1 / (1 - a) + max 1 ((2 : ℝ) ^ (1 - a) / (1 - a))) * θ ^ (1 - a) := by
        refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hθp)
        exact le_add_of_nonneg_right (lt_of_lt_of_le one_pos (le_max_left _ _)).le
      linarith [h1, h2, hQle]
    calc (Real.pi / 4) ^ a * (θ ^ (1 - a) / (1 - a)
            + ((Real.pi / 2) ^ (1 - a) - (Real.pi / 2 - θ) ^ (1 - a)) / (1 - a))
        ≤ (Real.pi / 4) ^ a
            * ((1 / (1 - a) + max 1 ((2 : ℝ) ^ (1 - a) / (1 - a))) * θ ^ (1 - a)) :=
          mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (by positivity) _)
      _ = lightC a * θ ^ (1 - a) := by rw [lightC]; ring
  exact hstep1.trans (hMval.le.trans hfin)

theorem lightInvBounds (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ C : ℝ, 0 < C ∧
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      MeasureTheory.IntegrableOn (fun t : ℝ => ((Real.sin (2 * t)) ^ a)⁻¹) (Set.Ioo 0 θ)) ∧
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) θ))
        (fun t : ℝ => ((Real.sin (2 * t)) ^ a)⁻¹) ≤ C * θ ^ (1 - a)) ∧
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      MeasureTheory.IntegrableOn (fun t : ℝ => ((Real.sin (2 * t)) ^ a)⁻¹) (Set.Ioo θ (Real.pi / 2))) ∧
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      MeasureTheory.integral (MeasureTheory.volume.restrict (Set.Ioo θ (Real.pi / 2)))
        (fun t : ℝ => ((Real.sin (2 * t)) ^ a)⁻¹) ≤ C * (Real.pi / 2 - θ) ^ (1 - a)) := by
  refine ⟨lightC a, lightC_pos a ha ha1, ?_, ?_, ?_, ?_⟩
  · intro θ hθ
    exact integrableOn_sin_two_inv_rpow a ha ha1 (le_refl 0) (le_of_lt hθ.1) (le_of_lt hθ.2)
  · intro θ hθ
    exact integral_Ioo_sin_two_inv_rpow_le a θ ha ha1 hθ
  · intro θ hθ
    exact integrableOn_sin_two_inv_rpow a ha ha1 (le_of_lt hθ.1) (le_of_lt hθ.2) (le_refl _)
  · intro θ hθ
    have hsym : ∀ t : ℝ,
        ((Real.sin (2 * (Real.pi / 2 - t))) ^ a)⁻¹ = ((Real.sin (2 * t)) ^ a)⁻¹ := by
      intro t
      rw [show 2 * (Real.pi / 2 - t) = Real.pi - 2 * t by ring, Real.sin_pi_sub]
    have hreflect := integral_Ioo_pi_div_two_reflect
      (fun t : ℝ => ((Real.sin (2 * t)) ^ a)⁻¹) (fun t => hsym t) (le_of_lt hθ.1) (le_of_lt hθ.2)
    rw [hreflect]
    exact integral_Ioo_sin_two_inv_rpow_le a (Real.pi / 2 - θ) ha ha1
      ⟨by linarith [hθ.2], by linarith [hθ.1]⟩

end

end Work.FTS.EllipticEst.TT

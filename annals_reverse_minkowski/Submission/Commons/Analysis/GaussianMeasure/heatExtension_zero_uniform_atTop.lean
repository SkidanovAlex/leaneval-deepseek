import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Commons.Analysis.GaussianMeasure.gaussian_tail_upper
import Submission.Commons.Analysis.GaussianMeasure.gaussian_total_mass_one

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Commons.Analysis.GaussianMeasure

/-- For every `c > 0` there is `M ≥ 1` with `exp (-π M²) ≤ c`. -/
lemma exists_one_le_exp_neg_pi_sq_le (c : ℝ) (hc : 0 < c) :
    ∃ M : ℝ, 1 ≤ M ∧ Real.exp (-Real.pi * M ^ 2) ≤ c := by
  refine ⟨Real.sqrt (max 1 (-Real.log c / Real.pi)), ?_, ?_⟩
  · rw [Real.one_le_sqrt]
    exact le_max_left _ _
  · have hmaxnn : 0 ≤ max 1 (-Real.log c / Real.pi) :=
      le_trans zero_le_one (le_max_left _ _)
    have hsq : (Real.sqrt (max 1 (-Real.log c / Real.pi))) ^ 2
        = max 1 (-Real.log c / Real.pi) := Real.sq_sqrt hmaxnn
    have hle : -Real.log c ≤ Real.pi * (Real.sqrt (max 1 (-Real.log c / Real.pi))) ^ 2 := by
      rw [hsq]
      have h1 := mul_le_mul_of_nonneg_left (le_max_right (1:ℝ) (-Real.log c / Real.pi))
        Real.pi_pos.le
      have h2 : Real.pi * (-Real.log c / Real.pi) = -Real.log c := by
        field_simp
      linarith
    have hfin : Real.exp (-Real.pi * (Real.sqrt (max 1 (-Real.log c / Real.pi))) ^ 2)
        ≤ Real.exp (Real.log c) := by
      apply Real.exp_le_exp.mpr
      linarith
    rwa [Real.exp_log hc] at hfin

/-- Two-sided Gaussian tail: for `M > 0`,
`∫_{|z| > M} exp (-π z²) ≤ exp (-π M²) / (π M)`. -/
lemma gaussian_abs_tail_le (M : ℝ) (hM : 0 < M) :
    (∫ z in {z : ℝ | M < |z|}, Real.exp (-Real.pi * z ^ 2))
      ≤ Real.exp (-Real.pi * M ^ 2) / (Real.pi * M) := by
  set F : ℝ → ℝ := fun y => if M < y then Real.exp (-Real.pi * y ^ 2) else 0 with hF
  have hmeas : MeasurableSet {z : ℝ | M < |z|} := by measurability
  have hcomp : ∀ z : ℝ, F |z| = ({z : ℝ | M < |z|}.indicator fun z => Real.exp (-Real.pi * z ^ 2)) z := by
    intro z
    rw [hF, Set.indicator_apply]
    by_cases h : M < |z|
    · simp only [h, if_true, Set.mem_ofPred_eq]
      rw [sq_abs]
    · simp only [Set.mem_ofPred_eq, h, if_false]
  have h1 : (∫ z, F |z|) = ∫ z in {z : ℝ | M < |z|}, Real.exp (-Real.pi * z ^ 2) := by
    have heq : (∫ z, F |z|)
        = ∫ z, ({z : ℝ | M < |z|}.indicator fun z => Real.exp (-Real.pi * z ^ 2)) z :=
      integral_congr_ae (Eventually.of_forall (fun z => hcomp z))
    rw [heq, integral_indicator hmeas]
  have h2 : (∫ x in Set.Ioi (0:ℝ), F x) = ∫ x in Set.Ioi M, Real.exp (-Real.pi * x ^ 2) := by
    rw [← integral_indicator (s := Set.Ioi (0:ℝ)) (f := F) measurableSet_Ioi,
      ← integral_indicator (s := Set.Ioi M)
        (f := fun x => Real.exp (-Real.pi * x ^ 2)) measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with x
    rw [Set.indicator_apply, Set.indicator_apply, hF]
    simp only [Set.mem_Ioi]
    by_cases h : M < x
    · rw [if_pos (lt_trans hM h), if_pos h]
    · rw [if_neg h]
      by_cases h0 : 0 < x
      · rw [if_pos h0]
      · rw [if_neg h0]
  have key : (∫ z in {z : ℝ | M < |z|}, Real.exp (-Real.pi * z ^ 2))
      = 2 * ∫ x in Set.Ioi M, Real.exp (-Real.pi * x ^ 2) := by
    rw [← h1, integral_comp_abs (f := F), h2]
  have htail := Commons.Analysis.GaussianMeasure.gaussian_tail_upper M hM
  calc (∫ z in {z : ℝ | M < |z|}, Real.exp (-Real.pi * z ^ 2))
      = 2 * ∫ x in Set.Ioi M, Real.exp (-Real.pi * x ^ 2) := key
    _ ≤ 2 * (Real.exp (-Real.pi * M ^ 2) / (2 * Real.pi * M)) :=
        mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = Real.exp (-Real.pi * M ^ 2) / (Real.pi * M) := by
        field_simp

theorem heatExtension_zero_uniform_atTop
    (f : ℝ → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (hfinf : ∀ ε > 0, ∃ R : ℝ, ∀ x, R ≤ |x| → |f x| ≤ ε) :
    ∀ T > 0, ∀ ε > 0, ∃ R : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : ℝ, R ≤ x →
      |∫ z : ℝ, f (x + Real.sqrt t * z) * Real.exp (-Real.pi * z ^ 2)| ≤ ε := by
  intro T hT ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨R0, hR0⟩ := hfinf (ε / 2) hε2
  obtain ⟨M, hM1, hMexp⟩ := exists_one_le_exp_neg_pi_sq_le (ε / 2 * Real.pi) (by positivity)
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have htail : (∫ z in {z : ℝ | M < |z|}, Real.exp (-Real.pi * z ^ 2)) ≤ ε / 2 := by
    refine le_trans (gaussian_abs_tail_le M hMpos) ?_
    have hπM : 0 < Real.pi * M := by positivity
    have h3 : Real.pi ≤ Real.pi * M := by
      simpa using mul_le_mul_of_nonneg_left hM1 Real.pi_pos.le
    have h2 : (ε / 2) * Real.pi ≤ (ε / 2) * (Real.pi * M) :=
      mul_le_mul_of_nonneg_left h3 hε2.le
    rw [div_le_iff₀ hπM]
    linarith
  refine ⟨max R0 0 + Real.sqrt T * M, ?_⟩
  intro t ht x hx
  set s : ℝ := Real.sqrt t with hs
  have ht0 : 0 ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hs0 : 0 ≤ s := Real.sqrt_nonneg t
  have hsle : s ≤ Real.sqrt T := Real.sqrt_le_sqrt htT
  have hR1le : R0 ≤ max R0 0 := le_max_left _ _
  have hR1nn : 0 ≤ max R0 0 := le_max_right _ _
  have hG : Integrable (fun z : ℝ => Real.exp (-Real.pi * z ^ 2)) :=
    integrable_exp_neg_mul_sq Real.pi_pos
  have hmeas : MeasurableSet {z : ℝ | M < |z|} := by measurability
  have hmaj : Integrable (fun z : ℝ => (ε / 2) * Real.exp (-Real.pi * z ^ 2)
      + Set.indicator {z : ℝ | M < |z|} (fun z => Real.exp (-Real.pi * z ^ 2)) z) :=
    (hG.const_mul _).add (hG.indicator hmeas)
  have hb : ∀ z : ℝ, ‖f (x + s * z) * Real.exp (-Real.pi * z ^ 2)‖
      ≤ (ε / 2) * Real.exp (-Real.pi * z ^ 2)
        + Set.indicator {z : ℝ | M < |z|} (fun z => Real.exp (-Real.pi * z ^ 2)) z := by
    intro z
    have hGnn : 0 ≤ Real.exp (-Real.pi * z ^ 2) := Real.exp_nonneg _
    have hnorm : ‖f (x + s * z) * Real.exp (-Real.pi * z ^ 2)‖
        = |f (x + s * z)| * Real.exp (-Real.pi * z ^ 2) := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hGnn]
    rw [hnorm, Set.indicator_apply]
    by_cases hz : z ∈ {z : ℝ | M < |z|}
    · rw [if_pos hz]
      have hz' : M < |z| := hz
      have hf1 : |f (x + s * z)| ≤ 1 := hf _
      have h1 : |f (x + s * z)| * Real.exp (-Real.pi * z ^ 2) ≤ Real.exp (-Real.pi * z ^ 2) := by
        calc |f (x + s * z)| * Real.exp (-Real.pi * z ^ 2)
            ≤ 1 * Real.exp (-Real.pi * z ^ 2) := mul_le_mul_of_nonneg_right hf1 hGnn
          _ = Real.exp (-Real.pi * z ^ 2) := one_mul _
      have h2 : (0:ℝ) ≤ (ε / 2) * Real.exp (-Real.pi * z ^ 2) := mul_nonneg hε2.le hGnn
      linarith
    · rw [if_neg hz]
      have hzle : |z| ≤ M := not_lt.mp (fun hh => hz (by simpa using hh))
      have habs : |s * z| ≤ Real.sqrt T * M := by
        rw [abs_mul, abs_of_nonneg hs0]
        exact mul_le_mul hsle hzle (abs_nonneg z) (Real.sqrt_nonneg T)
      have harg : max R0 0 ≤ x + s * z := by
        have h1 := neg_le_of_abs_le habs
        have hx' : max R0 0 + Real.sqrt T * M ≤ x := hx
        linarith
      have hf2 : |f (x + s * z)| ≤ ε / 2 := by
        apply hR0
        have hpos : 0 ≤ x + s * z := le_trans hR1nn harg
        rw [abs_of_nonneg hpos]
        linarith
      simpa using mul_le_mul_of_nonneg_right hf2 hGnn
  have hstep := norm_integral_le_of_norm_le hmaj (Eventually.of_forall hb)
  have hsplit : (∫ z, (ε / 2) * Real.exp (-Real.pi * z ^ 2)
        + Set.indicator {z : ℝ | M < |z|} (fun z => Real.exp (-Real.pi * z ^ 2)) z)
      = ε / 2 * (∫ z, Real.exp (-Real.pi * z ^ 2))
        + ∫ z in {z : ℝ | M < |z|}, Real.exp (-Real.pi * z ^ 2) := by
    rw [integral_add (hG.const_mul _) (hG.indicator hmeas), integral_const_mul,
      integral_indicator hmeas]
  have hmass : (∫ z : ℝ, Real.exp (-Real.pi * z ^ 2)) = 1 := by
    have h := Commons.Analysis.GaussianMeasure.gaussian_total_mass_one ℝ
    simpa only [Real.norm_eq_abs, sq_abs] using h
  rw [hsplit, hmass, mul_one] at hstep
  have hfin : ‖∫ z : ℝ, f (x + s * z) * Real.exp (-Real.pi * z ^ 2)‖ ≤ ε := by
    linarith [hstep, htail]
  simpa only [Real.norm_eq_abs] using hfin

end Commons.Analysis.GaussianMeasure
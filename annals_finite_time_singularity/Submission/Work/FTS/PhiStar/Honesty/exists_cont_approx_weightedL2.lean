import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UrysohnsLemma
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Honesty.sq_integrableOn_Ioi_of
import Submission.Work.FTS.PhiStar.Honesty.near_integral_abs_lt
import Submission.Work.FTS.PhiStar.Honesty.tail_integral_tendsto_zero
import Submission.Work.FTS.PhiStar.Honesty.approx_on_Icc_boundedContinuous
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_sub_div_Ioo
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_sub_Ioi
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_mul_w_sq_of
import Submission.Work.FTS.PhiStar.Honesty.tendsto_sq_mul_w_sq_zero
import Submission.Work.FTS.PhiStar.Honesty.tendsto_sq_weighted_of_tendsto_difference
import Submission.Work.FTS.PhiStar.Honesty.near_bound
import Submission.Work.FTS.PhiStar.Honesty.far_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter

noncomputable section

/-! ## Elementary helper lemmas used by the main construction -/

/-- **A continuous cutoff.**  There is a continuous `χ : ℝ → ℝ` with values in `[0,1]` which
vanishes on `(-∞, δ] ∪ [N, ∞)` and equals `1` on `[2δ, N/2]` (the last condition being vacuous
if `2δ > N/2`). -/
theorem exists_continuous_cutoff {δ N : ℝ} (hδ : 0 < δ) (hN : 0 < N) :
    ∃ χ : ℝ → ℝ, Continuous χ ∧ (∀ t : ℝ, χ t ∈ Set.Icc 0 1) ∧
      (∀ t : ℝ, t ≤ δ → χ t = 0) ∧ (∀ t : ℝ, N ≤ t → χ t = 0) ∧
      (∀ t : ℝ, 2 * δ ≤ t → t ≤ N / 2 → χ t = 1) := by
  have hdisj : Disjoint (Set.Iic δ ∪ Set.Ici N) (Set.Icc (2 * δ) (N / 2)) := by
    rw [Set.disjoint_left]
    rintro t (ht | ht) ht'
    · simp only [Set.mem_Iic] at ht
      simp only [Set.mem_Icc] at ht'
      linarith [ht, ht'.1]
    · simp only [Set.mem_Ici] at ht
      simp only [Set.mem_Icc] at ht'
      have hN0 : (0:ℝ) < N := hN
      linarith [ht, ht'.2, hN0]
  obtain ⟨f, hf0, hf1, hfr⟩ :=
    exists_continuous_zero_one_of_isClosed (isClosed_Iic.union isClosed_Ici) isClosed_Icc hdisj
  exact ⟨fun t => f t, f.continuous, fun t => hfr t,
    fun t ht => hf0 (Or.inl ht), fun t ht => hf0 (Or.inr ht),
    fun t ht1 ht2 => hf1 ⟨ht1, ht2⟩⟩

/-- `(c t)^2` is integrable on any compact interval contained in `(0, ∞)`. -/
theorem integrableOn_sq_Icc_of {c : ℝ → ℝ} {α β : ℝ} (hα : 0 < α)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Icc α β) :=
  (sq_integrableOn_Ioi_of (by linarith : (0:ℝ) < α / 2) hnear hfar).mono_set
    (fun t ht => by simp only [Set.mem_Ioi]; linarith [ht.1])

/-- The cross term `u · c · w²` is integrable as soon as `u²w²` and `c²w²` are, provided
`u` and `c` are a.e.-measurable. -/
theorem integrableOn_cross_mul_w_sq {c u : ℝ → ℝ}
    (hu : AEMeasurable u) (hc : AEMeasurable c)
    (hcw : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (Set.Ioi 0))
    (huw : MeasureTheory.IntegrableOn (fun t : ℝ => (u t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (Set.Ioi 0)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => u t * c t * (Work.Spaces.w t) ^ 2)
      (Set.Ioi 0) := by
  have hw2 : Measurable (fun t : ℝ => (Work.Spaces.w t) ^ 2) := by
    unfold Work.Spaces.w; fun_prop
  refine Integrable.mono' (huw.add hcw) ?_ ?_
  · have h1 : AEMeasurable (fun t : ℝ => u t * c t * (Work.Spaces.w t) ^ 2) :=
      (hu.mul hc).mul hw2.aemeasurable
    exact (h1.mono_measure Measure.restrict_le_self).aestronglyMeasurable
  · filter_upwards with t
    have hw : (0:ℝ) ≤ (Work.Spaces.w t) ^ 2 := sq_nonneg _
    have habs : |u t * c t| ≤ (u t) ^ 2 + (c t) ^ 2 := by
      have h := sq_nonneg (|u t| - |c t|)
      rw [abs_mul]
      nlinarith [abs_nonneg (u t), abs_nonneg (c t), sq_abs (u t), sq_abs (c t)]
    show |u t * c t * (Work.Spaces.w t) ^ 2|
      ≤ (u t) ^ 2 * (Work.Spaces.w t) ^ 2 + (c t) ^ 2 * (Work.Spaces.w t) ^ 2
    calc |u t * c t * (Work.Spaces.w t) ^ 2| = |u t * c t| * (Work.Spaces.w t) ^ 2 := by
          rw [abs_mul, abs_of_nonneg hw]
      _ ≤ ((u t) ^ 2 + (c t) ^ 2) * (Work.Spaces.w t) ^ 2 :=
          mul_le_mul_of_nonneg_right habs hw
      _ = (u t) ^ 2 * (Work.Spaces.w t) ^ 2 + (c t) ^ 2 * (Work.Spaces.w t) ^ 2 := by ring

theorem exists_cont_approx_weightedL2 {c : ℝ → ℝ}
    (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∃ c_ : ℕ → ℝ → ℝ,
      (∀ n, ContinuousOn (c_ n) (Set.Ioi 0)) ∧
      (∀ n, ∃ a b : ℝ, 0 < a ∧ ∀ t : ℝ, t ∉ Set.Icc a b → c_ n t = 0) ∧
      (∀ n, MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2 / t ^ 4)
        (Set.Ioo 0 1)) ∧
      (∀ n, MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2) (Set.Ioi 1)) ∧
      Filter.Tendsto (fun n => ∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 / t ^ 4)
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => ∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2)
        Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun n => ∫ t in Set.Ioi (0:ℝ), (c_ n t) ^ 2 * (Work.Spaces.w t) ^ 2)
        Filter.atTop (nhds (∫ t in Set.Ioi (0:ℝ), (c t) ^ 2 * (Work.Spaces.w t) ^ 2)) := by
  classical
  -- ## Step 1: for every `ε > 0` there is a compactly supported continuous `φ` with
  -- `∫_{(0,1)} (φ-c)²/t⁴ ≤ ε` and `∫_{(1,∞)} (φ-c)² ≤ ε`.
  have hmain : ∀ ε : ℝ, 0 < ε → ∃ φ : ℝ → ℝ,
      Continuous φ ∧ (∃ a b : ℝ, 0 < a ∧ ∀ t : ℝ, t ∉ Set.Icc a b → φ t = 0) ∧
      MeasureTheory.IntegrableOn (fun t : ℝ => (φ t - c t) ^ 2 / t ^ 4) (Set.Ioo 0 1) ∧
      MeasureTheory.IntegrableOn (fun t : ℝ => (φ t - c t) ^ 2) (Set.Ioi 1) ∧
      (∫ t in Set.Ioo (0:ℝ) 1, (φ t - c t) ^ 2 / t ^ 4) ≤ ε ∧
      (∫ t in Set.Ioi (1:ℝ), (φ t - c t) ^ 2) ≤ ε := by
    intro ε hε
    -- an error budget
    set T : ℝ := ε / 1000 with hTdef
    have hTpos : 0 < T := by rw [hTdef]; linarith
    -- (1) a small radius where the near weight has small mass
    obtain ⟨δ, hδpos, hδlt1, hδint⟩ := near_integral_abs_lt hnear hTpos
    set r : ℝ := δ / 2 with hrdef
    have hrpos : 0 < r := by rw [hrdef]; linarith
    have hr1 : 2 * r ≤ 1 := by rw [hrdef]; linarith
    have h2r : 2 * r = δ := by rw [hrdef]; ring
    have hη : ∫ t in Set.Ioo 0 (2 * r), (c t) ^ 2 / t ^ 4 ≤ T := by
      have h3 : ∫ t in Set.Ioo (0:ℝ) (2 * r), |(c t) ^ 2 / t ^ 4| < T := by
        rw [h2r]
        exact hδint
      have heq : ∫ t in Set.Ioo (0:ℝ) (2 * r), |(c t) ^ 2 / t ^ 4|
          = ∫ t in Set.Ioo (0:ℝ) (2 * r), (c t) ^ 2 / t ^ 4 :=
        setIntegral_congr_fun measurableSet_Ioo
          (fun t ht => abs_of_nonneg (div_nonneg (sq_nonneg _) (pow_pos ht.1 4).le))
      rw [← heq]
      exact le_of_lt h3
    -- (2) a large truncation radius
    have hev1 : ∀ᶠ n : ℕ in Filter.atTop, (∫ t in Set.Ioi (n : ℝ), (c t) ^ 2) < T :=
      (tail_integral_tendsto_zero hfar).eventually_lt tendsto_const_nhds hTpos
    have hev2 : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ n := eventually_ge_atTop 1
    obtain ⟨n, hnT, hn1⟩ := (hev1.and hev2).exists
    have hn1' : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn1
    set N : ℝ := 2 * (n : ℝ) with hNdef
    have hNpos : 0 < N := by rw [hNdef]; linarith
    have hN2 : 2 ≤ N := by rw [hNdef]; linarith
    have hNhalf : N / 2 = (n : ℝ) := by rw [hNdef]; ring
    have hη₃ : ∫ t in Set.Ioi (N / 2), (c t) ^ 2 ≤ T := by
      rw [hNhalf]; exact le_of_lt hnT
    -- (3) the approximation accuracy
    have hK1 : (1:ℝ) ≤ (r⁻¹) ^ 4 := by
      have h1 : r ≤ 1 / 2 := by linarith
      have h2 : (2:ℝ) ≤ r⁻¹ := by
        rw [le_inv_comm₀ (by norm_num : (0:ℝ) < 2) hrpos]
        rw [show (2:ℝ)⁻¹ = 1 / 2 by norm_num]
        linarith
      calc (1:ℝ) ≤ 2 ^ 4 := by norm_num
        _ ≤ (r⁻¹) ^ 4 := pow_le_pow_left₀ (by norm_num) h2 4
    set ε₁ : ℝ := T / (400 * (r⁻¹) ^ 4) with hε₁def
    have hε₁pos : 0 < ε₁ := by rw [hε₁def]; positivity
    have hε₁le : ε₁ ≤ T / 400 := by
      rw [hε₁def]
      exact div_le_div_of_nonneg_left hTpos.le (by norm_num) (by nlinarith [hK1])
    have hKne : (r⁻¹) ^ 4 ≠ 0 := by positivity
    -- (4) the compactly supported continuous approximation on `[r/2, 2N]`
    have hcIcc : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2)
        (Set.Icc (r / 2) (2 * N)) :=
      integrableOn_sq_Icc_of (by linarith) hnear hfar
    obtain ⟨G, hGcont, _hGbdd, hGint0, hGapp0⟩ :=
      approx_on_Icc_boundedContinuous (f := c) (a := r / 2) (b := 2 * N) hc hcIcc hε₁pos
    have hGint : MeasureTheory.IntegrableOn (fun t : ℝ => (G t - c t) ^ 2)
        (Set.Icc (r / 2) (2 * N)) :=
      hGint0.congr_fun (fun t _ => by ring) measurableSet_Icc
    have hGapp : ∫ t in Set.Icc (r / 2) (2 * N), (G t - c t) ^ 2 ≤ ε₁ := by
      rw [setIntegral_congr_fun measurableSet_Icc
        (fun t _ => by ring : ∀ t ∈ Set.Icc (r / 2) (2 * N),
          (G t - c t) ^ 2 = (c t - G t) ^ 2)]
      exact hGapp0
    -- (5) the cutoff
    obtain ⟨χ, hχcont, hχmem, hχ0, hχN, hχ1⟩ :=
      exists_continuous_cutoff (δ := r / 2) (N := N) (by linarith) hNpos
    have hχ1' : ∀ t : ℝ, r ≤ t → t ≤ N / 2 → χ t = 1 := by
      intro t ht1 ht2
      refine hχ1 t ?_ ht2
      rw [show 2 * (r / 2) = r by ring]
      exact ht1
    have hχb : ∀ t : ℝ, |χ t| ≤ 1 := by
      intro t
      have h := hχmem t
      rw [Set.mem_Icc] at h
      rw [abs_le]
      constructor <;> linarith [h.1, h.2]
    -- (6) the approximant and its properties
    have hφcont : Continuous (fun t : ℝ => χ t * G t) := hχcont.mul hGcont
    have hφsupp' : ∀ t : ℝ, t ∉ Set.Icc (r / 2) N → χ t * G t = 0 := by
      intro t ht
      have hcases : t < r / 2 ∨ N < t := by
        by_contra h
        rw [not_or] at h
        exact ht ⟨not_lt.mp h.1, not_lt.mp h.2⟩
      rcases hcases with h | h
      · rw [hχ0 t (le_of_lt h), zero_mul]
      · rw [hχN t (le_of_lt h), zero_mul]
    have hint1 : MeasureTheory.IntegrableOn
        (fun t : ℝ => (χ t * G t - c t) ^ 2 / t ^ 4) (Set.Ioo 0 1) :=
      integrableOn_sq_sub_div_Ioo (a := r / 2) (b := N) (by linarith) hc hφcont hφsupp' hnear
    have hint2 : MeasureTheory.IntegrableOn (fun t : ℝ => (χ t * G t - c t) ^ 2)
        (Set.Ioi 1) :=
      integrableOn_sq_sub_Ioi (a := r / 2) (b := N) hc hφcont hφsupp' hfar
    -- (7) the two estimates
    have hnb := near_bound (c := c) (G := G) (χ := χ) (r := r) (N := N) (ε₁ := ε₁) (η := T)
      hrpos hr1 hN2 hχ0 hχ1' hχb hnear hcIcc hη hGint hGapp hint1
    have hnearε : ∫ t in Set.Ioo (0:ℝ) 1, (χ t * G t - c t) ^ 2 / t ^ 4 ≤ ε := by
      refine le_trans hnb ?_
      have h65 : 65 * (r⁻¹) ^ 4 * ε₁ = 65 * T / 400 := by
        rw [hε₁def]
        field_simp
      rw [h65, hTdef]
      nlinarith
    have hfb := far_bound (c := c) (G := G) (χ := χ) (r := r) (N := N) (ε₁ := ε₁) (η := T)
      hrpos hr1 hN2 hχN hχ1' hχb hfar hη₃ hGint hGapp hint2
    have hfarε : ∫ t in Set.Ioi (1:ℝ), (χ t * G t - c t) ^ 2 ≤ ε := by
      refine le_trans hfb ?_
      have h5 : 5 * ε₁ ≤ 5 * (T / 400) := mul_le_mul_of_nonneg_left hε₁le (by norm_num)
      have h2 : (5:ℝ) * (T / 400) + 7 * T ≤ ε := by rw [hTdef]; linarith
      linarith
    exact ⟨fun t => χ t * G t, hφcont,
      ⟨r / 2, N, by linarith, hφsupp'⟩, hint1, hint2, hnearε, hfarε⟩
  -- ## Step 2: the sequence
  let c_ : ℕ → ℝ → ℝ :=
    fun n => Classical.choose (hmain (1 / ((n : ℝ) + 1)) (by positivity))
  have hspec : ∀ n : ℕ,
      Continuous (c_ n) ∧ (∃ a b : ℝ, 0 < a ∧ ∀ t : ℝ, t ∉ Set.Icc a b → c_ n t = 0) ∧
      MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2 / t ^ 4) (Set.Ioo 0 1) ∧
      MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2) (Set.Ioi 1) ∧
      (∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 / t ^ 4) ≤ 1 / ((n : ℝ) + 1) ∧
      (∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2) ≤ 1 / ((n : ℝ) + 1) :=
    fun n => Classical.choose_spec (hmain (1 / ((n : ℝ) + 1)) (by positivity))
  have hlim1 : Filter.Tendsto
      (fun n : ℕ => ∫ t in Set.Ioo (0:ℝ) 1, (c_ n t - c t) ^ 2 / t ^ 4)
      Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ?_ ?_
    · filter_upwards with n
      exact setIntegral_nonneg measurableSet_Ioo
        (fun t ht => div_nonneg (sq_nonneg _) (pow_pos ht.1 4).le)
    · filter_upwards with n
      exact (hspec n).2.2.2.2.1
  have hlim2 : Filter.Tendsto
      (fun n : ℕ => ∫ t in Set.Ioi (1:ℝ), (c_ n t - c t) ^ 2) Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ?_ ?_
    · filter_upwards with n
      exact setIntegral_nonneg measurableSet_Ioi (fun t _ => sq_nonneg _)
    · filter_upwards with n
      exact (hspec n).2.2.2.2.2
  refine ⟨c_, fun n => (hspec n).1.continuousOn, fun n => (hspec n).2.1,
    fun n => (hspec n).2.2.1, fun n => (hspec n).2.2.2.1, hlim1, hlim2, ?_⟩
  -- ## Step 3: the weighted `L²` norm converges
  have hcw : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 * (Work.Spaces.w t) ^ 2)
      (Set.Ioi 0) :=
    integrableOn_sq_mul_w_sq_of (u := c) hnear hfar
  have hintw : ∀ n : ℕ, MeasureTheory.IntegrableOn
      (fun t : ℝ => (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioi 0) :=
    fun n => integrableOn_sq_mul_w_sq_of (u := fun t : ℝ => c_ n t - c t)
      ((hspec n).2.2.1) ((hspec n).2.2.2.1)
  have hcross : ∀ n : ℕ, MeasureTheory.IntegrableOn
      (fun t : ℝ => (c_ n t - c t) * c t * (Work.Spaces.w t) ^ 2) (Set.Ioi 0) :=
    fun n => integrableOn_cross_mul_w_sq (u := fun t : ℝ => c_ n t - c t)
      (((hspec n).1.aemeasurable).sub hc) hc hcw (hintw n)
  have hconv : Filter.Tendsto
      (fun n : ℕ => ∫ t in Set.Ioi (0:ℝ), (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
      Filter.atTop (nhds 0) :=
    tendsto_sq_mul_w_sq_zero (fun n => (hspec n).2.2.1) (fun n => (hspec n).2.2.2.1)
      hlim1 hlim2
  exact tendsto_sq_weighted_of_tendsto_difference hcw hintw hcross hconv

end

end Work.FTS.PhiStar.Honesty

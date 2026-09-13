import Mathlib
import Submission.Commons.Analysis.Inequalities.pow_five_div_bound
import Submission.Commons.Measure.Integral.integral_ge_of_lipschitz_subball

namespace Commons.Measure.Lebesgue

open MeasureTheory Metric Set Filter Function
open scoped BigOperators ENNReal Topology

open Commons.Analysis.Inequalities in
theorem sup_le_of_average_and_slope {h : EuclideanSpace ℝ (Fin 4) → ℝ}
    {x₀ : EuclideanSpace ℝ (Fin 4)} {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    (hL1 : ∀ ε > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ),
        (∫ y in Metric.ball x₀ r, |h y|)
          / (MeasureTheory.volume (Metric.ball x₀ r)).toReal ≤ ε * r ^ 2)
    (hpoint : ∀ r : ℝ, 0 < r → 2 * r < R →
        ∀ y ∈ Metric.closedBall x₀ r, ∀ z ∈ Metric.closedBall x₀ r, y ≠ z →
        |h y - h z| / dist y z ≤ A / r * ((∫ w in Metric.ball x₀ (2 * r), |h w|)
          / (MeasureTheory.volume (Metric.ball x₀ (2 * r))).toReal) + A * r) :
    ∀ ε > 0, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ y ∈ Metric.ball x₀ (r / 2), |h y| ≤ ε * r ^ 2 := by
  intro ε hε
  let m : ℝ → ℝ := fun r => (∫ y in Metric.ball x₀ r, |h y|)
      / (MeasureTheory.volume (Metric.ball x₀ r)).toReal
  let c : ℝ := min (ε / 32) (ε ^ 5 / (512 * (A ^ 2 + 1) ^ 2))
  have hcpos : 0 < c := lt_min (by positivity) (by positivity)
  have hc_le_left : c ≤ ε / 32 := min_le_left _ _
  have hc_le_right : c ≤ ε ^ 5 / (512 * (A ^ 2 + 1) ^ 2) := min_le_right _ _
  -- Extract the two "smallness" radii from `hL1`.
  obtain ⟨b2, hb2pos, hb2⟩ : ∃ b, 0 < b ∧ ∀ r ∈ Ioo 0 b, m r ≤ (c / 2) * r ^ 2 :=
    (nhdsGT_basis (0 : ℝ)).eventually_iff.mp (hL1 (c / 2) (by positivity))
  obtain ⟨b3, hb3pos, hb3⟩ : ∃ b, 0 < b ∧ ∀ r ∈ Ioo 0 b, m r ≤ (1 / 4) * r ^ 2 :=
    (nhdsGT_basis (0 : ℝ)).eventually_iff.mp (hL1 (1 / 4) (by norm_num))
  let δ : ℝ := min (R / 2) (min b2 (b3 / 2))
  have hδpos : 0 < δ := lt_min (by positivity) (lt_min hb2pos (by positivity))
  have hδ_R : δ ≤ R / 2 := min_le_left _ _
  have hδ_b2 : δ ≤ b2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_b3 : δ ≤ b3 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  refine Filter.mem_of_superset (Ioo_mem_nhdsGT hδpos) ?_
  intro r hr
  rw [mem_Ioo] at hr
  obtain ⟨hrpos, hrδ⟩ := hr
  have hrR : 2 * r < R := by
    have : r < R / 2 := lt_of_lt_of_le hrδ hδ_R
    linarith
  have hsmall2 : m r ≤ (c / 2) * r ^ 2 := hb2 r ⟨hrpos, lt_of_lt_of_le hrδ hδ_b2⟩
  have hsmall4 : m (2 * r) ≤ r ^ 2 := by
    have h2r : 2 * r ∈ Ioo (0 : ℝ) b3 := ⟨by linarith, by linarith [hrδ, hδ_b3]⟩
    have h := hb3 (2 * r) h2r
    have heq : (1 / 4 : ℝ) * (2 * r) ^ 2 = r ^ 2 := by ring
    rwa [heq] at h
  intro y hy
  by_contra hcon
  rw [not_le] at hcon
  -- The Lipschitz constant on `closedBall x₀ r`.
  let K : ℝ := A / r * m (2 * r) + A * r
  -- Lipschitz on the closed ball, hence continuity/integrability and the required hypotheses.
  have hlip : ∀ z ∈ closedBall x₀ r, ∀ w ∈ closedBall x₀ r, |h z - h w| ≤ K * dist z w := by
    intro z hz w hw
    rcases eq_or_ne z w with rfl | hne
    · simp
    · have hp := hpoint r hrpos hrR z hz w hw hne
      rw [div_le_iff₀ (dist_pos.mpr hne)] at hp
      simpa only [Real.dist_eq] using hp
  have hKnonneg : 0 ≤ K := by
    have hAdiv : 0 ≤ A / r := div_nonneg hA hrpos.le
    have hm2nn : 0 ≤ m (2 * r) := by
      have : m (2 * r) = (∫ y in Metric.ball x₀ (2 * r), |h y|)
          / (MeasureTheory.volume (Metric.ball x₀ (2 * r))).toReal := rfl
      rw [this]
      exact div_nonneg (integral_nonneg (fun z => abs_nonneg _)) ENNReal.toReal_nonneg
    have hAr : 0 ≤ A * r := mul_nonneg hA hrpos.le
    nlinarith [mul_nonneg hAdiv hm2nn, hAr]
  have hK_le : K ≤ 2 * A * r := by
    have hAdiv : 0 ≤ A / r := div_nonneg hA hrpos.le
    have hmul : A / r * m (2 * r) ≤ A / r * r ^ 2 := mul_le_mul_of_nonneg_left hsmall4 hAdiv
    have heq : A / r * r ^ 2 = A * r := by field_simp
    rw [heq] at hmul
    have : K = A / r * m (2 * r) + A * r := rfl
    rw [this]; nlinarith [hmul]
  have hu_pos : 0 < |h y| := by
    have : 0 < ε * r ^ 2 := mul_pos hε (pow_pos hrpos 2)
    linarith [hcon]
  -- `|h|` is bounded below by `|h y|/2` on a small ball; this is the core estimate.
  have hIntLemma : ∀ s : ℝ, 0 < s → s ≤ r / 2 → s * K ≤ |h y| / 2 →
      (|h y| / 2) * (s / r) ^ 4 ≤ m r := by
    intro s hs hs_half hsK
    exact Commons.Measure.Integral.integral_ge_of_lipschitz_subball
      hrpos hs hs_half hy hKnonneg hlip hsK
  have key : c * r ^ 2 ≤ m r := by
    by_cases hcase : K * r ≤ |h y|
    · -- Case A: `K r ≤ |h y|`; test ball of radius `r/2`.
      have hs : (0 : ℝ) < r / 2 := by linarith
      have hsK : (r / 2) * K ≤ |h y| / 2 := by nlinarith [hcase]
      have hb := hIntLemma (r / 2) hs (le_refl _) hsK
      have hbase : (r / 2) / r = (1 : ℝ) / 2 := by field_simp
      have hratio : ((r / 2) / r) ^ 4 = ((1 : ℝ) / 2) ^ 4 := by rw [hbase]
      rw [hratio] at hb
      have hnorm : ((1 : ℝ) / 2) ^ 4 = 1 / 16 := by norm_num
      rw [hnorm] at hb
      have h1 : c * r ^ 2 ≤ (ε / 32) * r ^ 2 := by nlinarith [hc_le_left, sq_nonneg r]
      have h2 : (ε / 32) * r ^ 2 ≤ (|h y| / 2) * (1 / 16) := by
        nlinarith [le_of_lt hcon, sq_nonneg r]
      linarith [h1, h2, hb]
    · -- Case B: `|h y| < K r`; test ball of radius `|h y|/(2K)`.
      have hcase : |h y| < K * r := lt_of_not_ge hcase
      have hKpos : 0 < K := by nlinarith [hcase, hu_pos, hrpos]
      have hs : 0 < |h y| / (2 * K) := by positivity
      have hsK : (|h y| / (2 * K)) * K = |h y| / 2 := by
        field_simp
      refine le_trans ?_ (hIntLemma (|h y| / (2 * K)) hs ?_ (le_of_eq hsK))
      · -- arithmetic: `c r² ≤ (|h y|/2) * ((|h y|/(2K))/r)^4`
        have heq : (|h y| / 2) * ((|h y| / (2 * K)) / r) ^ 4
            = |h y| ^ 5 / (32 * K ^ 4 * r ^ 4) := by
          field_simp
          ring
        rw [heq]
        exact pow_five_div_bound hA hε hrpos hKpos hc_le_right hK_le (le_of_lt hcon)
      · -- `s ≤ r/2`
        have h1 : |h y| / (2 * K) ≤ r / 2 := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)]
          nlinarith [hcase]
        exact h1
  have := le_trans key hsmall2
  nlinarith [this, hcpos, pow_pos hrpos 2]

end Commons.Measure.Lebesgue

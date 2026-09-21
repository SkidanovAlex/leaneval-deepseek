import Mathlib
import Submission.Work.OddCurve.LowSlope.anchorPhiData_eq_ballData
import Submission.Work.OddCurve.LowSlope.anchorPsiData_eq_zero
import Submission.Work.OddCurve.LowSlope.step3_anchor_data
import Submission.Work.OddCurve.Free.deltaCapAndSupport
import Submission.Work.OddVolterra.Free.FreeSetup

/-!
# The anchor's Radon data are the ball's below the slope `4/5`

This is the *closed-left-endpoint* form of the junction
`Work.OddCurve.LowSlope.anchorData_junction_cap`.  There the equality
`radonPhi n ρ c = ballPhiData n c ∧ radonPsi n ρ c = 0` is proved on the *open* interval

`c ∈ ((√(1+(4/5)²))⁻¹, (√(1+(7/10)²))⁻¹)`,

i.e. for slopes `s = √(1-c²)/c ∈ (7/10, 4/5)`.  Here we need it on
`[(√(1+(4/5)²))⁻¹, 4/5)`, i.e. for slopes `s ∈ (3/4, 4/5]` — the left endpoint
`c = (√(1+(4/5)²))⁻¹`, i.e. `s = 4/5`, included.

The point of the endpoint is that `4/5 = 1 - 2τ` is the *left edge of the support window* of the
bump: `IsSmallFlatBumpClass` provides both `Function.support h ⊆ Ioo (1-2τ) (1-τ) = Ioo (4/5) (9/10)`
and an `η > 0` with `h = 0` on `[4/5, 4/5+η)`.  Hence `h` vanishes — with all its derivatives —
on the *closed* window `[7/10, 4/5+η)`, which strictly contains the slope `4/5`.  The junction
`Work.OddCurve.LowSlope.anchorPhiData_junction` is then applied to a sliding interval
`[a,b] = [(7/10+s)/2, 4/5+δ/2]` (with `δ = min η (1/5)`) which contains the slope `s` for *every*
`s ≤ 4/5`, the endpoint `s = 4/5` included.
-/

namespace Work.OddVolterra.Free

theorem anchorDatum_eq_ball_of_le_four_fifths (n : ℕ) (hn : 1 ≤ n) {ε : ℝ} {h X Y ρ : ℝ → ℝ}
    (hbump : Work.OddVolterra.Free.IsSmallFlatBumpClass n (2 * n + 2) ε h)
    (hne : h ≠ 0)
    (H : Work.OddEnvelope.IsEnvelopeCurve h X Y)
    (hA : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentA n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s =
        Work.OddCurve.refConst n / Real.sqrt (1 + s ^ 2))
    (hB : ∀ s : ℝ, 1 - 3 * Work.OddVolterra.tau < s → s ≤ 1 →
      Work.OddCurve.momentB n h X Y (Work.OddEnvelope.envelopeProfile h X Y) s = 0)
    (hanc : Work.OddVolterra.Free.IsAnchorRadial h X Y ρ) :
    ∀ c : ℝ, (Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹ ≤ c → c < 4 / 5 →
      Work.OddCurve.LowSlope.radonPhi n ρ c = Work.OddCurve.LowSlope.ballPhiData n c ∧
      Work.OddCurve.LowSlope.radonPsi n ρ c = 0 := by
  obtain ⟨_hcont, hsupp, _hsmall, hηex⟩ := hbump
  obtain ⟨η, hηpos, hη⟩ := hηex
  have hτ1 : (1 : ℝ) - Work.OddVolterra.tau = 9 / 10 := by norm_num [Work.OddVolterra.tau]
  have hτ2 : (1 : ℝ) - 2 * Work.OddVolterra.tau = 4 / 5 := by norm_num [Work.OddVolterra.tau]
  have hτ3 : (1 : ℝ) - 3 * Work.OddVolterra.tau = 7 / 10 := by norm_num [Work.OddVolterra.tau]
  have hsupp4 : Function.support h ⊆ Set.Ioo ((4 : ℝ) / 5) (9 / 10) := by
    intro x hx
    have h := hsupp hx
    rw [Set.mem_Ioo, hτ2, hτ1] at h
    exact h
  intro c hcge hclt
  have hcpos : 0 < c := by
    have h1 : (0 : ℝ) < (Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹ :=
      inv_pos.mpr (Real.sqrt_pos.mpr (by norm_num))
    linarith
  have hclt1 : c ≤ 1 := by linarith
  set s : ℝ := Real.sqrt (1 - c ^ 2) / c with hsdef
  have hsnonneg : 0 ≤ s := by
    rw [hsdef]; exact div_nonneg (Real.sqrt_nonneg _) hcpos.le
  have hc2pos : 0 < c ^ 2 := by positivity
  have hsq : s ^ 2 * c ^ 2 = 1 - c ^ 2 := by
    rw [hsdef]; exact Work.OddCurve.LowSlope.sqrt_one_sub_sq_div_sq_mul hcpos hclt1
  have hcs : c ^ 2 * (1 + s ^ 2) = 1 := by nlinarith [hsq]
  -- The slope `s` attached to `c` lies in `(3/4, 4/5]`.
  have hs_le : s ≤ 4 / 5 := by
    have hid : ((Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹) ^ 2 * (1 + (4 / 5 : ℝ) ^ 2) = 1 := by
      rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 + (4 / 5 : ℝ) ^ 2),
        inv_mul_cancel₀ (by norm_num : (1 + (4 / 5 : ℝ) ^ 2) ≠ 0)]
    have hcsq : ((Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹) ^ 2 ≤ c ^ 2 :=
      pow_le_pow_left₀ (by positivity) hcge 2
    have h1 : 1 ≤ c ^ 2 * (1 + (4 / 5 : ℝ) ^ 2) := by
      calc (1 : ℝ) = ((Real.sqrt (1 + (4 / 5 : ℝ) ^ 2))⁻¹) ^ 2 *
            (1 + (4 / 5 : ℝ) ^ 2) := hid.symm
        _ ≤ c ^ 2 * (1 + (4 / 5 : ℝ) ^ 2) := mul_le_mul_of_nonneg_right hcsq (by norm_num)
    have h3 : s ^ 2 * c ^ 2 ≤ (4 / 5 : ℝ) ^ 2 * c ^ 2 := by
      rw [hsq]; nlinarith [h1]
    have h2 : s ^ 2 ≤ (4 / 5 : ℝ) ^ 2 := (mul_le_mul_iff_of_pos_right hc2pos).mp h3
    have h4 : |s| ≤ |(4 : ℝ) / 5| := (sq_le_sq).mp h2
    rwa [abs_of_nonneg hsnonneg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4 / 5)] at h4
  have hs_gt : 3 / 4 < s := by
    have hc2lt : c ^ 2 < (4 / 5 : ℝ) ^ 2 := by nlinarith [hclt, hcpos]
    have hkey : (3 / 4 : ℝ) ^ 2 < s ^ 2 := by
      have h3 : (3 / 4 : ℝ) ^ 2 * c ^ 2 < 1 - c ^ 2 := by nlinarith [hc2lt]
      rw [← hsq] at h3
      exact (mul_lt_mul_iff_of_pos_right hc2pos).mp h3
    have h4 : |(3 : ℝ) / 4| < |s| := (sq_lt_sq).mp hkey
    rwa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4), abs_of_nonneg hsnonneg] at h4
  -- The sliding window `[a,b]` on which the bump vanishes together with its derivative.
  set δ : ℝ := min η (1 / 5) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact lt_min hηpos (by norm_num)
  have hδη : δ ≤ η := by rw [hδdef]; exact min_le_left _ _
  have hδ15 : δ ≤ 1 / 5 := by rw [hδdef]; exact min_le_right _ _
  set a : ℝ := (7 / 10 + s) / 2 with hadef
  set b : ℝ := 4 / 5 + δ / 2 with hbdef
  have ha_gt : (7 : ℝ) / 10 < a := by rw [hadef]; linarith [hs_gt]
  have ha_pos : 0 < a := by linarith
  have ha_lt_s : a < s := by rw [hadef]; linarith [hs_gt]
  have hab : a ≤ b := by rw [hadef, hbdef]; linarith [hs_le, hδpos]
  have hb_gt_s : s < b := by rw [hbdef]; linarith [hs_le, hδpos]
  have hb_ltη : b < 4 / 5 + η := by rw [hbdef]; linarith [hδη, hδpos]
  have hb_lt1 : b < 1 := by rw [hbdef]; linarith [hδ15, hδpos]
  have hzero : ∀ u ∈ Set.Icc a b, h u = 0 := by
    intro u hu
    rcases le_or_gt ((4 : ℝ) / 5) u with h | h
    · refine hη u ?_ ?_
      · rw [hτ2]; exact h
      · rw [hτ2]; linarith [hu.2, hb_ltη]
    · by_contra hne'
      have hmem := hsupp4 (Function.mem_support.mpr hne')
      exact absurd hmem.1 (not_lt.mpr (le_of_lt h))
  have hder0 : ∀ u ∈ Set.Icc a b, deriv h u = 0 := by
    intro u hu
    refine Work.OddCurve.LowSlope.deriv_eq_zero_of_eqOn_Ioo
      (show (7 : ℝ) / 10 < u by linarith [hu.1, ha_gt])
      (show u < 4 / 5 + η by linarith [hu.2, hb_ltη]) ?_
    intro x hx
    rcases le_or_gt ((4 : ℝ) / 5) x with h | h
    · refine hη x ?_ ?_
      · rw [hτ2]; exact h
      · rw [hτ2]; linarith [hx.2]
    · by_contra hne'
      have hmem := hsupp4 (Function.mem_support.mpr hne')
      exact absurd hmem.1 (not_lt.mpr (le_of_lt h))
  have hAb : ∀ u ∈ Set.Icc a b, Work.OddCurve.momentA n h X Y
      (Work.OddEnvelope.envelopeProfile h X Y) u =
        Work.OddCurve.refConst n / Real.sqrt (1 + u ^ 2) := by
    intro u hu
    refine hA u ?_ ?_
    · rw [hτ3]; linarith [hu.1, ha_gt]
    · linarith [hu.2, hb_lt1]
  have hBb : ∀ u ∈ Set.Icc a b, Work.OddCurve.momentB n h X Y
      (Work.OddEnvelope.envelopeProfile h X Y) u = 0 := by
    intro u hu
    refine hB u ?_ ?_
    · rw [hτ3]; linarith [hu.1, ha_gt]
    · linarith [hu.2, hb_lt1]
  have hcb : 1 < c ^ 2 * (1 + b ^ 2) := by
    have hbs : s ^ 2 < b ^ 2 := pow_lt_pow_left₀ hb_gt_s hsnonneg (by norm_num)
    nlinarith [hcs, hbs, hc2pos]
  have hca : c ^ 2 * (1 + a ^ 2) < 1 := by
    have has : a ^ 2 < s ^ 2 := pow_lt_pow_left₀ ha_lt_s ha_pos.le (by norm_num)
    nlinarith [hcs, has, hc2pos]
  have hρpos : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, 0 < ρ u := hanc.1
  have hρsm : ContDiffOn ℝ 1 ρ (Set.Ioo (-1 : ℝ) 1) := hanc.2.1.of_le (by simp)
  have hρmono : StrictMonoOn (fun u : ℝ => ρ u * u) (Set.Ioo (-1 : ℝ) 1) := hanc.2.2.1
  have hgraph : ∀ u ∈ Set.Ioo (-1 : ℝ) 1, ρ u * Real.sqrt (1 - u ^ 2) =
      Work.OddEnvelope.envelopeProfile h X Y (ρ u * u) := hanc.2.2.2.1
  exact ⟨Work.OddCurve.LowSlope.anchorPhiData_junction n hn H hρpos hρsm hρmono hgraph
      ha_pos hab hcpos hclt1 hzero hder0 hAb hBb hcb hca,
    Work.OddCurve.LowSlope.anchorPsiData_junction n hn H hρpos hρsm hρmono hgraph
      ha_pos hab hcpos hclt1 hzero hder0 hBb hcb hca⟩

end Work.OddVolterra.Free

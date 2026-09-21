import Mathlib
import Submission.Work.OddRadon.Abel

/-!
# The exponent-lowering recursion `T_α G' = 2α c T_{α-1} G`, direct proof

Self-contained proof of `HasDerivAt (abelTrans α G) (2 α c * abelTrans (α-1) G c) c` for `G` of
class `C¹` on `[0,1]`, `α > 0` and `c ∈ (0,1)`, following the route
* substitution `s = c t`,
* differentiation under the integral sign,
* an integration-by-parts identity for the kernel `(1-t²)^α`.

This duplicates (independently) `Submission.Work.OddRadon.hasDerivAt_abelTrans`; it is used as a
self-contained fallback by `Submission.Work.OddRadon.abelReduceIter_abelTrans`.
-/

noncomputable section

open MeasureTheory Set Interval Function Filter
open scoped Topology

namespace Work.OddRadon

namespace AbelDirect

/-- The (possibly singular) weight `(1-t²)^p` is interval integrable on `[0,1]` for `p > -1`. -/
lemma intervalIntegrable_one_sub_sq_rpow {p : ℝ} (hp : -1 < p) :
    IntervalIntegrable (fun t : ℝ => (1 - t ^ 2) ^ p) volume (0:ℝ) 1 := by
  have h1 : IntervalIntegrable (fun t : ℝ => (1 - t) ^ p) volume (0:ℝ) 1 := by
    have hbase : IntervalIntegrable (fun u : ℝ => u ^ p) volume (0:ℝ) 1 :=
      intervalIntegral.intervalIntegrable_rpow' hp
    have h2 := hbase.comp_sub_left 1
    simpa using h2.symm
  have hcont : ContinuousOn (fun t : ℝ => (1 + t) ^ p) (Set.uIcc (0:ℝ) 1) := by
    apply ContinuousOn.rpow
    · exact continuousOn_const.add continuousOn_id
    · exact continuousOn_const
    · intro x hx
      left
      have hx1 : (0:ℝ) ≤ x := by rw [Set.uIcc_of_le zero_le_one] at hx; exact hx.1
      linarith
  have h3 : IntervalIntegrable (fun t : ℝ => (1 - t) ^ p * (1 + t) ^ p) volume (0:ℝ) 1 :=
    h1.mul_continuousOn hcont
  refine h3.congr fun t ht => ?_
  rw [Set.uIoc_of_le zero_le_one] at ht
  have htn : (0:ℝ) ≤ 1 - t := by linarith [ht.2]
  have htp : (0:ℝ) ≤ 1 + t := by linarith [ht.1]
  rw [← Real.mul_rpow htn htp]
  ring_nf

/-- **The substitution `s = c t` in the forward Abel transform.** For `c > 0` and any `G`, `α`,
`T_α G c = c^(2α+1) ∫_0^1 G(ct)(1-t²)^α dt`. -/
lemma abelTrans_eq_integral_comp_mul (α : ℝ) (G : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    abelTrans α G c = c ^ (2*α+1) * ∫ t in (0:ℝ)..1, G (c*t) * (1 - t^2)^α := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have key : ∫ x in (0:ℝ)..c, G x * (c^2 - x^2)^α
      = c * ∫ t in (0:ℝ)..1, G (c*t) * (c^2 - (c*t)^2)^α := by
    have hthis := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := 1)
      (fun s : ℝ => G s * (c^2 - s^2)^α) hc0
    simp only [smul_eq_mul, mul_zero, mul_one] at hthis
    rw [hthis, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  rw [abelTrans, key]
  have hpt : Set.EqOn (fun t : ℝ => G (c*t) * (c^2-(c*t)^2)^α)
                      (fun t : ℝ => c^(2*α) * (G (c*t) * (1-t^2)^α)) (Set.uIcc 0 1) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    have h1 : (0:ℝ) ≤ 1 - t^2 := by nlinarith [ht.1, ht.2]
    have h2 : c^2 - (c*t)^2 = c^2 * (1 - t^2) := by ring
    have h3 : (c^2)^α = c^(2*α) := by
      rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt hc) 2 α]
    change G (c*t) * (c^2-(c*t)^2)^α = c^(2*α) * (G (c*t) * (1-t^2)^α)
    rw [h2, Real.mul_rpow (by positivity) h1, h3]
    ring
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul]
  have hpow : c ^ (2*α+1) = c * c ^ (2*α) := by
    rw [show (2:ℝ)*α + 1 = 1 + 2*α by ring, Real.rpow_add hc, Real.rpow_one]
  rw [hpow]
  ring

/-- **Differentiation under the integral sign** for the substituted Abel integral: the derivative
in `c` of `∫_0^1 G(x t)(1-t²)^α dt` is `∫_0^1 (deriv G)(c t) t (1-t²)^α dt`. -/
lemma hasDerivAt_integral_rpow_mul_comp {α : ℝ} (hα : 0 < α) {G : ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G (Set.Icc 0 1)) {c : ℝ} (hc : c ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (fun x : ℝ => ∫ t in (0:ℝ)..1, G (x*t) * (1-t^2)^α)
      (∫ t in (0:ℝ)..1, t * deriv G (c*t) * (1-t^2)^α) c := by
  have hGcont : ContinuousOn G (Set.Icc 0 1) := hG.continuousOn
  have hderiv_cont : ContinuousOn (derivWithin G (Set.Icc 0 1)) (Set.Icc 0 1) :=
    hG.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hderiv_cont
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, zero_le_one⟩)
  have hGdiff : DifferentiableOn ℝ G (Set.Icc 0 1) := hG.differentiableOn (by norm_num)
  have hG_at : ∀ y ∈ Set.Ioo (0:ℝ) 1, HasDerivAt G (deriv G y) y := by
    intro y hy
    exact ((hGdiff y ⟨hy.1.le, hy.2.le⟩).differentiableAt (Icc_mem_nhds hy.1 hy.2)).hasDerivAt
  have hs : Set.Ioo (c/2) 1 ∈ 𝓝 c := Ioo_mem_nhds (by linarith [hc.1]) hc.2
  have mono_uIoc : Set.uIoc (0:ℝ) 1 ⊆ Set.uIcc (0:ℝ) 1 := by
    rw [Set.uIoc_of_le zero_le_one, Set.uIcc_of_le zero_le_one]; exact Ioc_subset_Icc_self
  have hpow_cont : ContinuousOn (fun t : ℝ => (1-t^2)^α) (Set.uIcc (0:ℝ) 1) := by
    apply ContinuousOn.rpow
    · exact continuousOn_const.sub (continuousOn_id.pow 2)
    · exact continuousOn_const
    · intro t ht; right; exact hα
  have hcont_F : ∀ x ∈ Set.Ioo (c/2) 1,
      ContinuousOn (fun t : ℝ => G (x*t) * (1-t^2)^α) (Set.uIcc (0:ℝ) 1) := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt (lt_trans (by linarith [hc.1]) hx.1)
    have hx1 : x ≤ 1 := le_of_lt hx.2
    have hcomp : ContinuousOn (fun t : ℝ => x*t) (Set.uIcc (0:ℝ) 1) :=
      (continuous_const.mul continuous_id).continuousOn
    have hmaps : Set.MapsTo (fun t : ℝ => x*t) (Set.uIcc (0:ℝ) 1) (Set.Icc 0 1) := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      exact ⟨mul_nonneg hx0 ht.1, by nlinarith [ht.2, hx0, hx1]⟩
    exact (hGcont.comp hcomp hmaps).mul hpow_cont
  have hcont_F' : ∀ x ∈ Set.Ioo (c/2) 1,
      ContinuousOn (fun t : ℝ => t * derivWithin G (Set.Icc 0 1) (x*t) * (1-t^2)^α)
        (Set.uIcc (0:ℝ) 1) := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt (lt_trans (by linarith [hc.1]) hx.1)
    have hx1 : x ≤ 1 := le_of_lt hx.2
    have hcomp : ContinuousOn (fun t : ℝ => x*t) (Set.uIcc (0:ℝ) 1) :=
      (continuous_const.mul continuous_id).continuousOn
    have hmaps : Set.MapsTo (fun t : ℝ => x*t) (Set.uIcc (0:ℝ) 1) (Set.Icc 0 1) := by
      intro t ht
      rw [Set.uIcc_of_le zero_le_one] at ht
      exact ⟨mul_nonneg hx0 ht.1, by nlinarith [ht.2, hx0, hx1]⟩
    exact (continuousOn_id.mul (hderiv_cont.comp hcomp hmaps)).mul hpow_cont
  have hkey := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0:ℝ)) (b := 1)
    (F := fun x t => G (x*t) * (1-t^2)^α)
    (F' := fun x t => t * derivWithin G (Set.Icc 0 1) (x*t) * (1-t^2)^α)
    (x₀ := c) (s := Set.Ioo (c/2) 1) (bound := fun _ => M)
    hs ?_ ?_ ?_ ?_ ?_ ?_
  · obtain ⟨hint, hderiv⟩ := hkey
    have hval : (∫ t in (0:ℝ)..1, t * derivWithin G (Set.Icc 0 1) (c*t) * (1-t^2)^α)
        = ∫ t in (0:ℝ)..1, t * deriv G (c*t) * (1-t^2)^α := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht
      rw [Set.uIoc_of_le zero_le_one] at ht
      have ht0 : 0 < t := ht.1
      have hmem : c * t ∈ Set.Ioo (0:ℝ) 1 :=
        ⟨mul_pos hc.1 ht0, by nlinarith [hc.2, ht0, ht.2]⟩
      rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hmem.1 hmem.2)]
    rwa [hval] at hderiv
  · filter_upwards [hs] with x hx
    exact ((hcont_F x hx).mono mono_uIoc).aestronglyMeasurable measurableSet_uIoc
  · exact (hcont_F c ⟨by linarith [hc.1], hc.2⟩).intervalIntegrable
  · exact ((hcont_F' c ⟨by linarith [hc.1], hc.2⟩).mono mono_uIoc).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards with t ht x hx
    rw [Set.uIoc_of_le zero_le_one] at ht
    obtain ⟨ht0, ht1⟩ := ht
    have hxt : x*t ∈ Set.Ioo (0:ℝ) 1 :=
      ⟨mul_pos (by linarith [hx.1, hc.1]) ht0, by nlinarith [hx.2, ht0, ht1]⟩
    have h1 : ‖derivWithin G (Set.Icc 0 1) (x*t)‖ ≤ M := hM _ ⟨hxt.1.le, hxt.2.le⟩
    have h2 : (1:ℝ) - t^2 ∈ Set.Icc 0 1 := ⟨by nlinarith [ht1], by nlinarith [ht0]⟩
    have h3 : ‖(1-t^2)^α‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg h2.1 α)]
      exact Real.rpow_le_one h2.1 h2.2 hα.le
    have h4 : ‖(t : ℝ)‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_pos ht0]; exact ht1
    rw [norm_mul, norm_mul]
    calc ‖t‖ * ‖derivWithin G (Set.Icc 0 1) (x*t)‖ * ‖(1-t^2)^α‖
        ≤ 1 * M * 1 := by
          exact mul_le_mul (mul_le_mul h4 h1 (norm_nonneg _) zero_le_one) h3
            (norm_nonneg _) (mul_nonneg zero_le_one hM0)
      _ = M := by ring
  · exact intervalIntegrable_const
  · filter_upwards with t ht x hx
    rw [Set.uIoc_of_le zero_le_one] at ht
    obtain ⟨ht0, ht1⟩ := ht
    have hxt : x*t ∈ Set.Ioo (0:ℝ) 1 :=
      ⟨mul_pos (by linarith [hx.1, hc.1]) ht0, by nlinarith [hx.2, ht0, ht1]⟩
    have hinner : HasDerivAt (fun x : ℝ => x*t) t x := by
      simpa using (hasDerivAt_id x).mul_const t
    have hcomp : HasDerivAt (fun x : ℝ => G (x*t)) (t * deriv G (x*t)) x :=
      (hG_at (x*t) hxt).scomp x hinner
    have hmul := hcomp.mul_const ((1-t^2)^α)
    refine hmul.congr_deriv ?_
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hxt.1 hxt.2)]

/-- **An integration-by-parts identity for the Abel kernel.**

For `α > 0`, `G` of class `C¹` on `[0,1]` and `0 < c < 1`:
`(2α+1) ∫_0^1 G(ct)(1-t²)^α dt + c ∫_0^1 (deriv G)(ct) t (1-t²)^α dt = 2α ∫_0^1 G(ct)(1-t²)^(α-1) dt`. -/
theorem ibp_direct {α : ℝ} (hα : 0 < α) {G : ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G (Set.Icc 0 1)) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    (2*α+1) * (∫ t in (0:ℝ)..1, G (c*t) * (1-t^2)^α)
      + c * (∫ t in (0:ℝ)..1, deriv G (c*t) * t * (1-t^2)^α)
      = 2*α * (∫ t in (0:ℝ)..1, G (c*t) * (1-t^2)^(α-1)) := by
  have hGcont : ContinuousOn G (Set.Icc 0 1) := hG.continuousOn
  have hderiv_cont : ContinuousOn (derivWithin G (Set.Icc 0 1)) (Set.Icc 0 1) :=
    hG.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) le_rfl
  have hGdiff : DifferentiableOn ℝ G (Set.Icc 0 1) := hG.differentiableOn (by norm_num)
  have hG_at : ∀ y ∈ Set.Ioo (0:ℝ) 1, HasDerivAt G (deriv G y) y := by
    intro y hy
    exact ((hGdiff y ⟨hy.1.le, hy.2.le⟩).differentiableAt (Icc_mem_nhds hy.1 hy.2)).hasDerivAt
  have hpow_cont : ContinuousOn (fun t : ℝ => (1-t^2)^α) (Set.uIcc (0:ℝ) 1) := by
    apply ContinuousOn.rpow
    · exact continuousOn_const.sub (continuousOn_id.pow 2)
    · exact continuousOn_const
    · intro t ht; right; exact hα
  have hmaps : Set.MapsTo (fun t : ℝ => c*t) (Set.uIcc (0:ℝ) 1) (Set.Icc 0 1) := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact ⟨mul_nonneg hc.le ht.1, by nlinarith [ht.2, hc1]⟩
  have hGc_cont : ContinuousOn (fun t : ℝ => G (c*t)) (Set.uIcc (0:ℝ) 1) :=
    hGcont.comp ((continuous_const.mul continuous_id).continuousOn) hmaps
  -- continuity of the primitive P
  have hP_cont : ContinuousOn (fun t : ℝ => G (c*t) * t * (1-t^2)^α) (Set.Icc (0:ℝ) 1) := by
    rw [← Set.uIcc_of_le zero_le_one]
    exact (hGc_cont.mul continuousOn_id).mul hpow_cont
  -- derivative of P
  have hPder : ∀ x ∈ Set.Ioo (0:ℝ) 1, HasDerivAt (fun t : ℝ => G (c*t) * t * (1-t^2)^α)
      (c * (deriv G (c*x) * x * (1-x^2)^α) + G (c*x) * (1-x^2)^α
        - 2*α * (G (c*x) * x^2 * (1-x^2)^(α-1))) x := by
    intro x hx
    have hxb : (1 - x^2) ≠ 0 := by nlinarith [hx.1, hx.2]
    have h1 : HasDerivAt (fun t : ℝ => G (c*t)) (c * deriv G (c*x)) x := by
      have hinner : HasDerivAt (fun t : ℝ => c*t) c x := by
        simpa using (hasDerivAt_id x).const_mul c
      have hmem : c*x ∈ Set.Ioo (0:ℝ) 1 := ⟨mul_pos hc hx.1, by nlinarith [hc1, hx.1, hx.2]⟩
      exact (hG_at (c*x) hmem).scomp x hinner
    have h2 : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
    have h3 : HasDerivAt (fun t : ℝ => (1-t^2)^α) ((-(2*x)) * (α * (1-x^2)^(α-1))) x := by
      have hp : HasDerivAt (fun t : ℝ => t^2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have hinner : HasDerivAt (fun t : ℝ => 1 - t^2) (-(2*x)) x := hp.const_sub (1:ℝ)
      exact (Real.hasDerivAt_rpow_const (p := α) (Or.inl hxb)).scomp x hinner
    have hprod := (h1.mul h2).mul h3
    refine hprod.congr_deriv ?_
    simp only [Pi.mul_apply]
    ring_nf
  -- integrability of the three pieces of P'
  have hi1 : IntervalIntegrable (fun t : ℝ => c * (deriv G (c*t) * t * (1-t^2)^α)) volume (0:ℝ) 1 := by
    have hcont : ContinuousOn
        (fun t : ℝ => c * (derivWithin G (Set.Icc 0 1) (c*t) * t * (1-t^2)^α))
        (Set.uIcc (0:ℝ) 1) :=
      continuousOn_const.mul ((hderiv_cont.comp ((continuous_const.mul continuous_id).continuousOn) hmaps).mul continuousOn_id |>.mul hpow_cont)
    refine (hcont.intervalIntegrable).congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    congr 1
    have hmem : c*t ∈ Set.Ioo (0:ℝ) 1 := ⟨mul_pos hc ht.1, by nlinarith [hc1, hc.le, ht.1, ht.2]⟩
    rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hmem.1 hmem.2)]
  have hi2 : IntervalIntegrable (fun t : ℝ => G (c*t) * (1-t^2)^α) volume (0:ℝ) 1 :=
    (hGc_cont.mul hpow_cont).intervalIntegrable
  have hsing : IntervalIntegrable (fun t : ℝ => (1-t^2)^(α-1)) volume (0:ℝ) 1 :=
    intervalIntegrable_one_sub_sq_rpow (show -1 < α - 1 by linarith)
  have hcont2 : ContinuousOn (fun t : ℝ => G (c*t) * t^2) (Set.uIcc (0:ℝ) 1) :=
    hGc_cont.mul (continuousOn_id.pow 2)
  have hi3 : IntervalIntegrable (fun t : ℝ => 2*α * (G (c*t) * t^2 * (1-t^2)^(α-1))) volume (0:ℝ) 1 := by
    have := (hsing.mul_continuousOn hcont2).const_mul (2*α)
    refine this.congr_ae ?_
    filter_upwards with t
    ring
  have hPint : IntervalIntegrable (fun t : ℝ => c * (deriv G (c*t) * t * (1-t^2)^α) + G (c*t) * (1-t^2)^α
        - 2*α * (G (c*t) * t^2 * (1-t^2)^(α-1))) volume (0:ℝ) 1 := (hi1.add hi2).sub hi3
  -- integration by parts
  have hibp := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a := (0:ℝ)) (b := 1)
    zero_le_one hP_cont hPder hPint
  have hP1 : G (c*1) * 1 * (1 - 1^2)^α = 0 := by
    rw [one_pow, sub_self, Real.zero_rpow (ne_of_gt hα), mul_zero]
  have hP0 : G (c*0) * 0 * (1 - 0^2)^α = 0 := by ring
  rw [hP1, hP0, sub_zero] at hibp
  rw [intervalIntegral.integral_sub (hi1.add hi2) hi3, intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hibp
  -- the algebraic relation A + C = B
  have hACB : (∫ t in (0:ℝ)..1, G (c*t) * (1-t^2)^α)
      + (∫ t in (0:ℝ)..1, G (c*t) * t^2 * (1-t^2)^(α-1))
      = (∫ t in (0:ℝ)..1, G (c*t) * (1-t^2)^(α-1)) := by
    have h2' : IntervalIntegrable (fun t : ℝ => G (c*t) * t^2 * (1-t^2)^(α-1)) volume (0:ℝ) 1 := by
      have := hsing.mul_continuousOn hcont2
      exact this.congr_ae (by filter_upwards with t; ring)
    have h3' : IntervalIntegrable (fun t : ℝ => G (c*t) * (1-t^2)^(α-1)) volume (0:ℝ) 1 := by
      have := hsing.mul_continuousOn hGc_cont
      exact this.congr_ae (by filter_upwards with t; ring)
    rw [← intervalIntegral.integral_add hi2 h2']
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    dsimp only
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · subst h1
      rw [one_pow, sub_self, Real.zero_rpow (ne_of_gt hα)]
      ring
    · have hb : 0 < 1 - t^2 := by nlinarith [ht.1, h1]
      have key : (1-t^2)^α = (1-t^2)^(α-1) * (1-t^2) := by
        have h1 : (1-t^2)^α = (1-t^2)^((α-1)+1) := by congr 1; ring
        rw [h1, Real.rpow_add hb (α-1) 1, Real.rpow_one]
      rw [key]
      ring
  linear_combination hibp + (2*α) * hACB


/-- **The exponent-lowering recursion** `T_α' = 2α c T_{α-1}` for the Abel-type transform. -/
theorem hasDerivAt_abelTrans_direct {α : ℝ} (hα : 0 < α) {G : ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G (Set.Icc 0 1)) {c : ℝ} (hc : c ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (abelTrans α G) (2 * α * c * abelTrans (α - 1) G c) c := by
  have hc0 : 0 < c := hc.1
  have hc1 : c < 1 := hc.2
  have hK : HasDerivAt (fun x : ℝ => ∫ t in (0:ℝ)..1, G (x*t) * (1-t^2)^α)
      (∫ t in (0:ℝ)..1, deriv G (c*t) * t * (1-t^2)^α) c := by
    refine (hasDerivAt_integral_rpow_mul_comp hα hG hc).congr_deriv ?_
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  have hx : HasDerivAt (fun x : ℝ => x^(2*α+1)) ((2*α+1) * c^(2*α)) c := by
    have h := Real.hasDerivAt_rpow_const (x := c) (p := 2*α+1) (Or.inl (ne_of_gt hc0))
    refine h.congr_deriv ?_
    ring_nf
  have hxA := hx.mul hK
  -- transfer to abelTrans
  have hsub : abelTrans α G
      =ᶠ[𝓝 c] (fun x : ℝ => x^(2*α+1) * ∫ t in (0:ℝ)..1, G (x*t) * (1-t^2)^α) := by
    filter_upwards [Ioi_mem_nhds hc0] with x hxpos
    exact abelTrans_eq_integral_comp_mul α G hxpos
  have hmain : HasDerivAt (abelTrans α G)
      ((2*α+1) * c^(2*α) * (∫ t in (0:ℝ)..1, G (c*t) * (1-t^2)^α)
        + c^(2*α+1) * (∫ t in (0:ℝ)..1, deriv G (c*t) * t * (1-t^2)^α)) c :=
    hxA.congr_of_eventuallyEq hsub
  have hval : (2*α+1) * c^(2*α) * (∫ t in (0:ℝ)..1, G (c*t) * (1-t^2)^α)
        + c^(2*α+1) * (∫ t in (0:ℝ)..1, deriv G (c*t) * t * (1-t^2)^α)
      = 2*α*c*abelTrans (α-1) G c := by
    have hsub1 : abelTrans (α-1) G c
        = c^(2*(α-1)+1) * (∫ t in (0:ℝ)..1, G (c*t) * (1-t^2)^(α-1)) :=
      abelTrans_eq_integral_comp_mul (α-1) G hc0
    have hibp : (2*α+1) * (∫ t in (0:ℝ)..1, G (c*t) * (1-t^2)^α)
        + c * (∫ t in (0:ℝ)..1, deriv G (c*t) * t * (1-t^2)^α)
        = 2*α * (∫ t in (0:ℝ)..1, G (c*t) * (1-t^2)^(α-1)) :=
      ibp_direct hα hG hc0 hc1
    have e1 : c^(2*α+1) = c^(2*α) * c := by
      rw [Real.rpow_add hc0 (2*α) 1, Real.rpow_one]
    have e2 : c^(2*(α-1)+1) = c^(2*α) * c⁻¹ := by
      rw [show 2*(α-1)+1 = 2*α + (-1) by ring, Real.rpow_add hc0 (2*α) (-1), Real.rpow_neg_one]
    rw [hsub1, e1, e2]
    have hf1 : (2*α+1) * c^(2*α) * (∫ t in (0:ℝ)..1, G (c*t) * (1-t^2)^α)
        + c^(2*α) * c * (∫ t in (0:ℝ)..1, deriv G (c*t) * t * (1-t^2)^α)
        = c^(2*α) * ((2*α+1) * (∫ t in (0:ℝ)..1, G (c*t) * (1-t^2)^α)
            + c * (∫ t in (0:ℝ)..1, deriv G (c*t) * t * (1-t^2)^α)) := by ring
    have hf2 : 2*α*c*(c^(2*α) * c⁻¹ * (∫ t in (0:ℝ)..1, G (c*t) * (1-t^2)^(α-1)))
        = c^(2*α) * (2*α * (∫ t in (0:ℝ)..1, G (c*t) * (1-t^2)^(α-1))) := by
      field_simp
    rw [hf1, hf2, hibp]
  rw [hval] at hmain
  exact hmain


end AbelDirect

end Work.OddRadon

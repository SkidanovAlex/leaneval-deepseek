import Mathlib

namespace Work.OddRadon

noncomputable section

open MeasureTheory Set
open scoped Interval

/-- The derivative of a function on `[0,1]`, realised as a globally defined function:
`wDeriv G y = fderivWithin ℝ G (Icc 0 1) y 1`.  On the interior of `[0,1]` it agrees with
`deriv G`; away from `[0,1]` its values are irrelevant.  Its use is that it is continuous on
the compact set `[0,1]` (so bounded, so a valid domination constant), whereas the a priori
global function `deriv G` carries no information outside `[0,1]`. -/
private def wDeriv (G : ℝ → ℝ) : ℝ → ℝ := fun y => fderivWithin ℝ G (Set.Icc (0:ℝ) 1) y 1

private lemma wDeriv_continuousOn {G : ℝ → ℝ} (hG : ContDiffOn ℝ 1 G (Set.Icc (0:ℝ) 1)) :
    ContinuousOn (wDeriv G) (Set.Icc (0:ℝ) 1) := by
  have h : ContDiffOn ℝ 0 (fderivWithin ℝ G (Set.Icc (0:ℝ) 1)) (Set.Icc (0:ℝ) 1) :=
    hG.fderivWithin (uniqueDiffOn_Icc zero_lt_one) (by simp)
  have h2 : ContinuousOn (fun y : ℝ => (fderivWithin ℝ G (Set.Icc (0:ℝ) 1) y) 1)
      (Set.Icc (0:ℝ) 1) :=
    h.continuousOn.clm_apply (continuousOn_const (c := (1:ℝ)))
  change ContinuousOn (fun y : ℝ => (fderivWithin ℝ G (Set.Icc (0:ℝ) 1) y) 1) (Set.Icc (0:ℝ) 1)
  exact h2

/-- On the interior of `[0,1]` the global derivative agrees with `wDeriv`. -/
private lemma deriv_eq_wDeriv {G : ℝ → ℝ} {y : ℝ} (hy : y ∈ Set.Ioo (0:ℝ) 1) :
    deriv G y = wDeriv G y := by
  have h := fderivWithin_of_mem_nhds (𝕜 := ℝ) (f := G) (Icc_mem_nhds hy.1 hy.2)
  change (fderiv ℝ G y) 1 = (fderivWithin ℝ G (Set.Icc (0:ℝ) 1) y) 1
  rw [h]

/-- The integrand of the substituted Abel integral. -/
private def abelF (α : ℝ) (G : ℝ → ℝ) (x t : ℝ) : ℝ :=
  x ^ (2 * α + 1) * (G (x * t) * (1 - t ^ 2) ^ α)

/-- The formal `x`-derivative of `abelF`, with `deriv G` replaced by the continuous representative
`wDeriv G`. -/
private def abelF' (α : ℝ) (G : ℝ → ℝ) (x t : ℝ) : ℝ :=
  (2 * α + 1) * x ^ (2 * α) * (G (x * t) * (1 - t ^ 2) ^ α)
    + x ^ (2 * α + 1) * (wDeriv G (x * t) * t * (1 - t ^ 2) ^ α)

private lemma continuousOn_G_mul {α x : ℝ} {G : ℝ → ℝ} (hα : 0 < α)
    (hG : ContDiffOn ℝ 1 G (Set.Icc (0:ℝ) 1)) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ContinuousOn (fun t : ℝ => G (x * t) * (1 - t ^ 2) ^ α) (Set.Icc (0:ℝ) 1) := by
  have hmaps : MapsTo (fun t : ℝ => x * t) (Set.Icc (0:ℝ) 1) (Set.Icc (0:ℝ) 1) := by
    intro t ht
    exact ⟨mul_nonneg hx0.le ht.1, by nlinarith [ht.2, hx0, hx1]⟩
  have hGc : ContinuousOn (fun t : ℝ => G (x * t)) (Set.Icc (0:ℝ) 1) :=
    hG.continuousOn.comp (continuousOn_const.mul continuousOn_id) hmaps
  have hpow : ContinuousOn (fun t : ℝ => (1 - t ^ 2) ^ α) (Set.Icc (0:ℝ) 1) :=
    ContinuousOn.rpow (continuous_const.sub (continuous_id.pow 2)).continuousOn
      continuousOn_const (fun _ _ => Or.inr hα)
  exact hGc.mul hpow

private lemma continuousOn_wDeriv_mul {α x : ℝ} {G : ℝ → ℝ} (hα : 0 < α)
    (hG : ContDiffOn ℝ 1 G (Set.Icc (0:ℝ) 1)) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ContinuousOn (fun t : ℝ => wDeriv G (x * t) * t * (1 - t ^ 2) ^ α) (Set.Icc (0:ℝ) 1) := by
  have hmaps : MapsTo (fun t : ℝ => x * t) (Set.Icc (0:ℝ) 1) (Set.Icc (0:ℝ) 1) := by
    intro t ht
    exact ⟨mul_nonneg hx0.le ht.1, by nlinarith [ht.2, hx0, hx1]⟩
  have hwc : ContinuousOn (fun t : ℝ => wDeriv G (x * t)) (Set.Icc (0:ℝ) 1) :=
    (wDeriv_continuousOn hG).comp (continuousOn_const.mul continuousOn_id) hmaps
  have hpow : ContinuousOn (fun t : ℝ => (1 - t ^ 2) ^ α) (Set.Icc (0:ℝ) 1) :=
    ContinuousOn.rpow (continuous_const.sub (continuous_id.pow 2)).continuousOn
      continuousOn_const (fun _ _ => Or.inr hα)
  exact (hwc.mul continuousOn_id).mul hpow

private lemma continuousOn_abelF {α x : ℝ} {G : ℝ → ℝ} (hα : 0 < α)
    (hG : ContDiffOn ℝ 1 G (Set.Icc (0:ℝ) 1)) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ContinuousOn (abelF α G x) (Set.Icc (0:ℝ) 1) := by
  have h := (continuousOn_G_mul (α := α) (x := x) hα hG hx0 hx1).const_mul (x ^ (2 * α + 1))
  change ContinuousOn (fun t : ℝ => x ^ (2 * α + 1) * (G (x * t) * (1 - t ^ 2) ^ α))
    (Set.Icc (0:ℝ) 1)
  exact h

private lemma continuousOn_abelF' {α x : ℝ} {G : ℝ → ℝ} (hα : 0 < α)
    (hG : ContDiffOn ℝ 1 G (Set.Icc (0:ℝ) 1)) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ContinuousOn (abelF' α G x) (Set.Icc (0:ℝ) 1) := by
  have h1 := (continuousOn_G_mul (α := α) (x := x) hα hG hx0 hx1).const_mul
    ((2 * α + 1) * x ^ (2 * α))
  have h2 := (continuousOn_wDeriv_mul (α := α) (x := x) hα hG hx0 hx1).const_mul
    (x ^ (2 * α + 1))
  have hsum := h1.add h2
  change ContinuousOn (fun t : ℝ => (2 * α + 1) * x ^ (2 * α) * (G (x * t) * (1 - t ^ 2) ^ α)
      + x ^ (2 * α + 1) * (wDeriv G (x * t) * t * (1 - t ^ 2) ^ α)) (Set.Icc (0:ℝ) 1)
  exact hsum

/-- The pointwise chain rule / product rule for the integrand, at points where the inner argument
`x * t` lies in the interior of `[0,1]` (so that `G` is honestly differentiable there). -/
private lemma hasDerivAt_abelF {α x t : ℝ} {G : ℝ → ℝ} (hG : ContDiffOn ℝ 1 G (Set.Icc (0:ℝ) 1))
    (hx0 : 0 < x) (hxt : x * t ∈ Set.Ioo (0:ℝ) 1) :
    HasDerivAt (fun y : ℝ => abelF α G y t) (abelF' α G x t) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ (2*α+1)) ((2*α+1) * x^(2*α)) x := by
    have h := Real.hasDerivAt_rpow_const (x := x) (p := 2*α+1) (Or.inl (ne_of_gt hx0))
    have hp : 2*α+1 - 1 = 2*α := by ring
    rwa [hp] at h
  have h2 : HasDerivAt (fun y : ℝ => G (y * t) * (1 - t^2)^α)
      (deriv G (x*t) * t * (1-t^2)^α) x := by
    have hGat : DifferentiableAt ℝ G (x * t) :=
      (hG.differentiableOn (by norm_num)).differentiableAt (Icc_mem_nhds hxt.1 hxt.2)
    have hGd : HasDerivAt G (deriv G (x*t)) (x*t) := by
      simpa only [deriv] using hGat.hasFDerivAt.hasDerivAt
    have hgt : HasDerivAt (fun y : ℝ => y * t) t x := by
      simpa using (hasDerivAt_id x).mul_const t
    exact (hGd.comp x hgt).mul_const _
  have h3 := h1.mul h2
  rw [deriv_eq_wDeriv hxt] at h3
  change HasDerivAt (fun y : ℝ => abelF α G y t) (abelF' α G x t) x
  exact h3

/-- **Differentiation under the integral sign for the substituted Abel integral.**

Context: with `T_α G c = ∫_0^c G s (c²-s²)^α ds` (this is `Work.OddRadon.abelTrans`, defined in
`Submission/Work/OddRadon/Abel.lean`), the substitution `s = c t` (`c > 0`) gives
`T_α G c = ∫_0^1 c^(2α+1) G(ct) (1-t²)^α dt`.  The result below is the derivative in `c` of that
last expression, with the integral of the partial derivative split into its two terms (the
Leibniz rule gives the integral of the sum; splitting it uses that each piece is
interval-integrable).

Intended downstream use: combined with the integration-by-parts identity
`(2α+1)∫_0^1 G(ct)(1-t²)^α + c∫_0^1 (deriv G)(ct) t (1-t²)^α = 2α∫_0^1 G(ct)(1-t²)^(α-1)`
this yields `T_α G' = 2α c T_{α-1} G` at `c`.

Hints: `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` with
`F x t = x^(2α+1) * (G (x*t) * (1-t²)^α)` and
`F' x t = (2α+1) * x^(2α) * (G (x*t) * (1-t²)^α) + x^(2α+1) * (deriv G (x*t) * t * (1-t²)^α)`,
dominated by `C * (1-t²)^α`.  `G` is `C¹` on `[0,1]` and the parameter ranges over a compact
subinterval of `(0,1)`, so `deriv G` is bounded there (`ContDiffOn.fderivWithin` plus compactness,
and `deriv G y = fderivWithin ℝ G (Icc 0 1) y 1` for `y ∈ (0,1)`).  Note `t` ranges over
`Ioc 0 1` almost everywhere, so the endpoint `t = 0` (where only one-sided information about `G`
is available) is harmless.-/
theorem hasDerivAt_integral_rpow_mul {α : ℝ} (hα : 0 < α) {G : ℝ → ℝ}
    (hG : ContDiffOn ℝ 1 G (Set.Icc 0 1)) {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun x : ℝ => ∫ t in (0 : ℝ)..1, x ^ (2 * α + 1) * (G (x * t) * (1 - t ^ 2) ^ α))
      ((2 * α + 1) * c ^ (2 * α) * (∫ t in (0 : ℝ)..1, G (c * t) * (1 - t ^ 2) ^ α)
        + c ^ (2 * α + 1) * (∫ t in (0 : ℝ)..1, deriv G (c * t) * t * (1 - t ^ 2) ^ α)) c := by
  obtain ⟨hc0, hc1⟩ := hc
  -- a neighbourhood of `c` inside `(0,1)`
  set s : Set ℝ := Set.Ioo (c / 2) ((1 + c) / 2) with hs_def
  have hcs : c ∈ s := by
    rw [hs_def]; exact ⟨by linarith, by linarith⟩
  have hs_nhds : ∀ᶠ x in nhds c, x ∈ s := by
    rw [hs_def]; exact isOpen_Ioo.mem_nhds hcs
  have hs_lt : ∀ x ∈ s, 0 < x ∧ x < 1 := by
    intro x hx
    rw [hs_def, Set.mem_Ioo] at hx
    exact ⟨by linarith [hc0, hx.1], by linarith [hc1, hx.2]⟩
  -- bounds for `G` and for its derivative on `[0,1]`
  obtain ⟨Dg, hDg⟩ : ∃ Dg : ℝ, ∀ y ∈ Set.Icc (0:ℝ) 1, ‖G y‖ ≤ Dg :=
    isCompact_Icc.exists_bound_of_continuousOn hG.continuousOn
  obtain ⟨Mw, hMw⟩ : ∃ Mw : ℝ, ∀ y ∈ Set.Icc (0:ℝ) 1, ‖wDeriv G y‖ ≤ Mw :=
    isCompact_Icc.exists_bound_of_continuousOn (wDeriv_continuousOn hG)
  set Dg' : ℝ := max Dg 0 with hDg'_def
  set M' : ℝ := max Mw 0 with hM'_def
  have hDg'_nonneg : 0 ≤ Dg' := by rw [hDg'_def]; exact le_max_right _ _
  have hM'_nonneg : 0 ≤ M' := by rw [hM'_def]; exact le_max_right _ _
  have hDg'_bound : ∀ y ∈ Set.Icc (0:ℝ) 1, ‖G y‖ ≤ Dg' := by
    intro y hy; rw [hDg'_def]; exact le_trans (hDg y hy) (le_max_left _ _)
  have hM'_bound : ∀ y ∈ Set.Icc (0:ℝ) 1, ‖wDeriv G y‖ ≤ M' := by
    intro y hy; rw [hM'_def]; exact le_trans (hMw y hy) (le_max_left _ _)
  -- the uniform domination bound
  have hbound : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0:ℝ) 1 →
      ∀ x ∈ s, ‖abelF' α G x t‖ ≤ (2 * α + 1) * Dg' + M' := by
    refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    rw [Set.uIoc_of_le zero_le_one] at ht
    obtain ⟨hx0, hx1⟩ := hs_lt x hx
    have ht0 : 0 < t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hxt0 : 0 < x * t := mul_pos hx0 ht0
    have hxt1 : x * t < 1 := by nlinarith [hx1, ht1, hx0, ht0]
    have hxtIcc : x * t ∈ Set.Icc (0:ℝ) 1 := ⟨hxt0.le, hxt1.le⟩
    have h21 : (0:ℝ) < 2 * α + 1 := by linarith
    have hxpow : |x ^ (2*α)| ≤ 1 := by
      rw [abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
      exact Real.rpow_le_one hx0.le hx1.le (by linarith)
    have hxpow1 : |x ^ (2*α+1)| ≤ 1 := by
      rw [abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
      exact Real.rpow_le_one hx0.le hx1.le (by linarith)
    have hpowle : |(1 - t^2)^α| ≤ 1 := by
      have hb0 : 0 ≤ 1 - t^2 := by nlinarith [sq_nonneg t]
      have hb1 : 1 - t^2 ≤ 1 := by nlinarith [sq_nonneg t]
      rw [abs_of_nonneg (Real.rpow_nonneg hb0 _)]
      exact Real.rpow_le_one hb0 hb1 hα.le
    have htabs : |t| ≤ 1 := by rw [abs_of_pos ht0]; exact ht1
    have hGle : |G (x * t)| ≤ Dg' := by rw [← Real.norm_eq_abs]; exact hDg'_bound _ hxtIcc
    have hMle : |wDeriv G (x * t)| ≤ M' := by rw [← Real.norm_eq_abs]; exact hM'_bound _ hxtIcc
    have hA : ‖(2*α+1) * x ^ (2*α) * (G (x*t) * (1-t^2)^α)‖ ≤ (2*α+1) * Dg' := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos h21]
      have h1 : |x ^ (2*α)| * (|G (x*t)| * |(1-t^2)^α|) ≤ 1 * (Dg' * 1) :=
        mul_le_mul hxpow (mul_le_mul hGle hpowle (abs_nonneg _) hDg'_nonneg)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)
      calc (2*α+1) * |x ^ (2*α)| * (|G (x*t)| * |(1-t^2)^α|)
          = (2*α+1) * (|x ^ (2*α)| * (|G (x*t)| * |(1-t^2)^α|)) := by ring
        _ ≤ (2*α+1) * (1 * (Dg' * 1)) := mul_le_mul_of_nonneg_left h1 h21.le
        _ = (2*α+1) * Dg' := by ring
    have hB : ‖x^(2*α+1) * (wDeriv G (x*t) * t * (1-t^2)^α)‖ ≤ M' := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      have h1 : (|wDeriv G (x*t)| * |t|) * |(1-t^2)^α| ≤ M' :=
        calc (|wDeriv G (x*t)| * |t|) * |(1-t^2)^α|
            ≤ (M' * 1) * 1 :=
              mul_le_mul (mul_le_mul hMle htabs (abs_nonneg _) hM'_nonneg) hpowle
                (abs_nonneg _) (by positivity)
          _ = M' := by ring
      calc |x^(2*α+1)| * ((|wDeriv G (x*t)| * |t|) * |(1-t^2)^α|)
          ≤ 1 * M' := mul_le_mul hxpow1 h1 (by positivity) (by norm_num)
        _ = M' := by ring
    change ‖((2*α+1) * x ^ (2*α) * (G (x*t) * (1-t^2)^α))
      + x^(2*α+1) * (wDeriv G (x*t) * t * (1-t^2)^α)‖ ≤ (2*α+1) * Dg' + M'
    have hsumle : ‖((2*α+1) * x ^ (2*α) * (G (x*t) * (1-t^2)^α))
        + x^(2*α+1) * (wDeriv G (x*t) * t * (1-t^2)^α)‖
        ≤ ‖(2*α+1) * x ^ (2*α) * (G (x*t) * (1-t^2)^α)‖
          + ‖x^(2*α+1) * (wDeriv G (x*t) * t * (1-t^2)^α)‖ := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      exact abs_add_le _ _
    linarith [hA, hB, hsumle]
  -- continuity/measurability of the two integrands
  have hF_cont : ∀ x ∈ s, ContinuousOn (abelF α G x) (Set.Icc (0:ℝ) 1) := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hs_lt x hx
    exact continuousOn_abelF hα hG hx0 hx1.le
  have hF'_cont : ∀ x ∈ s, ContinuousOn (abelF' α G x) (Set.Icc (0:ℝ) 1) := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hs_lt x hx
    exact continuousOn_abelF' hα hG hx0 hx1.le
  have huIoc_sub : Set.uIoc (0:ℝ) 1 ⊆ Set.Icc (0:ℝ) 1 := by
    intro t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    exact ⟨ht.1.le, ht.2⟩
  have hF_meas : ∀ᶠ x in nhds c,
      AEStronglyMeasurable (abelF α G x) (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    hs_nhds.mono (fun x hx =>
      ((hF_cont x hx).mono huIoc_sub).aestronglyMeasurable measurableSet_uIoc)
  have hF'_meas : AEStronglyMeasurable (abelF' α G c) (volume.restrict (Set.uIoc (0:ℝ) 1)) :=
    ((hF'_cont c hcs).mono huIoc_sub).aestronglyMeasurable measurableSet_uIoc
  have hF_int : IntervalIntegrable (abelF α G c) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hF_cont c hcs
  -- the pointwise derivative, almost everywhere on `Ioc 0 1`
  have h_diff : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.uIoc (0:ℝ) 1 →
      ∀ x ∈ s, HasDerivAt (fun y : ℝ => abelF α G y t) (abelF' α G x t) x := by
    refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
    rw [Set.uIoc_of_le zero_le_one] at ht
    obtain ⟨hx0, hx1⟩ := hs_lt x hx
    exact hasDerivAt_abelF hG hx0 ⟨mul_pos hx0 ht.1, by nlinarith [hx1, ht.2, hx0, ht.1]⟩
  -- differentiate under the integral sign
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (a := (0:ℝ)) (b := 1)
    (F := abelF α G) (F' := abelF' α G) (x₀ := c) (s := s)
    (bound := fun _ => (2*α+1) * Dg' + M')
    hs_nhds hF_meas hF_int hF'_meas hbound intervalIntegrable_const h_diff
  obtain ⟨-, hderiv⟩ := hmain
  -- rewrite the derivative into the two displayed integrals
  have hF'_unfold : ∀ t : ℝ, abelF' α G c t =
      (2*α+1) * c^(2*α) * (G (c*t) * (1-t^2)^α)
        + c^(2*α+1) * (wDeriv G (c*t) * t * (1-t^2)^α) := fun _ => rfl
  have hint1 : IntervalIntegrable
      (fun t : ℝ => (2*α+1) * c^(2*α) * (G (c*t) * (1-t^2)^α)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact (continuousOn_G_mul (α := α) (x := c) hα hG hc0 hc1.le).const_mul _
  have hint2 : IntervalIntegrable
      (fun t : ℝ => c^(2*α+1) * (wDeriv G (c*t) * t * (1-t^2)^α)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact (continuousOn_wDeriv_mul (α := α) (x := c) hα hG hc0 hc1.le).const_mul _
  have hcongr : (∫ t in (0:ℝ)..1, wDeriv G (c*t) * t * (1-t^2)^α)
      = ∫ t in (0:ℝ)..1, deriv G (c*t) * t * (1-t^2)^α := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    rw [Set.uIoc_of_le zero_le_one] at ht
    rw [deriv_eq_wDeriv (G := G) ⟨mul_pos hc0 ht.1, by nlinarith [hc1, ht.2, hc0, ht.1]⟩]
  have hint_eq : (∫ t in (0:ℝ)..1, abelF' α G c t)
      = (2*α+1) * c^(2*α) * (∫ t in (0:ℝ)..1, G (c*t) * (1-t^2)^α)
        + c^(2*α+1) * (∫ t in (0:ℝ)..1, deriv G (c*t) * t * (1-t^2)^α) := by
    simp only [hF'_unfold]
    rw [intervalIntegral.integral_add hint1 hint2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hcongr]
  rw [hint_eq] at hderiv
  exact hderiv

end

end Work.OddRadon

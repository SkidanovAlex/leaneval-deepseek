import Mathlib
import Submission.Work.Smooth.Jordan.All
import Submission.Work.BoxShrink.PinchOff.exists_untop_continuous

namespace Work.BoxShrink.PinchOff

noncomputable section

open Set

/-- **A small push of the model disc towards the marked point.**

`E : 𝔻 → S²` is continuous, injective, sends the boundary circle into the finite part of `S²`
(via a continuous `c`), sends `u₀` to `∞`, and sends the open disc minus `u₀` into a set `U`.

Given `0 < δ`, `0 < ε`, and `‖u₀‖ < 1 - δ`, there is a continuous `φ : 𝔻 → 𝔻` which

* fixes `{‖w‖ ≤ 1 - δ}` pointwise (the "far" region of the model disc),
* maps every point of `𝔻` strictly inside `𝔻` and, unless the point is `u₀` itself, avoids `u₀`
  (so that `E ∘ φ` takes values in the finite part, indeed in `U`),
* and whose effect *on the image under `E`* is at most `ε/4` in the Euclidean metric of `ℂ`.

The construction is the convex interpolation `φ w = (1 - σ(‖w‖)) • w + σ(‖w‖) • u₀` with
`σ : ℝ → [0, s₀]` continuous, `σ = 0` on `(-∞, 1 - δ]` and `σ = s₀` on `[1, ∞)`, with the amplitude
`s₀ > 0` chosen small enough; the last conclusion is uniform continuity of (the finite part of) `E`
on the compact active region `{1 - δ ≤ ‖w‖}` (which avoids `u₀` by `‖u₀‖ < 1 - δ`, so `E` is finite
there). -/
theorem exists_push_small
    {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε)
    {u₀ : Work.Smooth.Jordan.Disc} (hu₀ : ‖(u₀ : ℂ)‖ < 1 - δ)
    {U : Set ℂ} {E : Work.Smooth.Jordan.Disc → OnePoint ℂ} (hE : Continuous E)
    (hEinj : Function.Injective E)
    (hEu₀ : E u₀ = OnePoint.infty)
    (hEopen : ∀ w : Work.Smooth.Jordan.Disc, ‖(w : ℂ)‖ < 1 → w ≠ u₀ →
      ∃ z : ℂ, E w = (z : OnePoint ℂ) ∧ z ∈ U) :
    ∃ φ : Work.Smooth.Jordan.Disc → Work.Smooth.Jordan.Disc, Continuous φ ∧
      (∀ w : Work.Smooth.Jordan.Disc, ‖(w : ℂ)‖ ≤ 1 - δ → φ w = w) ∧
      (∀ w : Work.Smooth.Jordan.Disc, ‖((φ w : Work.Smooth.Jordan.Disc) : ℂ)‖ < 1) ∧
      (∀ w : Work.Smooth.Jordan.Disc, (w : ℂ) ≠ (u₀ : ℂ) →
        ((φ w : Work.Smooth.Jordan.Disc) : ℂ) ≠ (u₀ : ℂ)) ∧
      (∀ w : Work.Smooth.Jordan.Disc, ∀ b : ℂ, E w = (b : OnePoint ℂ) →
        ∃ a : ℂ, E (φ w) = (a : OnePoint ℂ) ∧ ‖a - b‖ ≤ ε / 4) := by
  classical
  obtain ⟨u, hu_sec, hu_cont⟩ := exists_untop_continuous
  have hu₀n : ‖(u₀ : ℂ)‖ < 1 := by linarith
  have norm_le_one : ∀ w : Work.Smooth.Jordan.Disc, ‖(w : ℂ)‖ ≤ 1 := by
    intro w
    have h := w.2
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  -- the gap between the marked point and the active collar
  have hμpos : 0 < (1 - δ) - ‖(u₀ : ℂ)‖ := by linarith
  set μ : ℝ := (1 - δ) - ‖(u₀ : ℂ)‖ with hμdef
  have hμpos' : 0 < μ := by rw [hμdef]; exact hμpos
  -- the compact "active" region
  set K : Set Work.Smooth.Jordan.Disc :=
    {w | μ / 2 ≤ ‖(w : ℂ) - (u₀ : ℂ)‖} with hKdef
  have hKclosed : IsClosed K := by
    rw [hKdef]
    exact isClosed_Ici.preimage
      (continuous_norm.comp (continuous_subtype_val.sub continuous_const))
  have hKcompact : IsCompact K :=
    (isCompact_univ : IsCompact (Set.univ : Set Work.Smooth.Jordan.Disc)).of_isClosed_subset
      hKclosed (subset_univ K)
  -- `u ∘ E` is continuous on the active region, hence uniformly continuous
  have hcont_K : ContinuousOn (fun w : Work.Smooth.Jordan.Disc => u (E w)) K := by
    intro x hx
    have hx_ineq : μ / 2 ≤ ‖(x : ℂ) - (u₀ : ℂ)‖ := by
      have h := hx
      rw [hKdef] at h
      simpa using h
    have hxu : x ≠ u₀ := by
      intro h
      rw [h] at hx_ineq
      simp at hx_ineq
      linarith [hμpos']
    have hEx : E x ≠ OnePoint.infty := by
      intro h
      exact hxu (hEinj (by rw [h, hEu₀]))
    exact ((hu_cont (E x) hEx).comp hE.continuousAt).continuousWithinAt
  have hUC : UniformContinuousOn (fun w : Work.Smooth.Jordan.Disc => u (E w)) K :=
    hKcompact.uniformContinuousOn_of_continuous hcont_K
  rw [Metric.uniformContinuousOn_iff] at hUC
  obtain ⟨ρ, hρpos, hρ⟩ := hUC (ε / 4) (by linarith)
  -- amplitude of the push
  obtain ⟨s₀, hs₀pos, hs₀ρ, hs₀half⟩ :
      ∃ s₀ : ℝ, 0 < s₀ ∧ 2 * s₀ < ρ ∧ s₀ ≤ 1 / 2 := by
    refine ⟨min (ρ / 4) (1 / 4), ?_, ?_, ?_⟩
    · exact lt_min (by linarith) (by norm_num)
    · have h : min (ρ / 4) (1 / 4) ≤ ρ / 4 := min_le_left _ _
      linarith
    · have h : min (ρ / 4) (1 / 4) ≤ 1 / 4 := min_le_right _ _
      linarith
  -- the bump function
  set σ : ℝ → ℝ := fun t => s₀ * max 0 (min 1 ((t - (1 - δ)) / δ)) with hσdef
  have hσcont : Continuous σ := by
    rw [hσdef]
    exact (continuous_const.max
      (continuous_const.min ((continuous_id.sub continuous_const).div_const δ))).const_mul s₀
  have hσval : ∀ t : ℝ, σ t = s₀ * max 0 (min 1 ((t - (1 - δ)) / δ)) := by
    intro t
    rw [hσdef]
  have hσ_nonneg : ∀ t : ℝ, 0 ≤ σ t := by
    intro t
    rw [hσval t]
    exact mul_nonneg hs₀pos.le (le_max_left _ _)
  have hσ_le : ∀ t : ℝ, σ t ≤ s₀ := by
    intro t
    rw [hσval t]
    have h1 : max 0 (min 1 ((t - (1 - δ)) / δ)) ≤ 1 :=
      max_le (by norm_num) (min_le_left _ _)
    nlinarith [hs₀pos.le, h1]
  have hσ_zero : ∀ t : ℝ, t ≤ 1 - δ → σ t = 0 := by
    intro t ht
    rw [hσval t]
    have hdiv : (t - (1 - δ)) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
    have h' : min 1 ((t - (1 - δ)) / δ) ≤ 0 := le_trans (min_le_right _ _) hdiv
    rw [max_eq_left h', mul_zero]
  have hσ_iff : ∀ t : ℝ, σ t = 0 ↔ t ≤ 1 - δ := by
    intro t
    refine ⟨?_, hσ_zero t⟩
    intro h
    by_contra hc
    push_neg at hc
    have hdiv : 0 < (t - (1 - δ)) / δ := div_pos (by linarith) hδ
    have hmin : 0 < min 1 ((t - (1 - δ)) / δ) := lt_min (by norm_num) hdiv
    have hmax : max 0 (min 1 ((t - (1 - δ)) / δ)) = min 1 ((t - (1 - δ)) / δ) :=
      max_eq_right hmin.le
    have : 0 < σ t := by
      rw [hσval t, hmax]
      exact mul_pos hs₀pos hmin
    linarith
  -- the norm estimate for the interpolation
  have hφnorm_le : ∀ w : Work.Smooth.Jordan.Disc,
      ‖(1 - σ ‖(w : ℂ)‖) • (w : ℂ) + σ ‖(w : ℂ)‖ • (u₀ : ℂ)‖
        ≤ 1 - σ ‖(w : ℂ)‖ * (1 - ‖(u₀ : ℂ)‖) := by
    intro w
    have hw1 : ‖(w : ℂ)‖ ≤ 1 := norm_le_one w
    have hs0 : 0 ≤ σ ‖(w : ℂ)‖ := hσ_nonneg _
    have hs1 : σ ‖(w : ℂ)‖ ≤ 1 := by
      have := hσ_le ‖(w : ℂ)‖
      linarith
    have hcoef : 0 ≤ 1 - σ ‖(w : ℂ)‖ := by linarith
    calc ‖(1 - σ ‖(w : ℂ)‖) • (w : ℂ) + σ ‖(w : ℂ)‖ • (u₀ : ℂ)‖
        ≤ ‖(1 - σ ‖(w : ℂ)‖) • (w : ℂ)‖ + ‖σ ‖(w : ℂ)‖ • (u₀ : ℂ)‖ := norm_add_le _ _
      _ = |1 - σ ‖(w : ℂ)‖| * ‖(w : ℂ)‖ + |σ ‖(w : ℂ)‖| * ‖(u₀ : ℂ)‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ = (1 - σ ‖(w : ℂ)‖) * ‖(w : ℂ)‖ + σ ‖(w : ℂ)‖ * ‖(u₀ : ℂ)‖ := by
            rw [abs_of_nonneg hcoef, abs_of_nonneg hs0]
      _ ≤ (1 - σ ‖(w : ℂ)‖) * 1 + σ ‖(w : ℂ)‖ * ‖(u₀ : ℂ)‖ := by
            have := mul_le_mul_of_nonneg_left hw1 hcoef
            linarith
      _ = 1 - σ ‖(w : ℂ)‖ * (1 - ‖(u₀ : ℂ)‖) := by ring
  -- membership of the interpolation in the disc
  have hbody : ∀ w : Work.Smooth.Jordan.Disc,
      ((1 - σ ‖(w : ℂ)‖) • (w : ℂ) + σ ‖(w : ℂ)‖ • (u₀ : ℂ)) ∈
        Metric.closedBall (0 : ℂ) 1 := by
    intro w
    rw [Metric.mem_closedBall, dist_zero_right]
    refine le_trans (hφnorm_le w) ?_
    have hs0 : 0 ≤ σ ‖(w : ℂ)‖ := hσ_nonneg _
    have huw : ‖(u₀ : ℂ)‖ ≤ 1 := le_of_lt hu₀n
    nlinarith
  -- the push itself
  set φ : Work.Smooth.Jordan.Disc → Work.Smooth.Jordan.Disc :=
    fun w => ⟨(1 - σ ‖(w : ℂ)‖) • (w : ℂ) + σ ‖(w : ℂ)‖ • (u₀ : ℂ), hbody w⟩ with hφdef
  have hφapply : ∀ w : Work.Smooth.Jordan.Disc,
      ((φ w : Work.Smooth.Jordan.Disc) : ℂ)
        = (1 - σ ‖(w : ℂ)‖) • (w : ℂ) + σ ‖(w : ℂ)‖ • (u₀ : ℂ) := by
    intro w
    rw [hφdef]
  have hφsub : ∀ w : Work.Smooth.Jordan.Disc,
      ((φ w : Work.Smooth.Jordan.Disc) : ℂ) - (u₀ : ℂ)
        = (1 - σ ‖(w : ℂ)‖) • ((w : ℂ) - (u₀ : ℂ)) := by
    intro w
    rw [hφapply w, smul_sub]
    have key : (1 - σ ‖(w : ℂ)‖) • (u₀ : ℂ) = (u₀ : ℂ) - σ ‖(w : ℂ)‖ • (u₀ : ℂ) := by
      rw [sub_smul, one_smul]
    rw [key]
    abel
  have hφsubnorm : ∀ w : Work.Smooth.Jordan.Disc,
      ‖((φ w : Work.Smooth.Jordan.Disc) : ℂ) - (u₀ : ℂ)‖
        = (1 - σ ‖(w : ℂ)‖) * ‖(w : ℂ) - (u₀ : ℂ)‖ := by
    intro w
    rw [hφsub w, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by have := hσ_le ‖(w : ℂ)‖; linarith)]
  -- the push is continuous
  have hφcont : Continuous φ := by
    rw [hφdef]
    refine Continuous.subtype_mk ?_ hbody
    refine Continuous.add ?_ ?_
    · exact (continuous_const.sub (hσcont.comp (continuous_norm.comp continuous_subtype_val))).smul
        continuous_subtype_val
    · exact (hσcont.comp (continuous_norm.comp continuous_subtype_val)).smul continuous_const
  -- it fixes the far region
  have hφfix : ∀ w : Work.Smooth.Jordan.Disc, ‖(w : ℂ)‖ ≤ 1 - δ → φ w = w := by
    intro w hw
    apply Subtype.ext
    rw [hφapply w, (hσ_iff ‖(w : ℂ)‖).mpr hw]
    simp
  -- it maps the disc strictly inside
  have hφint : ∀ w : Work.Smooth.Jordan.Disc,
      ‖((φ w : Work.Smooth.Jordan.Disc) : ℂ)‖ < 1 := by
    intro w
    by_cases hσw : σ ‖(w : ℂ)‖ = 0
    · have hwδ : ‖(w : ℂ)‖ ≤ 1 - δ := (hσ_iff ‖(w : ℂ)‖).mp hσw
      rw [hφapply w, hσw]
      simp only [sub_zero, one_smul, zero_smul, add_zero]
      linarith
    · have hσpos : 0 < σ ‖(w : ℂ)‖ := lt_of_le_of_ne (hσ_nonneg _) (Ne.symm hσw)
      have h1 := hφnorm_le w
      have h2 : 0 < 1 - ‖(u₀ : ℂ)‖ := by linarith
      nlinarith [hσpos, h2, hσ_nonneg ‖(w : ℂ)‖, hu₀n]
  -- it avoids `u₀` away from `u₀`
  have hφu₀ : ∀ w : Work.Smooth.Jordan.Disc, (w : ℂ) ≠ (u₀ : ℂ) →
      ((φ w : Work.Smooth.Jordan.Disc) : ℂ) ≠ (u₀ : ℂ) := by
    intro w hw h
    have h0 : ‖((φ w : Work.Smooth.Jordan.Disc) : ℂ) - (u₀ : ℂ)‖ = 0 := by
      rw [h, sub_self, norm_zero]
    rw [hφsubnorm w] at h0
    have hp1 : 0 < ‖(w : ℂ) - (u₀ : ℂ)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw)
    have hp2 : 0 < 1 - σ ‖(w : ℂ)‖ := by have := hσ_le ‖(w : ℂ)‖; linarith
    nlinarith
  refine ⟨φ, hφcont, hφfix, hφint, hφu₀, ?_⟩
  intro w b hb
  by_cases hwfar : ‖(w : ℂ)‖ ≤ 1 - δ
  · refine ⟨b, by rw [hφfix w hwfar]; exact hb, ?_⟩
    rw [sub_self, norm_zero]
    positivity
  · push_neg at hwfar
    have hw_u₀ : (w : ℂ) ≠ (u₀ : ℂ) := by
      intro h
      have : ‖(w : ℂ)‖ = ‖(u₀ : ℂ)‖ := by rw [h]
      linarith
    have hw_ge : μ ≤ ‖(w : ℂ) - (u₀ : ℂ)‖ := by
      have h1 : ‖(w : ℂ)‖ - ‖(u₀ : ℂ)‖ ≤ ‖(w : ℂ) - (u₀ : ℂ)‖ := norm_sub_norm_le _ _
      have h2 : μ = (1 - δ) - ‖(u₀ : ℂ)‖ := hμdef
      linarith
    have hwK : w ∈ K := by
      rw [hKdef]
      show μ / 2 ≤ ‖(w : ℂ) - (u₀ : ℂ)‖
      linarith
    have hφwK : φ w ∈ K := by
      rw [hKdef]
      show μ / 2 ≤ ‖((φ w : Work.Smooth.Jordan.Disc) : ℂ) - (u₀ : ℂ)‖
      rw [hφsubnorm w]
      have hcoef : (1 : ℝ) / 2 ≤ 1 - σ ‖(w : ℂ)‖ := by
        have := hσ_le ‖(w : ℂ)‖
        linarith
      nlinarith [hμpos', hw_ge, hcoef]
    have hφw_u₀ : ((φ w : Work.Smooth.Jordan.Disc) : ℂ) ≠ (u₀ : ℂ) := hφu₀ w hw_u₀
    have hφdist : dist (φ w) w < ρ := by
      rw [Subtype.dist_eq, dist_eq_norm]
      have hsub : ((φ w : Work.Smooth.Jordan.Disc) : ℂ) - (w : ℂ)
          = σ ‖(w : ℂ)‖ • ((u₀ : ℂ) - (w : ℂ)) := by
        rw [hφapply w]
        have key : (1 - σ ‖(w : ℂ)‖) • (w : ℂ)
            = (w : ℂ) - σ ‖(w : ℂ)‖ • (w : ℂ) := by rw [sub_smul, one_smul]
        rw [key]
        rw [smul_sub]
        abel
      rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hσ_nonneg _)]
      have hb2 : ‖(u₀ : ℂ) - (w : ℂ)‖ ≤ 2 := by
        have h1 : ‖(u₀ : ℂ) - (w : ℂ)‖ ≤ ‖(u₀ : ℂ)‖ + ‖(w : ℂ)‖ := norm_sub_le _ _
        have h2 : ‖(u₀ : ℂ)‖ ≤ 1 := le_of_lt hu₀n
        have h3 : ‖(w : ℂ)‖ ≤ 1 := norm_le_one w
        linarith
      have hs := hσ_le ‖(w : ℂ)‖
      nlinarith [hσ_nonneg ‖(w : ℂ)‖, hb2, hs, hs₀ρ]
    have hEφw_ne : E (φ w) ≠ OnePoint.infty := by
      intro h
      have : φ w = u₀ := hEinj (by rw [h, hEu₀])
      exact hφw_u₀ (by rw [this])
    have hue : u (E w) = b := by
      rw [hb]
      exact OnePoint.coe_eq_coe.mp (hu_sec (b : OnePoint ℂ) (OnePoint.coe_ne_infty b))
    refine ⟨u (E (φ w)), (hu_sec (E (φ w)) hEφw_ne).symm, ?_⟩
    have h := hρ (φ w) hφwK w hwK hφdist
    rw [hue, dist_eq_norm] at h
    linarith

end

end Work.BoxShrink.PinchOff

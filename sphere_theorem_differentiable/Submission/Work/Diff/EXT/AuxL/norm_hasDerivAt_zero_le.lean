import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Topology
open Filter Set

namespace Work.Diff.EXT.AuxL

/-- One-sided mean value bound. If `g : ℝ → W` is differentiable at `0` with derivative `L`, and on
the open interval `(0,ε)` with derivative `g' t` bounded by `C ≥ 0`, then `‖L‖ ≤ C`. -/
theorem norm_hasDerivAt_zero_le
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {g g' : ℝ → W} {L : W} {ε C : ℝ}
    (hε : 0 < ε) (hC : 0 ≤ C) (h0 : HasDerivAt g L 0)
    (hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) ε, HasDerivAt g (g' t) t)
    (hbound : ∀ t ∈ Set.Ioo (0 : ℝ) ε, ‖g' t‖ ≤ C) :
    ‖L‖ ≤ C := by
  have hpt : ∀ t ∈ Set.Ioo (0 : ℝ) ε, ∀ δ ∈ Set.Ioo (0 : ℝ) t,
      ‖g t - g δ‖ ≤ C * (t - δ) := by
    intro t ht δ hδ
    have hdiff : ∀ x ∈ Set.Icc δ t, DifferentiableAt ℝ g x := by
      intro x hx
      exact (hderiv x ⟨lt_of_lt_of_le hδ.1 hx.1, lt_of_le_of_lt hx.2 ht.2⟩).differentiableAt
    have hder : ∀ x ∈ Set.Icc δ t, ‖deriv g x‖ ≤ C := by
      intro x hx
      have hxε : x ∈ Set.Ioo (0 : ℝ) ε := ⟨lt_of_lt_of_le hδ.1 hx.1, lt_of_le_of_lt hx.2 ht.2⟩
      rw [(hderiv x hxε).deriv]
      exact hbound x hxε
    have hle := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hder (convex_Icc δ t)
      (Set.mem_Icc.mpr ⟨le_rfl, hδ.2.le⟩) (Set.mem_Icc.mpr ⟨hδ.2.le, le_rfl⟩)
    rwa [Real.norm_of_nonneg (by linarith [hδ.2.le] : (0 : ℝ) ≤ t - δ)] at hle
  have hmain : ∀ t ∈ Set.Ioo (0 : ℝ) ε, ‖g t - g 0‖ ≤ C * t := by
    intro t ht
    refine le_of_forall_pos_le_add fun η hη => ?_
    have hδev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ‖g δ - g 0‖ < η / 2 := by
      have hc : ContinuousAt (fun δ : ℝ => g δ) 0 := h0.continuousAt
      have hb : {x : W | ‖x - g 0‖ < η / 2} ∈ 𝓝 (g 0) := by
        have h1 : Metric.ball (g 0) (η / 2) ∈ 𝓝 (g 0) := Metric.ball_mem_nhds _ (half_pos hη)
        refine Filter.mem_of_superset h1 fun x hx => ?_
        simpa [Metric.mem_ball, dist_eq_norm] using hx
      exact (hc.tendsto.mono_left nhdsWithin_le_nhds).eventually hb
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        ‖g δ - g 0‖ < η / 2 ∧ δ ∈ Set.Ioo (0 : ℝ) t :=
      hδev.and (Ioo_mem_nhdsGT ht.1)
    obtain ⟨δ, hδ1, hδ2⟩ := hev.exists
    have h2 : ‖g t - g δ‖ ≤ C * (t - δ) := hpt t ht δ hδ2
    have htri : ‖g t - g 0‖ ≤ ‖g t - g δ‖ + ‖g δ - g 0‖ := by
      have h : g t - g 0 = (g t - g δ) + (g δ - g 0) := by abel
      rw [h]
      exact norm_add_le _ _
    calc ‖g t - g 0‖ ≤ ‖g t - g δ‖ + ‖g δ - g 0‖ := htri
      _ ≤ C * (t - δ) + η / 2 := add_le_add h2 hδ1.le
      _ ≤ C * t + η := by nlinarith [hC, hδ2.1.le, hη]
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖g t - g 0 - t • L‖ ≤ η * t := by
    have hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖g t - g 0 - t • L‖ ≤ η * t := by
      have hb' : ∀ᶠ y in 𝓝 (0 : ℝ),
          ‖g y - g 0 - (ContinuousLinearMap.toSpanSingleton ℝ L) (y - 0)‖ ≤ η * ‖y - 0‖ :=
        (h0.hasFDerivAt.isLittleO).bound hη
      have hb'' : ∀ᶠ y in 𝓝[>] (0 : ℝ),
          ‖g y - g 0 - (ContinuousLinearMap.toSpanSingleton ℝ L) (y - 0)‖ ≤ η * ‖y - 0‖ :=
        hb'.filter_mono inf_le_left
      filter_upwards [hb'', self_mem_nhdsWithin] with y hy hypos
      have hypos' : 0 < y := hypos
      simp only [ContinuousLinearMap.toSpanSingleton_apply, sub_zero] at hy
      rw [Real.norm_of_nonneg hypos'.le] at hy
      exact hy
    filter_upwards [hb, Ioo_mem_nhdsGT hε] with t ht _
    simpa using ht
  have hkey : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ ‖L‖ * t ≤ (C + η) * t := by
    filter_upwards [hsmall, Ioo_mem_nhdsGT hε] with t hst htε
    refine ⟨htε.1, ?_⟩
    have h1 : ‖g t - g 0‖ ≤ C * t := hmain t htε
    have h2 : t * ‖L‖ = ‖t • L‖ := by
      rw [norm_smul, Real.norm_of_nonneg htε.1.le]
    have h3 : t • L = (g t - g 0) - (g t - g 0 - t • L) := by abel
    calc ‖L‖ * t = t * ‖L‖ := by ring
      _ = ‖t • L‖ := h2
      _ = ‖(g t - g 0) - (g t - g 0 - t • L)‖ := congrArg Norm.norm h3
      _ ≤ ‖g t - g 0‖ + ‖g t - g 0 - t • L‖ := norm_sub_le _ _
      _ ≤ C * t + η * t := add_le_add h1 hst
      _ = (C + η) * t := by ring
  obtain ⟨t, ht1, ht2⟩ := hkey.exists
  have hfin : ‖L‖ ≤ C + η := (mul_le_mul_iff_of_pos_right ht1).mp ht2
  linarith

end Work.Diff.EXT.AuxL

import Mathlib.Analysis.Calculus.MeanValue

namespace Commons.Analysis.Calculus

open Filter Set
open scoped Topology

/-- **Slow variation.**  If `g` has derivative `g'` on `(0, δ)` and `t • g' t → 0` as `t → 0⁺`,
then along any sequence `λ_n → 0` with `λ_n > 0` the curve `t ↦ g (t * λ_n)` is eventually
*uniformly* slowly varying on `[a,b]` (for `0 < a ≤ b`). -/
theorem eventually_forall_Icc_norm_sub_lt_of_slow_variation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g g' : ℝ → E} {a b δ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hδ : 0 < δ)
    (hder : ∀ t ∈ Set.Ioo (0:ℝ) δ, HasDerivAt g (g' t) t)
    (hslow : Tendsto (fun t : ℝ => t • g' t) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds 0))
    {lam : ℕ → ℝ} (hpos : ∀ n, 0 < lam n) (hlim : Tendsto lam atTop (nhds 0)) :
    ∀ η > 0, ∀ᶠ n in atTop, ∀ t ∈ Set.Icc a b, ‖g (t * lam n) - g (a * lam n)‖ < η := by
  intro η hη
  have hbpos : 0 < b := lt_of_lt_of_le ha hab
  -- The threshold `ε` for `‖t • g' t‖`, chosen so that `ε * (b - a) / a < η`.
  set ε : ℝ := η * a / (b - a + 1) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]
    apply div_pos (mul_pos hη ha)
    linarith
  have hεη : ε * (b - a) / a < η := by
    have h1 : ε * (b - a) / a = η * (b - a) / (b - a + 1) := by
      rw [hεdef]; field_simp
    rw [h1]
    have hden : 0 < b - a + 1 := by linarith
    rw [div_lt_iff₀ hden]
    have : η * (b - a) < η * (b - a + 1) := by
      apply mul_lt_mul_of_pos_left _ hη; linarith
    linarith
  -- From slow variation: `‖t • g' t‖ < ε` for all `0 < t < α`.
  have hball : Metric.ball (0:E) ε ∈ nhds (0:E) := Metric.ball_mem_nhds 0 hεpos
  have hmem : (fun t : ℝ => t • g' t) ⁻¹' Metric.ball (0:E) ε ∈
      nhdsWithin (0:ℝ) (Set.Ioi 0) := hslow hball
  rw [Metric.mem_nhdsWithin_iff] at hmem
  obtain ⟨α, hαpos, hα⟩ := hmem
  have hα' : ∀ t : ℝ, 0 < t → t < α → ‖t • g' t‖ < ε := by
    intro t ht hlt
    have hd : t ∈ Metric.ball (0:ℝ) α := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht]; exact hlt
    have := hα ⟨hd, ht⟩
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at this
    exact this
  have hr : 0 < min δ α / b := div_pos (lt_min hδ hαpos) hbpos
  filter_upwards [hlim.eventually (Iio_mem_nhds hr)] with n hn
  intro t ht
  have hnpos : 0 < lam n := hpos n
  have hblam : lam n * b < min δ α := (lt_div_iff₀ hbpos).mp hn
  have hblamδ : lam n * b < δ := lt_of_lt_of_le hblam (min_le_left _ _)
  have hblamα : lam n * b < α := lt_of_lt_of_le hblam (min_le_right _ _)
  set c : ℝ := a * lam n with hcdef
  set d : ℝ := t * lam n with hddef
  have hcpos : 0 < c := by rw [hcdef]; exact mul_pos ha hnpos
  have hcd : c ≤ d := by
    rw [hcdef, hddef]; exact mul_le_mul_of_nonneg_right ht.1 hnpos.le
  have hdδ : d < δ := by
    rw [hddef]
    have h1 : t * lam n ≤ b * lam n := mul_le_mul_of_nonneg_right ht.2 hnpos.le
    have h2 : b * lam n = lam n * b := by ring
    linarith
  have hdα : d < α := by
    rw [hddef]
    have h1 : t * lam n ≤ b * lam n := mul_le_mul_of_nonneg_right ht.2 hnpos.le
    have h2 : b * lam n = lam n * b := by ring
    linarith
  -- On the segment `[c,d]` the derivative is bounded by `ε / c`.
  have hbound : ∀ x ∈ Set.Ico c d, ‖g' x‖ ≤ ε / c := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hcpos hx.1
    have hxltα : x < α := lt_trans hx.2 hdα
    have hxsmul : ‖x • g' x‖ = x * ‖g' x‖ := by
      rw [norm_smul, Real.norm_of_nonneg hxpos.le]
    have hxnorm : ‖g' x‖ = ‖x • g' x‖ / x := by
      rw [hxsmul]; field_simp
    rw [hxnorm]
    have h1 : ‖x • g' x‖ / x ≤ ε / x :=
      div_le_div_of_nonneg_right (le_of_lt (hα' x hxpos hxltα)) hxpos.le
    have h2 : ε / x ≤ ε / c := div_le_div_of_nonneg_left hεpos.le hcpos hx.1
    linarith
  have hder' : ∀ x ∈ Set.Icc c d, HasDerivWithinAt g (g' x) (Set.Icc c d) x := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hcpos hx.1
    have hxltδ : x < δ := lt_of_le_of_lt hx.2 hdδ
    exact (hder x ⟨hxpos, hxltδ⟩).hasDerivWithinAt
  have hseg := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (f' := g')
    (a := c) (b := d) (C := ε / c) hder' hbound
  have htd : d ∈ Set.Icc c d := ⟨hcd, le_rfl⟩
  have hmain : ‖g d - g c‖ ≤ ε / c * (d - c) := hseg d htd
  have hdc : d - c = (t - a) * lam n := by rw [hcdef, hddef]; ring
  have hfinal : ε / c * (d - c) = ε * (t - a) / a := by
    rw [hdc, hcdef]
    field_simp
  have hstep : ε * (t - a) / a ≤ ε * (b - a) / a := by
    apply div_le_div_of_nonneg_right _ ha.le
    exact mul_le_mul_of_nonneg_left (by linarith [ht.2]) hεpos.le
  have hsub : ‖g (t * lam n) - g (a * lam n)‖ = ‖g d - g c‖ := by rw [hddef, hcdef]
  rw [hsub]
  calc ‖g d - g c‖ ≤ ε / c * (d - c) := hmain
    _ = ε * (t - a) / a := hfinal
    _ ≤ ε * (b - a) / a := hstep
    _ < η := hεη

end Commons.Analysis.Calculus
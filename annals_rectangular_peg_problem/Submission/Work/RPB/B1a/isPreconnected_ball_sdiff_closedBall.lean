import Mathlib

/-!
# `Work.RPB.B1a.isPreconnected_ball_sdiff_closedBall`

The *far side* `ball 0 1 \ closedBall ζ r` of a chord of the unit disc is preconnected
(here `‖ζ‖ = 1` and `0 < r < 1`).

## Proof

The Möbius map `w ↦ w / (ζ - w)` (which sends `ζ` to `∞`) carries the unit disc onto the
half-plane `{Re > -1/2}` and the exterior of `closedBall ζ r` onto the exterior of the disc
`ball (-1) (1/r)`.  Its image of `ball 0 1 \ closedBall ζ r` is therefore the set

`V = {u | -1/2 < u.re ∧ ‖u + 1‖ < 1/r}`,

an intersection of an open half-plane and an open ball, hence convex.  Since the inverse
`u ↦ u * ζ / (1 + u)` is continuous on `V` (because `Re u > -1/2` forces `1 + u ≠ 0`), the
set `ball 0 1 \ closedBall ζ r` is the continuous image of the preconnected set `V`, hence
preconnected.
-/

namespace Work.RPB.B1a

/-- On the half-plane `Re u > -1/2` one has `‖u‖ < ‖1 + u‖`. -/
private lemma norm_lt_norm_one_add {u : ℂ} (h : (-1/2 : ℝ) < u.re) : ‖u‖ < ‖1 + u‖ := by
  have h1 : Complex.normSq u < Complex.normSq (1 + u) := by
    rw [Complex.normSq_add]
    simp only [Complex.normSq_one, one_mul, Complex.conj_re]
    linarith
  rw [← Complex.sq_norm u, ← Complex.sq_norm (1 + u)] at h1
  nlinarith [norm_nonneg u, norm_nonneg (1 + u)]

/-- Conversely, `‖u‖ < ‖1 + u‖` is equivalent to `Re u > -1/2`. -/
private lemma neg_half_lt_re_of_norm_lt {u : ℂ} (h : ‖u‖ < ‖1 + u‖) : (-1/2 : ℝ) < u.re := by
  have h2 : ‖u‖ ^ 2 < ‖1 + u‖ ^ 2 := by nlinarith [norm_nonneg u, norm_nonneg (1 + u)]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_add] at h2
  simp only [Complex.normSq_one, one_mul, Complex.conj_re] at h2
  linarith

theorem isPreconnected_ball_sdiff_closedBall {ζ : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    IsPreconnected (Metric.ball (0 : ℂ) 1 \ Metric.closedBall ζ r) := by
  have hζne : ζ ≠ 0 := by
    intro h; rw [h] at hζ; simp at hζ
  have hSmem : ∀ w : ℂ, w ∈ Metric.ball (0:ℂ) 1 \ Metric.closedBall ζ r ↔ ‖w‖ < 1 ∧ r < ‖w - ζ‖ := by
    intro w
    simp only [Set.mem_sdiff, Metric.mem_ball, Metric.mem_closedBall, dist_eq_norm, sub_zero,
      not_le]
  set V : Set ℂ := {u : ℂ | (-1/2 : ℝ) < u.re ∧ ‖u + 1‖ < 1/r} with hVdef
  have hVconv : Convex ℝ V := by
    rw [hVdef, Set.ofPred_and]
    refine Convex.inter ?_ ?_
    · have h : {u : ℂ | (-1/2 : ℝ) < u.re} = Complex.reCLM.toLinearMap ⁻¹' (Set.Ioi (-1/2)) := by
        ext u; rfl
      rw [h]; exact (convex_Ioi (-1/2)).linear_preimage Complex.reCLM.toLinearMap
    · have h : {u : ℂ | ‖u + 1‖ < 1/r} = Metric.ball (-1 : ℂ) (1/r) := by
        ext u; rw [Metric.mem_ball, dist_eq_norm]; simp
      rw [h]; exact convex_ball _ _
  have hVpre : IsPreconnected V := hVconv.isPreconnected
  set G : ℂ → ℂ := fun u => u * ζ / (1 + u) with hGdef
  have hGcont : ContinuousOn G V := by
    rw [hGdef]
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuous_id.mul continuous_const).continuousOn
    · exact (continuous_const.add continuous_id).continuousOn
    · intro u hu hcon
      have hre : u.re = -1 := by
        have hc := congrArg Complex.re hcon; simp at hc; linarith
      rw [hVdef] at hu
      simp only [Set.mem_ofPred_eq] at hu
      linarith [hu.1]
  have hGimage : G '' V = Metric.ball (0:ℂ) 1 \ Metric.closedBall ζ r := by
    apply Set.Subset.antisymm
    · rintro _ ⟨u, hu, rfl⟩
      rw [hVdef] at hu
      simp only [Set.mem_ofPred_eq] at hu
      rw [hSmem]
      have h1une : 1 + u ≠ 0 := by
        intro hc; have := congrArg Complex.re hc; simp at this; linarith [hu.1]
      have hpos : 0 < ‖1 + u‖ := norm_pos_iff.mpr h1une
      have hlt : ‖u‖ < ‖1 + u‖ := norm_lt_norm_one_add hu.1
      refine ⟨?_, ?_⟩
      · show ‖u * ζ / (1 + u)‖ < 1
        rw [norm_div, norm_mul, hζ, mul_one, div_lt_one hpos]
        exact hlt
      · show r < ‖u * ζ / (1 + u) - ζ‖
        have heq : u * ζ / (1 + u) - ζ = -ζ / (1 + u) := by field_simp; ring
        rw [heq, norm_div, norm_neg, hζ]
        rw [lt_div_iff₀ hpos]
        have hu2' : ‖1 + u‖ < 1/r := by rw [add_comm]; exact hu.2
        have := (lt_div_iff₀ hr).mp hu2'
        rwa [mul_comm] at this
    · intro w hw
      rw [hSmem] at hw
      have hζw : ζ - w ≠ 0 := by
        intro h
        have hwζ : w = ζ := by linear_combination -h
        rw [hwζ, hζ] at hw
        exact absurd hw.1 (by norm_num)
      set u : ℂ := w / (ζ - w) with hudef
      have h1u : 1 + u = ζ / (ζ - w) := by rw [hudef]; field_simp; ring
      have hweq : w = u * ζ / (1 + u) := by
        rw [hudef]
        have h1une : (1 : ℂ) + w / (ζ - w) ≠ 0 := by rw [h1u]; exact div_ne_zero hζne hζw
        rw [eq_div_iff h1une]; field_simp; ring
      have hzw : r < ‖ζ - w‖ := by
        have h : ‖ζ - w‖ = ‖w - ζ‖ := by rw [← neg_sub w ζ, norm_neg]
        linarith [hw.2, h]
      have hpos2 : 0 < ‖ζ - w‖ := lt_trans hr hzw
      have hu_norm : ‖u‖ = ‖w‖ / ‖ζ - w‖ := by rw [hudef, norm_div]
      have h1u_norm : ‖1 + u‖ = 1 / ‖ζ - w‖ := by rw [h1u, norm_div, hζ]
      refine ⟨u, ?_, ?_⟩
      · rw [hVdef]
        simp only [Set.mem_ofPred_eq]
        constructor
        · apply neg_half_lt_re_of_norm_lt
          rw [hu_norm, h1u_norm, div_lt_div_iff₀ hpos2 hpos2]
          exact mul_lt_mul_of_pos_right hw.1 hpos2
        · have hu1 : u + 1 = ζ / (ζ - w) := by rw [add_comm, h1u]
          rw [hu1, norm_div, hζ, div_lt_div_iff₀ hpos2 hr]
          simp only [one_mul]
          exact hzw
      · show u * ζ / (1 + u) = w
        exact hweq.symm
  rw [← hGimage]
  exact hVpre.image G hGcont

end Work.RPB.B1a

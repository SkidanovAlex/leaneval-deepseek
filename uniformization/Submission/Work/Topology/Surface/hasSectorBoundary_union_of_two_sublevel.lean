import Mathlib
import Submission.Work.SimplyConnected.ABS.RegularPieceDefs
import Submission.Work.Topology.Surface.hasSectorBoundary_transfer_chart

/-!
# The cone condition at a crossing of two smooth level sets

This module isolates the *aggregation engine* of the two-ball sector analysis in the form that works
in **any** ambient atlas chart, and therefore for a union of chart balls taken in *different* charts:

`Work.Topology.Surface.hasSectorBoundary_union_of_two_sublevel`.

Suppose `W₁, W₂ ⊆ X` are, near `p`, contained in the sub-level sets of two real functions `u₁, u₂`
(`x ∈ Wᵢ ⟹ uᵢ x ≤ uᵢ p`), each with a *non-zero* derivative `Lᵢ` at `p` (expressed in the chart
an atlas chart `d` at `p`), and such that the two half-planes `{L₁ > 0}`, `{L₂ > 0}` have a common sector.  Then
`W₁ ∪ W₂` satisfies the cone condition at `p`.

## Why the naive version would be wrong, and what replaces it

For a *round* chart ball the sub-level description is *exact*: the ball lies in the half-plane
`{L < 0}` determined by the outward conormal `L`, and the elementary `hasSectorBoundary_union_of_two_oneSided`
of `region_with_sector_boundary.lean` handles two such balls in one chart.  But when a ball of a chart
`c₂` is read in another chart `c₁` (which is what a union of chart balls in *different* charts needs),
its boundary is the image of a circle under the transition, and the exact one-sidedness is **false**:
points of the transported ball may lie strictly on the `{L > 0}` side of the transported conormal, by
an amount `O(‖ζ‖²)`.  What survives is the *strictly inside* cone

  `C_η = {h : η ‖h‖ < L₁ h and η ‖h‖ < L₂ h}`  (`η > 0`),

because on it the derivative dominates the second-order remainder: `η ‖ζ‖` beats `o(‖ζ‖)`.  The
functionals describing `C_η` are produced by `exists_wedge_margin_of_pair`
(`Work.Topology.Surface.exists_wedge_margin_of_pair`), and the little-`o` estimate of each derivative
supplies the neighbourhood on which the sign is decided.

This is the same mechanism as `Work.SimplyConnected.ABS.hasSectorBoundary_of_local_sublevel` (the
single-function case), and it reduces to it for `W₂ = ∅`.

The chart is an explicit parameter `d` (an atlas chart through `p`) rather than `chartAt ℂ p`, because
the applications run in the chart of a chart ball whose boundary passes through `p`; the
`chartAt`-form is the special case `d := chartAt ℂ p`.
-/

open Set Metric
open scoped Topology Manifold ContDiff

noncomputable section

namespace Work.Topology.Surface

/-- **The cone condition at a crossing of two smooth level sets, in an atlas chart `d`.**

`u₁, u₂ : X → ℝ` have non-zero derivatives `L₁, L₂` at `p` (in the chart at `p`), the half-planes
`{L₁ > 0}` and `{L₂ > 0}` meet, and `Wᵢ` lies in the sub-level set `{uᵢ ≤ uᵢ p}` near `p`.  Then
`W₁ ∪ W₂` satisfies the cone condition at `p`. -/
theorem hasSectorBoundary_union_of_two_sublevel {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] {d : OpenPartialHomeomorph X ℂ} (hd : d ∈ atlas ℂ X) {p : X}
    (hpd : p ∈ d.source) {W₁ W₂ : Set X} {u₁ u₂ : X → ℝ} {L₁ L₂ : ℂ →L[ℝ] ℝ}
    (hderiv₁ : HasFDerivAt (fun z : ℂ => u₁ (d.symm z)) L₁ (d p))
    (hL₁ : L₁ ≠ 0)
    (hderiv₂ : HasFDerivAt (fun z : ℂ => u₂ (d.symm z)) L₂ (d p))
    (hL₂ : L₂ ≠ 0)
    (hcross : ∃ w : ℂ, 0 < L₁ w ∧ 0 < L₂ w)
    (hside₁ : ∀ᶠ y in 𝓝 p, y ∈ W₁ → ¬ (u₁ p < u₁ y))
    (hside₂ : ∀ᶠ y in 𝓝 p, y ∈ W₂ → ¬ (u₂ p < u₂ y)) :
    Work.SimplyConnected.ABS.HasSectorBoundary (W₁ ∪ W₂) p := by
  classical
  obtain ⟨P, Q, η, hηpos, hP, hQ, hwit, hmargin⟩ :=
    exists_wedge_margin_of_pair hL₁ hL₂ hcross
  set z₀ : ℂ := d p with hz₀
  set φ₁ : ℂ → ℝ := fun z => u₁ (d.symm z) with hφ₁
  set φ₂ : ℂ → ℝ := fun z => u₂ (d.symm z) with hφ₂
  have hφ₁z₀ : φ₁ z₀ = u₁ p := by
    show u₁ (d.symm (d p)) = u₁ p
    rw [d.left_inv hpd]
  have hφ₂z₀ : φ₂ z₀ = u₂ p := by
    show u₂ (d.symm (d p)) = u₂ p
    rw [d.left_inv hpd]
  -- the little-`o` estimates
  have hev₁ : ∀ᶠ z in 𝓝 z₀, ‖φ₁ z - φ₁ z₀ - L₁ (z - z₀)‖ ≤ (η / 2) * ‖z - z₀‖ :=
    Asymptotics.isLittleO_iff.mp hderiv₁.isLittleO (by linarith)
  have hev₂ : ∀ᶠ z in 𝓝 z₀, ‖φ₂ z - φ₂ z₀ - L₂ (z - z₀)‖ ≤ (η / 2) * ‖z - z₀‖ :=
    Asymptotics.isLittleO_iff.mp hderiv₂.isLittleO (by linarith)
  rw [Metric.eventually_nhds_iff] at hev₁ hev₂
  obtain ⟨r₁, hr₁, hb₁⟩ := hev₁
  obtain ⟨r₂, hr₂, hb₂⟩ := hev₂
  rcases Filter.eventually_iff_exists_mem.mp hside₁ with ⟨V₁, hV₁mem, hV₁side⟩
  rcases Filter.eventually_iff_exists_mem.mp hside₂ with ⟨V₂, hV₂mem, hV₂side⟩
  set r : ℝ := min (min r₁ r₂) 1 with hr
  have hrpos : 0 < r := lt_min (lt_min hr₁ hr₂) one_pos
  -- the neighbourhood of `p`
  set V : Set X := (interior (V₁ ∩ V₂) ∩ d.source) ∩
    (d.source ∩ d ⁻¹' Metric.ball z₀ r) with hV
  have hVopen : IsOpen V := by
    rw [hV]
    exact (isOpen_interior.inter d.open_source).inter
      (ContinuousOn.isOpen_inter_preimage d.continuousOn_toFun
        d.open_source Metric.isOpen_ball)
  have hpV : p ∈ V := by
    rw [hV, hz₀]
    exact ⟨⟨mem_interior_iff_mem_nhds.mpr (Filter.inter_mem hV₁mem hV₂mem), hpd⟩,
      hpd, Metric.mem_ball_self hrpos⟩
  have hVsub : V ⊆ d.source := fun x hx => hx.1.2
  refine ⟨d, V, P, Q, hd, hVopen, hpV, hVsub, hpd, hP, hQ, hwit, ?_⟩
  intro x hx
  rintro ⟨hPx, hQx⟩
  obtain ⟨hxW, hxV⟩ := hx
  obtain ⟨⟨hxint, hxsrc⟩, hxsrc', hxball⟩ := hxV
  have hxV₁ : x ∈ V₁ := interior_subset hxint |>.1
  have hxV₂ : x ∈ V₂ := interior_subset hxint |>.2
  set ζ : ℂ := d x - z₀ with hζ
  have hζball : d x ∈ Metric.ball z₀ r := hxball
  have hζlt : ‖ζ‖ < r := by
    rw [hζ, ← dist_eq_norm]
    exact Metric.mem_ball.mp hζball
  have hm := hmargin ζ hPx hQx
  have hxid : d.symm (d x) = x := d.left_inv hxsrc
  have hζdist : ‖ζ‖ < min r₁ r₂ :=
    lt_of_lt_of_le hζlt (min_le_left _ _)
  have hb₁' : |φ₁ (d x) - φ₁ z₀ - L₁ ζ| ≤ (η / 2) * ‖ζ‖ := by
    have h := hb₁ (y := d x) ?_
    · simpa [hζ] using h
    · show dist (d x) z₀ < r₁
      rw [dist_eq_norm, ← hζ]
      exact lt_of_lt_of_le hζlt (le_trans (min_le_left _ _) (min_le_left _ _))
  have hb₂' : |φ₂ (d x) - φ₂ z₀ - L₂ ζ| ≤ (η / 2) * ‖ζ‖ := by
    have h := hb₂ (y := d x) ?_
    · simpa [hζ] using h
    · show dist (d x) z₀ < r₂
      rw [dist_eq_norm, ← hζ]
      exact lt_of_lt_of_le hζlt (le_trans (min_le_left _ _) (min_le_right _ _))
  have hup₁ : φ₁ (d x) - φ₁ z₀ > 0 := by
    have h1 := (abs_le.mp hb₁').1
    have h2 : (η / 2) * ‖ζ‖ + (η / 2) * ‖ζ‖ < L₁ ζ := by
      have heq : (η / 2) * ‖ζ‖ + (η / 2) * ‖ζ‖ = η * ‖ζ‖ := by ring
      rw [heq]; exact hm.1
    have hnn : (0 : ℝ) ≤ (η / 2) * ‖ζ‖ := by positivity
    linarith
  have hup₂ : φ₂ (d x) - φ₂ z₀ > 0 := by
    have h1 := (abs_le.mp hb₂').1
    have h2 : (η / 2) * ‖ζ‖ + (η / 2) * ‖ζ‖ < L₂ ζ := by
      have heq : (η / 2) * ‖ζ‖ + (η / 2) * ‖ζ‖ = η * ‖ζ‖ := by ring
      rw [heq]; exact hm.2
    have hnn : (0 : ℝ) ≤ (η / 2) * ‖ζ‖ := by positivity
    linarith
  have hu₁ : u₁ p < u₁ x := by
    have h := hup₁
    simp only [hφ₁] at h
    rw [hxid] at h
    linarith
  have hu₂ : u₂ p < u₂ x := by
    have h := hup₂
    simp only [hφ₂] at h
    rw [hxid] at h
    linarith
  rcases hxW with h | h
  · exact hV₁side x hxV₁ h hu₁
  · exact hV₂side x hxV₂ h hu₂

/-! ## Two chart balls in possibly different charts

The engine above is applied here to the concrete case that matters for a *multi-chart* union of chart
balls: `p` lies on the boundary of the chart ball of `c₁` around `a₁` of radius `ρ₁` and also on the
boundary of the chart ball of `c₂` around `a₂` of radius `ρ₂` (the two charts being arbitrary atlas
charts through `p`).  Reading both balls in the chart `c₁`, the first is round (its defining function
has derivative `2 • innerSL ℝ (c₁ p - a₁)`) and the second is the image of a round ball under the
transition `c₂ ∘ c₁⁻¹`, whose defining function has derivative
`2 • (innerSL ℝ (c₂ p - a₂)) ∘SL b`, where `b` is the transition's derivative at `c₁ p`.

The hypothesis `hcross` says that the two conormals — the second transported by `b` — are not
opposite, i.e. that the two balls are not *externally tangent* at `p`; this is necessary (external
tangency leaves a cusp, which contains no cone of positive angle) and it is the general-position
condition that a tile cover has to be put in. -/

/-- **The cone condition where two chart balls of possibly different charts meet.** -/
theorem hasSectorBoundary_union_of_two_chartBalls {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]
    {c₁ c₂ : OpenPartialHomeomorph X ℂ} (hc₁ : c₁ ∈ atlas ℂ X) (hc₂ : c₂ ∈ atlas ℂ X)
    {a₁ a₂ : ℂ} {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 < ρ₁) (hρ₂ : 0 < ρ₂) {p : X}
    (hp₁ : p ∈ c₁.source) (hp₂ : p ∈ c₂.source)
    (hbd₁ : ‖c₁ p - a₁‖ = ρ₁) (hbd₂ : ‖c₂ p - a₂‖ = ρ₂)
    {b : ℂ →L[ℂ] ℂ} (hb : HasFDerivAt (fun ζ : ℂ => c₂ (c₁.symm ζ)) b (c₁ p)) (hbne : b ≠ 0)
    (hcross : ∃ w : ℂ, 0 < inner ℝ (c₁ p - a₁) w ∧ 0 < inner ℝ (c₂ p - a₂) (b w)) :
    Work.SimplyConnected.ABS.HasSectorBoundary
      ((c₁.source ∩ c₁ ⁻¹' Metric.ball a₁ ρ₁) ∪ (c₂.source ∩ c₂ ⁻¹' Metric.ball a₂ ρ₂)) p := by
  classical
  -- the first ball: read in its own chart it is round, with conormal `2 • innerSL ℝ (c₁ p - a₁)`
  have hd₁ : HasFDerivAt (fun ζ : ℂ => ‖c₁ (c₁.symm ζ) - a₁‖ ^ 2 - ρ₁ ^ 2)
      ((2 : ℕ) • (innerSL ℝ (c₁ p - a₁))) (c₁ p) := by
    have hbase : HasFDerivAt (fun w : ℂ => w - a₁) (ContinuousLinearMap.id ℝ ℂ) (c₁ p) :=
      (hasFDerivAt_id (𝕜 := ℝ) (c₁ p)).sub_const a₁
    have hsq : HasFDerivAt (fun w : ℂ => ‖w - a₁‖ ^ 2)
        ((2 : ℕ) • ((innerSL ℝ) (c₁ p - a₁) ∘SL ContinuousLinearMap.id ℝ ℂ)) (c₁ p) :=
      hbase.norm_sq
    have hsq' : HasFDerivAt (fun w : ℂ => ‖w - a₁‖ ^ 2)
        ((2 : ℕ) • (innerSL ℝ (c₁ p - a₁))) (c₁ p) := by
      convert hsq using 1
      ext x
      rfl
    have hcongr : (fun ζ : ℂ => ‖c₁ (c₁.symm ζ) - a₁‖ ^ 2 - ρ₁ ^ 2)
        =ᶠ[𝓝 (c₁ p)] (fun w : ℂ => ‖w - a₁‖ ^ 2 - ρ₁ ^ 2) := by
      filter_upwards [c₁.open_target.mem_nhds (c₁.map_source hp₁)] with ζ hζ
      rw [c₁.right_inv hζ]
    exact (hsq'.sub_const (ρ₁ ^ 2)).congr_of_eventuallyEq hcongr
  -- the second ball, read in the chart `c₁`
  have hd₂ := hasFDerivAt_chartBall_sq_sub (c := c₂) (d := c₁) (a := a₂) (ρ := ρ₂) (p := p)
    hp₁ hb
  -- non-vanishing of the two derivatives
  have hL₁ne : ((2 : ℕ) • (innerSL ℝ (c₁ p - a₁))) ≠ 0 := by
    intro h0
    have h1 : (2 : ℝ) * inner ℝ (c₁ p - a₁) (c₁ p - a₁) = 0 := by
      have h2 := congrFun (congrArg DFunLike.coe h0) (c₁ p - a₁)
      rw [smul_apply, innerSL_apply_apply, nsmul_eq_mul] at h2
      simpa using h2
    rw [real_inner_self_eq_norm_sq] at h1
    have h3 : 0 < ‖c₁ p - a₁‖ := by rw [hbd₁]; exact hρ₁
    nlinarith [h1, h3]
  have hL₂ne : ((2 : ℕ) • ((innerSL ℝ) (c₂ p - a₂) ∘SL (b.restrictScalars ℝ))) ≠ 0 := by
    have hb1 : b 1 ≠ 0 := by
      intro h0
      refine hbne (ContinuousLinearMap.ext fun z => ?_)
      rw [complexLinear_apply_one_mul b z, h0, mul_zero]
      simp
    have hbsurj : Function.Surjective b := fun w => ⟨w * (b 1)⁻¹, by
      rw [complexLinear_apply_one_mul b, mul_assoc, inv_mul_cancel₀ hb1, mul_one]⟩
    obtain ⟨z, hz⟩ : ∃ z : ℂ, b z = c₂ p - a₂ := hbsurj (c₂ p - a₂)
    intro h0
    have h1 : (2 : ℝ) * inner ℝ (c₂ p - a₂) (c₂ p - a₂) = 0 := by
      have harg : (b.restrictScalars ℝ) z = b z := rfl
      have h2 := congrFun (congrArg DFunLike.coe h0) z
      rw [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
        nsmul_eq_mul, harg, hz] at h2
      simpa using h2
    rw [real_inner_self_eq_norm_sq] at h1
    have h3 : 0 < ‖c₂ p - a₂‖ := by rw [hbd₂]; exact hρ₂
    nlinarith [h1, h3]
  -- a common positive witness for the two derivatives
  obtain ⟨w, hw₁, hw₂⟩ := hcross
  have hcross' : ∃ w : ℂ,
      0 < ((2 : ℕ) • (innerSL ℝ (c₁ p - a₁))) w ∧
      0 < ((2 : ℕ) • ((innerSL ℝ) (c₂ p - a₂) ∘SL (b.restrictScalars ℝ))) w := by
    refine ⟨w, ?_, ?_⟩
    · rw [smul_apply, innerSL_apply_apply, nsmul_eq_mul]
      exact mul_pos (by norm_num) hw₁
    · rw [smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply, nsmul_eq_mul,
        show (b.restrictScalars ℝ) w = b w from rfl]
      exact mul_pos (by norm_num) hw₂
  -- the two defining functions are sub-level descriptions of the two balls at `p`
  have hside₁ : ∀ᶠ y in 𝓝 p, y ∈ (c₁.source ∩ c₁ ⁻¹' Metric.ball a₁ ρ₁) →
      ¬ ((fun x : X => ‖c₁ x - a₁‖ ^ 2 - ρ₁ ^ 2) p
          < (fun x : X => ‖c₁ x - a₁‖ ^ 2 - ρ₁ ^ 2) y) := by
    filter_upwards with y hy
    have h2 : ‖c₁ y - a₁‖ < ρ₁ := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hy.2
    have hp : ‖c₁ p - a₁‖ ^ 2 - ρ₁ ^ 2 = 0 := by rw [hbd₁]; ring
    have hy' : ‖c₁ y - a₁‖ ^ 2 - ρ₁ ^ 2 < 0 := by
      nlinarith [hρ₁, h2, norm_nonneg (c₁ y - a₁)]
    rw [hp]; exact not_lt.mpr hy'.le
  have hside₂ : ∀ᶠ y in 𝓝 p, y ∈ (c₂.source ∩ c₂ ⁻¹' Metric.ball a₂ ρ₂) →
      ¬ ((fun x : X => ‖c₂ x - a₂‖ ^ 2 - ρ₂ ^ 2) p
          < (fun x : X => ‖c₂ x - a₂‖ ^ 2 - ρ₂ ^ 2) y) := by
    filter_upwards with y hy
    have h2 : ‖c₂ y - a₂‖ < ρ₂ := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hy.2
    have hp : ‖c₂ p - a₂‖ ^ 2 - ρ₂ ^ 2 = 0 := by rw [hbd₂]; ring
    have hy' : ‖c₂ y - a₂‖ ^ 2 - ρ₂ ^ 2 < 0 := by
      nlinarith [hρ₂, h2, norm_nonneg (c₂ y - a₂)]
    rw [hp]; exact not_lt.mpr hy'.le
  exact hasSectorBoundary_union_of_two_sublevel (d := c₁)
    (u₁ := fun x : X => ‖c₁ x - a₁‖ ^ 2 - ρ₁ ^ 2)
    (u₂ := fun x : X => ‖c₂ x - a₂‖ ^ 2 - ρ₂ ^ 2)
    (W₁ := c₁.source ∩ c₁ ⁻¹' Metric.ball a₁ ρ₁)
    (W₂ := c₂.source ∩ c₂ ⁻¹' Metric.ball a₂ ρ₂)
    (L₁ := (2 : ℕ) • (innerSL ℝ (c₁ p - a₁)))
    (L₂ := (2 : ℕ) • ((innerSL ℝ) (c₂ p - a₂) ∘SL (b.restrictScalars ℝ)))
    hc₁ hp₁ hd₁ hL₁ne hd₂ hL₂ne hcross' hside₁ hside₂

end Work.Topology.Surface

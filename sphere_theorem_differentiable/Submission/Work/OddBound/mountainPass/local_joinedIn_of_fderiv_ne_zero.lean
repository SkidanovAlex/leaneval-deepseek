import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.mountainPass

open Set Metric
open scoped Topology

/-- **Local path connectedness of a sublevel set at a regular point.**

Let `f : E → ℝ` be `C¹` on a real normed space `E`, let `z` be a point with `f z = Λ`, and suppose
that the derivative of `f` at `z` does not vanish.  Then the sublevel set `{w | f w < Λ}` is locally
path connected at `z`: there is `ρ > 0` such that any two points of `{w | f w < Λ}` at distance
`< ρ` from `z` can be joined by a path inside `{w | f w < Λ}`.

The proof linearises: with `g = f'(z) ≠ 0` and a unit vector `u` satisfying `g u > 0`, the
perturbation `φ = f - Λ - g(· - z)` is `C¹` with `φ z = 0`, hence `‖φ p - φ q‖ ≤ ε ‖p - q‖` on a
ball around `z`.  Two points of the sublevel set at distance `< ρ` are joined through the "deep"
points `x - ρ u` and `y - ρ u`: on the two rays `x → x - ρ u`, `y → y - ρ u` the function `f`
decreases by at least `t ρ (γ - ε)`, and on the segment joining the two deep points `f` is bounded
by `Λ - γρ/4 < Λ`. -/
theorem local_joinedIn_of_fderiv_ne_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ 1 f) {Λ : ℝ} {z : E} (hz : f z = Λ)
    (hgz : fderiv ℝ f z ≠ 0) :
    ∃ ρ > 0, ∀ x y : E, dist x z < ρ → dist y z < ρ → f x < Λ → f y < Λ →
      JoinedIn {w : E | f w < Λ} x y := by
  classical
  -- ## The derivative `g = f'(z)`, a nonzero continuous linear functional.
  set g : E →L[ℝ] ℝ := fderiv ℝ f z with hg
  have hgne : g ≠ 0 := hgz
  -- ## A unit vector `u` on which `g` is positive.
  obtain ⟨u, hu_norm, hu_pos⟩ : ∃ u : E, ‖u‖ = 1 ∧ 0 < g u := by
    obtain ⟨w, hw⟩ : ∃ w : E, g w ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hgne (ContinuousLinearMap.ext h)
    have hwn : w ≠ 0 := fun h0 => hw (by rw [h0, map_zero])
    have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hwn
    set v : E := (‖w‖)⁻¹ • w with hv
    have hvnorm : ‖v‖ = 1 := by
      rw [hv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w))]
      exact inv_mul_cancel₀ (ne_of_gt hwnorm)
    have hgv : g v ≠ 0 := by
      intro h
      rw [hv, map_smul, smul_eq_mul] at h
      exact hw ((mul_eq_zero.mp h).resolve_left (inv_ne_zero (ne_of_gt hwnorm)))
    rcases lt_or_gt_of_ne hgv with hneg | hpos
    · exact ⟨-v, by rw [norm_neg, hvnorm], by rw [map_neg]; exact neg_pos.mpr hneg⟩
    · exact ⟨v, hvnorm, hpos⟩
  set γ : ℝ := g u with hγ
  have hγpos : 0 < γ := by rw [hγ]; exact hu_pos
  set ε : ℝ := γ / 4 with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  -- ## A ball around `z` on which `f'` is within `ε` of `g`.
  have hcontN : ContinuousAt (fun w : E => ‖fderiv ℝ f w - g‖) z :=
    (((hf.continuous_fderiv (by norm_num)).sub continuous_const).norm).continuousAt
  have hev : ∀ᶠ w in 𝓝 z, ‖fderiv ℝ f w - g‖ < ε :=
    hcontN.eventually_lt continuousAt_const (by rw [← hg]; simpa using hεpos)
  obtain ⟨δ, hδpos, hδball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  -- ## The geometric parameters: `ρ = δ/2` and the step length `ρ`.
  set ρ : ℝ := δ / 2 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; linarith
  have hρδ : ρ < δ := by rw [hρ]; linarith
  have hδ2 : δ = 2 * ρ := by linarith
  have hρρδ : ρ + ρ = δ := by linarith
  -- ## The linearised function `φ = f - Λ - g(· - z)`.
  set φ : E → ℝ := fun w => f w - (g w + (Λ - g z)) with hφ
  have hφz : φ z = 0 := by
    simp only [hφ]
    rw [hz]
    ring
  have hfeq : ∀ q : E, f q = Λ + g (q - z) + φ q := by
    intro q
    simp only [hφ, map_sub]
    ring
  have hfid : ∀ q r : E, f q - f r = g (q - r) + (φ q - φ r) := by
    intro q r
    have h2 : g (q - z) = g (q - r) + g (r - z) := by
      have h : q - z = (q - r) + (r - z) := by abel
      rw [h, map_add]
    rw [hfeq q, hfeq r, h2]
    ring
  have hφderiv : ∀ w : E, HasFDerivAt φ (fderiv ℝ f w - g) w := by
    intro w
    have h1 : HasFDerivAt (fun v : E => g v + (Λ - g z)) g w :=
      (g.hasFDerivAt (x := w)).add_const (Λ - g z)
    have h2 : HasFDerivAt (fun v : E => f v - (g v + (Λ - g z))) (fderiv ℝ f w - g) w :=
      (((hf.differentiable (by norm_num)).differentiableAt).hasFDerivAt).sub h1
    rw [hφ]
    exact h2
  -- ## `φ` is `ε`-Lipschitz on the ball.
  have hlip : ∀ p q : E, p ∈ Metric.ball z δ → q ∈ Metric.ball z δ →
      |φ p - φ q| ≤ ε * ‖p - q‖ := by
    intro p q hp hq
    have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := φ) (f' := fun w => fderiv ℝ f w - g) (s := Metric.ball z δ) (C := ε)
      (fun w _ => (hφderiv w).hasFDerivWithinAt)
      (fun w hw => (hδball w hw).le)
      (convex_ball z δ) hq hp
    rwa [Real.norm_eq_abs] at h
  have hφbound : ∀ q : E, ‖q - z‖ < δ → |φ q| ≤ ε * ‖q - z‖ := by
    intro q hq
    have h := hlip q z (Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hq))
      (Metric.mem_ball.mpr (by simpa using hδpos))
    rwa [hφz, sub_zero] at h
  -- ## Points of the sublevel set that are close to `z` have `g (q - z) < ε ρ`.
  have hshallow : ∀ q : E, dist q z < ρ → f q < Λ → g (q - z) < ε * ρ := by
    intro q hq hfq
    have hqn : ‖q - z‖ < ρ := by rw [← dist_eq_norm]; exact hq
    have hqδ : ‖q - z‖ < δ := lt_trans hqn hρδ
    have h1 : Λ + g (q - z) + φ q < Λ := by
      rw [← hfeq q]; exact hfq
    have h2 : |φ q| ≤ ε * ‖q - z‖ := hφbound q hqδ
    have h3 : ε * ‖q - z‖ < ε * ρ := mul_lt_mul_of_pos_left hqn hεpos
    linarith [neg_le_abs (φ q), h1, h2, h3]
  -- ## Moving a point of the sublevel set along `-u` keeps it in the sublevel set.
  have hray : ∀ p : E, dist p z < ρ → f p < Λ →
      ∀ t ∈ unitInterval, f (p - (t * ρ) • u) < Λ := by
    intro p hpz hfp t ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have hpρ : ‖p - z‖ < ρ := by rw [← dist_eq_norm]; exact hpz
    have hpb : p ∈ Metric.ball z δ := Metric.mem_ball.mpr (lt_trans hpz hρδ)
    have hta : t * ρ ≤ ρ := by simpa using mul_le_mul_of_nonneg_right ht1 hρpos.le
    set q : E := p - (t * ρ) • u with hq
    have hqδ : ‖q - z‖ < δ := by
      have h1 : q - z = (p - z) - (t * ρ) • u := by rw [hq]; abel
      have h2 : ‖(t * ρ) • u‖ = t * ρ := by
        rw [norm_smul, Real.norm_eq_abs, hu_norm, mul_one,
          abs_of_nonneg (mul_nonneg ht0 hρpos.le)]
      have h3 : ‖(p - z) - (t * ρ) • u‖ ≤ ‖p - z‖ + ‖(t * ρ) • u‖ := norm_sub_le _ _
      have h4 : ‖(p - z) - (t * ρ) • u‖ < δ := by
        rw [h2] at h3
        have hl : ‖p - z‖ + t * ρ < ρ + ρ := by linarith
        linarith [hρρδ]
      rwa [← h1] at h4
    have hqb : q ∈ Metric.ball z δ := Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hqδ)
    have hφqp : |φ q - φ p| ≤ ε * (t * ρ) := by
      have h := hlip q p hqb hpb
      have hnp : ‖q - p‖ = t * ρ := by
        have h1 : q - p = -((t * ρ) • u) := by rw [hq]; abel
        rw [h1, norm_neg, norm_smul, Real.norm_eq_abs, hu_norm, mul_one,
          abs_of_nonneg (mul_nonneg ht0 hρpos.le)]
      rwa [hnp] at h
    have hgqp : g (q - p) = -(t * ρ) * γ := by
      have h1 : q - p = -((t * ρ) • u) := by rw [hq]; abel
      rw [h1, map_neg, map_smul, smul_eq_mul, hγ]
      ring
    have hsplit : f q = f p + g (q - p) + (φ q - φ p) := by linarith [hfid q p]
    have hle : f q ≤ f p - (t * ρ) * (γ - ε) := by
      rw [hsplit, hgqp]
      have h5 : φ q - φ p ≤ ε * (t * ρ) := le_trans (le_abs_self _) hφqp
      have h6 : -(t * ρ) * γ + ε * (t * ρ) = -(t * ρ) * (γ - ε) := by ring
      linarith
    have h7 : 0 ≤ (t * ρ) * (γ - ε) :=
      mul_nonneg (mul_nonneg ht0 hρpos.le) (by linarith [hγpos, hε])
    linarith [hle, h7, hfp]
  -- ## The straight segment of two points of the sublevel set.
  have hseg1 : ∀ p : E, dist p z < ρ → f p < Λ →
      JoinedIn {w : E | f w < Λ} p (p - ρ • u) := by
    intro p hpz hfp
    refine JoinedIn.ofLine (f := fun t : ℝ => p - (t * ρ) • u) ?_ ?_ ?_ ?_
    · fun_prop
    · simp
    · simp
    · rintro y ⟨t, ht, rfl⟩
      exact hray p hpz hfp t ht
  -- ## The segment joining `x - ρ u` and `y - ρ u`, which sits strictly below `Λ`.
  have hseg2 : ∀ x y : E, dist x z < ρ → f x < Λ → dist y z < ρ → f y < Λ →
      JoinedIn {w : E | f w < Λ} (x - ρ • u) (y - ρ • u) := by
    intro x y hxz hfx hyz hfy
    have haux : ‖ρ • u‖ = ρ := by
      rw [norm_smul, Real.norm_eq_abs, hu_norm, mul_one, abs_of_nonneg hρpos.le]
    have hx'δ : ‖(x - ρ • u) - z‖ < δ := by
      have h1 : (x - ρ • u) - z = (x - z) - ρ • u := by abel
      have h3 : ‖(x - z) - ρ • u‖ ≤ ‖x - z‖ + ‖ρ • u‖ := norm_sub_le _ _
      have h4 : ‖(x - z) - ρ • u‖ < δ := by
        rw [haux] at h3
        have h5 : ‖x - z‖ < ρ := by rw [← dist_eq_norm]; exact hxz
        linarith [hρρδ]
      rwa [← h1] at h4
    have hy'δ : ‖(y - ρ • u) - z‖ < δ := by
      have h1 : (y - ρ • u) - z = (y - z) - ρ • u := by abel
      have h3 : ‖(y - z) - ρ • u‖ ≤ ‖y - z‖ + ‖ρ • u‖ := norm_sub_le _ _
      have h4 : ‖(y - z) - ρ • u‖ < δ := by
        rw [haux] at h3
        have h5 : ‖y - z‖ < ρ := by rw [← dist_eq_norm]; exact hyz
        linarith [hρρδ]
      rwa [← h1] at h4
    refine JoinedIn.ofLine (f := fun t : ℝ => (1 - t) • (x - ρ • u) + t • (y - ρ • u)) ?_ ?_ ?_ ?_
    · fun_prop
    · simp
    · simp
    · rintro w ⟨t, ht, rfl⟩
      have ht0 : 0 ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2
      set w' : E := (1 - t) • (x - ρ • u) + t • (y - ρ • u) with hw'
      have hsplit : w' - z = (1 - t) • ((x - ρ • u) - z) + t • ((y - ρ • u) - z) := by
        rw [hw']; module
      have hw'δ : ‖w' - z‖ < δ := by
        rw [hsplit]
        have hm : max ‖(x - ρ • u) - z‖ ‖(y - ρ • u) - z‖ < δ := max_lt hx'δ hy'δ
        have h4a : ‖(1 - t) • ((x - ρ • u) - z)‖ ≤ (1 - t) * ‖(x - ρ • u) - z‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - t)]
        have h4b : ‖t • ((y - ρ • u) - z)‖ ≤ t * ‖(y - ρ • u) - z‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
        have h4c : (1 - t) * ‖(x - ρ • u) - z‖
            ≤ (1 - t) * max ‖(x - ρ • u) - z‖ ‖(y - ρ • u) - z‖ :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith)
        have h4d : t * ‖(y - ρ • u) - z‖
            ≤ t * max ‖(x - ρ • u) - z‖ ‖(y - ρ • u) - z‖ :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) ht0
        have h4e : (1 - t) * max ‖(x - ρ • u) - z‖ ‖(y - ρ • u) - z‖
            + t * max ‖(x - ρ • u) - z‖ ‖(y - ρ • u) - z‖
            = max ‖(x - ρ • u) - z‖ ‖(y - ρ • u) - z‖ := by ring
        have h5 := norm_add_le ((1 - t) • ((x - ρ • u) - z)) (t • ((y - ρ • u) - z))
        linarith
      have hφw : φ w' ≤ ε * δ := by
        have h := hφbound w' hw'δ
        have h2 : ε * ‖w' - z‖ < ε * δ := mul_lt_mul_of_pos_left hw'δ hεpos
        have h3 : φ w' ≤ |φ w'| := le_abs_self _
        linarith
      have hgw : g (w' - z) ≤ ε * ρ - ρ * γ := by
        have hgx' : g ((x - ρ • u) - z) ≤ ε * ρ - ρ * γ := by
          have h1 : (x - ρ • u) - z = (x - z) - ρ • u := by abel
          have h2 : g (x - z) ≤ ε * ρ := (hshallow x hxz hfx).le
          have h3 : g ((x - z) - ρ • u) = g (x - z) - ρ * γ := by
            rw [map_sub, map_smul, smul_eq_mul, hγ]
          rw [h1, h3]
          linarith
        have hgy' : g ((y - ρ • u) - z) ≤ ε * ρ - ρ * γ := by
          have h1 : (y - ρ • u) - z = (y - z) - ρ • u := by abel
          have h2 : g (y - z) ≤ ε * ρ := (hshallow y hyz hfy).le
          have h3 : g ((y - z) - ρ • u) = g (y - z) - ρ * γ := by
            rw [map_sub, map_smul, smul_eq_mul, hγ]
          rw [h1, h3]
          linarith
        have h4 : (1 - t) * g ((x - ρ • u) - z) ≤ (1 - t) * (ε * ρ - ρ * γ) :=
          mul_le_mul_of_nonneg_left hgx' (by linarith)
        have h5 : t * g ((y - ρ • u) - z) ≤ t * (ε * ρ - ρ * γ) :=
          mul_le_mul_of_nonneg_left hgy' ht0
        have h6 : (1 - t) * (ε * ρ - ρ * γ) + t * (ε * ρ - ρ * γ) = ε * ρ - ρ * γ := by ring
        rw [hsplit, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        linarith [h4, h5, h6]
      have hsum : ε * ρ - ρ * γ + ε * δ = -(γ * ρ / 4) := by
        rw [hε, hδ2]
        ring_nf
      have hgr : 0 < γ * ρ / 4 := by
        have := mul_pos hγpos hρpos
        linarith
      have h1 : f w' ≤ Λ + ((ε * ρ - ρ * γ) + ε * δ) := by
        rw [hfeq w', add_assoc]
        exact add_le_add (le_refl Λ) (add_le_add hgw hφw)
      have h2 : Λ + ((ε * ρ - ρ * γ) + ε * δ) < Λ := by
        have h3 : Λ + (ε * ρ - ρ * γ + ε * δ) < Λ := by
          rw [hsum]
          linarith
        linarith [h3]
      exact lt_of_le_of_lt h1 h2
  refine ⟨ρ, hρpos, fun x y hxz hyz hfx hfy => ?_⟩
  have h1 : JoinedIn {w : E | f w < Λ} x (x - ρ • u) := hseg1 x hxz hfx
  have h2 : JoinedIn {w : E | f w < Λ} (x - ρ • u) (y - ρ • u) := hseg2 x y hxz hfx hyz hfy
  have h3 : JoinedIn {w : E | f w < Λ} (y - ρ • u) y := (hseg1 y hyz hfy).symm
  exact h1.trans (h2.trans h3)

end Work.OddBound.mountainPass

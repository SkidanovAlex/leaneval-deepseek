import Mathlib

namespace Work.OddBound.mountainPass3

open scoped ContDiff Topology

/-!
# Strict sublevel points accumulate at a point with a negative-definite plane

`Work.OddBound.mountainPass3.exists_sublevel_near_of_negDefPlane_local` is the *local* form
(`ContDiffAt` instead of a global `ContDiff`) of
`Work.OddBound.mountainPass.exists_sublevel_near_of_negDefPlane`, with the hypothesis that the
point is critical dropped: the conclusion is simply that `f` takes values *strictly below* `f u`
arbitrarily close to `u`, whenever the second derivative of `f` at `u` is strictly negative on a
plane spanned by two vectors `v`, `w`.

The mathematics is a second-order Taylor expansion along a line through `u`:

* `ContDiffAt ℝ 2 f u` first gives a ball around `u` on which `f` is `C²`
  (`ContDiffAt.contDiffOn`); and it also says that `f` is differentiable at `u` with derivative
  `fderiv ℝ f u`.
* If `(fderiv ℝ f u) w < 0` for some direction `w`, then first-order Taylor at `u` already
  produces points with `f` strictly below `f u`.
* Otherwise `u` is a critical point.  Taking `w := v` (so that
  `(D²f u) w w < 0`) and applying Mathlib's second-order expansion
  `Convex.taylor_approx_two_segment` to `f` along the segment `c + s • (k • w)` (the direction is
  rescaled by a small positive `k` so that the endpoint of the segment stays inside the ball where
  `f` is `C²`) yields
  `f (u + t • w) - f u = t * (fderiv ℝ f u) w + (t²/2) * (D²f u) w w + o(t²)`; with
  `(fderiv ℝ f u) w = 0` and `(D²f u) w w < 0` the right-hand side is negative for all small
  enough `t > 0`.

The sign of the first-order term is handled once and for all in
`exists_lt_ball_of_negSecondDeriv`, which is then applied to either `v` or `-v`.
-/

/-- **Core second-order Taylor step.**  Let `g : E → ℝ` be `C²` on the ball `ball c ρ`
(`ρ > 0`), suppose `(D²g c) w w < 0` and that the first derivative of `g` at `c` in the direction
`w` is non-positive.  Then there is a point of the ball at which `g` is strictly below `g c`.

The proof is the second-order Taylor expansion of `g` along the segment
`s ↦ c + s • (k • w)`, where `k > 0` is chosen small enough that the endpoint of the segment
lies inside `ball c ρ`. -/
theorem exists_lt_ball_of_negSecondDeriv_nonpos_grad
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {c : E} {ρ : ℝ} (hρ : 0 < ρ) (hg : ContDiffOn ℝ 2 g (Metric.ball c ρ))
    {w : E} (hw : (fderiv ℝ (fderiv ℝ g) c) w w < 0) (hb : (fderiv ℝ g c) w ≤ 0) :
    ∃ x : E, dist x c < ρ ∧ g x < g c := by
  set Q : E →L[ℝ] E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ g) c with hQ
  have hc_mem : c ∈ Metric.ball c ρ := by simp [Metric.mem_ball, hρ]
  have hopen : IsOpen (Metric.ball c ρ) := Metric.isOpen_ball
  have hinter : interior (Metric.ball c ρ) = Metric.ball c ρ := hopen.interior_eq
  have hconv : Convex ℝ (Metric.ball c ρ) := convex_ball c ρ
  have hdiff : ∀ y ∈ interior (Metric.ball c ρ), HasFDerivAt g (fderiv ℝ g y) y := by
    intro y hy
    rw [hinter] at hy
    exact ((hg.differentiableOn (by norm_num)).differentiableAt (hopen.mem_nhds hy)).hasFDerivAt
  have hsec : HasFDerivWithinAt (fderiv ℝ g) Q (interior (Metric.ball c ρ)) c := by
    rw [hinter]
    have h1 : ContDiffOn ℝ 1 (fderiv ℝ g) (Metric.ball c ρ) :=
      hg.fderiv_of_isOpen hopen (by norm_num)
    exact ((h1.differentiableOn (by norm_num)).differentiableAt
      (hopen.mem_nhds hc_mem)).hasFDerivAt.hasFDerivWithinAt
  -- rescale the direction so that the whole segment stays inside the ball
  set k : ℝ := ρ / (2 * (‖w‖ + 1)) with hk
  have hkpos : 0 < k := by rw [hk]; positivity
  have hknorm : ‖k • w‖ < ρ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hkpos]
    have h1 : k * ‖w‖ ≤ k * (‖w‖ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [norm_nonneg w]) hkpos.le
    have h2 : k * (‖w‖ + 1) = ρ / 2 := by rw [hk]; field_simp
    linarith
  have hQw : Q (k • w) (k • w) < 0 := by
    have hlin : Q (k • w) (k • w) = k * k * (Q w w) := by
      simp only [ContinuousLinearMap.map_smul, smul_apply, smul_eq_mul]
      ring
    rw [hlin, hQ]
    exact mul_neg_of_pos_of_neg (mul_pos hkpos hkpos) hw
  have hb' : (fderiv ℝ g c) (k • w) ≤ 0 := by
    rw [map_smul, smul_eq_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hkpos.le hb
  -- second-order Taylor expansion along the segment
  have hT := Convex.taylor_approx_two_segment (s := Metric.ball c ρ) (f := g)
    (f' := fderiv ℝ g) (f'' := Q) (x := c) (v := 0) (w := k • w) hconv hdiff hc_mem hsec
    (by rw [hinter]; simpa using hc_mem)
    (by rw [hinter, Metric.mem_ball]; simpa [dist_eq_norm, add_sub_cancel_left] using hknorm)
  have hmain : (fun h : ℝ => g (c + h • (k • w)) - g c - h * ((fderiv ℝ g c) (k • w))
      - (h^2/2) * (Q (k • w) (k • w))) =o[𝓝[>] 0] (fun h : ℝ => h^2) := by
    simpa [smul_eq_mul] using hT
  -- the remainder is dominated by `(κ/4) h²` for small `h > 0`, where `κ = -(D²g c) (k • w)² > 0`
  set κ : ℝ := - Q (k • w) (k • w) with hκ
  have hκpos : 0 < κ := by rw [hκ]; exact neg_pos.mpr hQw
  let L : ℝ → ℝ := fun h => g (c + h • (k • w)) - g c - h * ((fderiv ℝ g c) (k • w))
    - (h^2/2) * (Q (k • w) (k • w))
  have hL : L =o[𝓝[>] (0:ℝ)] (fun h : ℝ => h^2) := hmain
  have hbound : ∀ᶠ h in 𝓝[>] (0:ℝ), ‖L h‖ ≤ (κ/4) * ‖h^2‖ := hL.def (by linarith)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhdsWithin_iff.mp hbound
  set t : ℝ := min (δ/2) (ρ / (2 * (‖k • w‖ + 1))) with ht
  have htpos : 0 < t := by rw [ht]; exact lt_min (by linarith) (by positivity)
  have htδ : t < δ := by
    rw [ht]
    have hle : min (δ / 2) (ρ / (2 * (‖k • w‖ + 1))) ≤ δ / 2 := min_le_left _ _
    linarith
  refine ⟨c + t • (k • w), ?_, ?_⟩
  · -- the chosen point stays inside the ball
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    have hle : t ≤ ρ / (2 * (‖k • w‖ + 1)) := by rw [ht]; exact min_le_right _ _
    have hval : (ρ / (2 * (‖k • w‖ + 1))) * (‖k • w‖ + 1) = ρ / 2 := by field_simp
    have h2 : t * (‖k • w‖ + 1) < ρ := by
      calc t * (‖k • w‖ + 1) ≤ (ρ / (2 * (‖k • w‖ + 1))) * (‖k • w‖ + 1) :=
            mul_le_mul_of_nonneg_right hle (by positivity)
        _ = ρ / 2 := hval
        _ < ρ := by linarith
    have h3 : t * ‖k • w‖ ≤ t * (‖k • w‖ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (k • w)]) htpos.le
    linarith
  · -- and `g` is strictly below `g c` there
    have hmem : t ∈ Metric.ball (0:ℝ) δ ∩ Set.Ioi 0 := by
      refine ⟨?_, htpos⟩
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos htpos]
      exact htδ
    have hbnd : ‖L t‖ ≤ (κ/4) * ‖t^2‖ := hδ hmem
    have hbnd' : L t ≤ (κ/4) * t^2 := by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)] at hbnd
      exact le_trans (le_abs_self (L t)) hbnd
    have hLt : L t = g (c + t • (k • w)) - g c - t * ((fderiv ℝ g c) (k • w))
        + (t^2/2) * κ := by
      simp only [L, hκ]; ring
    have ht2 : 0 < t^2 := pow_pos htpos 2
    have htb : t * ((fderiv ℝ g c) (k • w)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos htpos.le hb'
    nlinarith [hbnd', hLt, hκpos, ht2, htb]

/-- **Second-order Taylor step, no sign hypothesis.**  Let `g : E → ℝ` be `C²` on the ball
`ball c ρ` (`ρ > 0`) and suppose `(D²g c) v v < 0` for some direction `v`.  Then the ball contains
a point at which `g` is strictly below `g c`.

If the first derivative of `g` at `c` in the direction `v` is non-positive this is
`exists_lt_ball_of_negSecondDeriv_nonpos_grad`; otherwise the same statement applied to the
direction `-v` (which leaves the second derivative unchanged and flips the first derivative)
applies. -/
theorem exists_lt_ball_of_negSecondDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {c : E} {ρ : ℝ} (hρ : 0 < ρ) (hg : ContDiffOn ℝ 2 g (Metric.ball c ρ))
    {v : E} (hv : (fderiv ℝ (fderiv ℝ g) c) v v < 0) :
    ∃ x : E, dist x c < ρ ∧ g x < g c := by
  by_cases hb : (fderiv ℝ g c) v ≤ 0
  · exact exists_lt_ball_of_negSecondDeriv_nonpos_grad hρ hg hv hb
  · simp only [not_le] at hb
    refine exists_lt_ball_of_negSecondDeriv_nonpos_grad hρ hg (w := -v) ?_ ?_
    · simpa using hv
    · rw [map_neg, neg_nonpos]; exact le_of_lt hb

theorem exists_sublevel_near_of_negDefPlane_local {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → ℝ} {u : E} (hf : ContDiffAt ℝ 2 f u)
    (hbad : ∃ v w : E, ∀ c d : ℝ, (c, d) ≠ 0 →
      (fderiv ℝ (fderiv ℝ f) u) (c • v + d • w) (c • v + d • w) < 0) :
    ∀ ρ > 0, ∃ x : E, dist x u < ρ ∧ f x < f u := by
  intro ρ hρ
  obtain ⟨v, w, hvw⟩ := hbad
  -- `v` is a direction of strictly negative second derivative
  have hv : (fderiv ℝ (fderiv ℝ f) u) v v < 0 := by
    have h := hvw 1 0 (by norm_num)
    simpa using h
  by_cases hcrit : fderiv ℝ f u = 0
  · -- `u` is critical: the second derivative decides, with the direction `v`
    obtain ⟨U, hU, hCU⟩ := hf.contDiffOn (m := 2) le_rfl (by intro h; exact absurd h (by norm_num))
    obtain ⟨ρ₀, hρ₀, hρ₀U⟩ := Metric.mem_nhds_iff.mp hU
    have hρmin : 0 < min ρ₀ ρ := lt_min hρ₀ hρ
    have hgmin : ContDiffOn ℝ 2 f (Metric.ball u (min ρ₀ ρ)) :=
      hCU.mono ((Metric.ball_subset_ball (min_le_left _ _)).trans hρ₀U)
    obtain ⟨x, hx, hxlt⟩ := exists_lt_ball_of_negSecondDeriv hρmin hgmin hv
    exact ⟨x, lt_of_lt_of_le hx (min_le_right _ _), hxlt⟩
  · -- `u` is not critical: choose a direction of negative first derivative
    obtain ⟨h, hh⟩ : ∃ h : E, (fderiv ℝ f u) h < 0 := by
      by_contra hcon
      simp only [not_exists, not_lt] at hcon
      refine hcrit (ContinuousLinearMap.ext fun x => le_antisymm ?_ (hcon x))
      exact neg_nonneg.mp (by simpa using hcon (-x))
    -- rescale `h` so that it has norm `≤ 1`
    set h₀ : E := (‖h‖ + 1)⁻¹ • h with hh₀
    have hh₀_le : ‖h₀‖ ≤ 1 := by
      rw [hh₀, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [← div_eq_inv_mul, div_le_one (by positivity)]
      linarith [norm_nonneg h]
    have hb₀ : (fderiv ℝ f u) h₀ < 0 := by
      rw [hh₀, map_smul, smul_eq_mul]
      exact mul_neg_of_pos_of_neg (by positivity) hh
    -- first-order Taylor expansion at `u`
    have hfd : HasFDerivAt f (fderiv ℝ f u) u := (hf.differentiableAt (by norm_num)).hasFDerivAt
    have hlittle := hfd.isLittleO
    rw [Asymptotics.isLittleO_iff] at hlittle
    set ε : ℝ := -((fderiv ℝ f u) h₀) / 2 with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; linarith
    have hev : ∀ᶠ y in 𝓝 u, ‖f y - f u - (fderiv ℝ f u) (y - u)‖ ≤ ε * ‖y - u‖ := hlittle hεpos
    obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hev
    set t : ℝ := min (δ/2) (ρ/2) with ht
    have htpos : 0 < t := by rw [ht]; exact lt_min (by linarith) (by linarith)
    have htδ : t < δ := by
      rw [ht]
      have hle : min (δ / 2) (ρ / 2) ≤ δ / 2 := min_le_left _ _
      linarith
    have htρ : t < ρ := by
      rw [ht]
      have hle : min (δ / 2) (ρ / 2) ≤ ρ / 2 := min_le_right _ _
      linarith
    refine ⟨u + t • h₀, ?_, ?_⟩
    · rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      calc t * ‖h₀‖ ≤ t * 1 := mul_le_mul_of_nonneg_left hh₀_le htpos.le
        _ = t := mul_one t
        _ < ρ := htρ
    · have hmem : dist (u + t • h₀) u < δ := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
        calc t * ‖h₀‖ ≤ t * 1 := mul_le_mul_of_nonneg_left hh₀_le htpos.le
          _ = t := mul_one t
          _ < δ := htδ
      have hbnd : ‖f (u + t • h₀) - f u - (fderiv ℝ f u) (t • h₀)‖ ≤ ε * ‖t • h₀‖ := by
        simpa [add_sub_cancel_left] using hδ hmem
      have hstep : |f (u + t • h₀) - f u - t * ((fderiv ℝ f u) h₀)| ≤ ε * t := by
        have h1 : |f (u + t • h₀) - f u - t * ((fderiv ℝ f u) h₀)| ≤ ε * (t * ‖h₀‖) := by
          simpa [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, abs_of_pos htpos] using hbnd
        have h3 : t * ‖h₀‖ ≤ t * 1 := mul_le_mul_of_nonneg_left hh₀_le htpos.le
        have h4 : ε * (t * ‖h₀‖) ≤ ε * t := by nlinarith [hεpos.le, h3]
        linarith [h1, h4]
      have hXle : f (u + t • h₀) - f u - t * ((fderiv ℝ f u) h₀) ≤ ε * t := (abs_le.mp hstep).2
      have hε2 : ε * 2 = -((fderiv ℝ f u) h₀) := by rw [hεdef]; ring
      nlinarith [hXle, hε2, hεpos, htpos]

end Work.OddBound.mountainPass3

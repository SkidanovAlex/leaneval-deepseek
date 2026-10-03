import Mathlib

namespace Work.L62

/-- **From a second-order remainder bound to a bound on the variation of the derivative.**

If `f` is holomorphic on `closedBall c R` and its second-order Taylor remainder is bounded by
`K ‖u-c‖²` on the disc of radius `R/2`, then the derivative satisfies
`‖deriv f u - deriv f c‖ ≤ 8K ‖u-c‖` on the disc of radius `R/4` (a *centered* bound, not a
pairwise Lipschitz bound).

Route: put `ψ z = f z - f c - f'(c)(z-c)`; then `ψ` is holomorphic and `deriv ψ u = deriv f u -
deriv f c`.  For `u ≠ c` apply Cauchy's estimate for the first derivative at the centre of the
disc of radius `‖u-c‖/2` around `u`
(`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`, Mathlib/Analysis/Complex/Liouville.lean):
that disc lies in `closedBall c R` and on its boundary `‖z - c‖ ≤ 3‖u-c‖/2 ≤ 3R/8 < R/2`, so
`‖ψ z‖ ≤ K(3‖u-c‖/2)²`; dividing by the radius gives
`‖deriv f u - deriv f c‖ ≤ (9/2) K ‖u-c‖ ≤ 8K‖u-c‖`.  For `u = c` both sides vanish. -/
theorem deriv_lipschitz_of_second_order {f : ℂ → ℂ} {c : ℂ} {R K : ℝ} (hR : 0 < R) (hK : 0 ≤ K)
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R))
    (h2 : ∀ u : ℂ, ‖u - c‖ ≤ R / 2 → ‖f u - f c - deriv f c * (u - c)‖ ≤ K * ‖u - c‖ ^ 2) :
    ∀ u : ℂ, ‖u - c‖ ≤ R / 4 → ‖deriv f u - deriv f c‖ ≤ (8 * K) * ‖u - c‖ := by
  intro u hu
  rcases eq_or_ne u c with rfl | hne
  · simp
  · -- abbreviations: `w = ‖u - c‖ > 0`, `r = w / 2` the radius of the Cauchy disc around `u`
    set w : ℝ := ‖u - c‖ with hwdef
    have hwpos : 0 < w := by
      rw [hwdef]; exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have hwle : w ≤ R / 4 := by rw [hwdef]; exact hu
    set r : ℝ := w / 2 with hrdef
    have hrpos : 0 < r := by rw [hrdef]; linarith
    have hlt : r + dist u c < R := by
      rw [hrdef, hwdef, dist_eq_norm]; linarith
    -- the auxiliary function `ψ`
    set ψ : ℂ → ℂ := f - fun z : ℂ => f c + deriv f c * (z - c) with hψdef
    have hψ_big : DifferentiableOn ℂ ψ (Metric.ball c R) := by
      rw [hψdef]
      have h1 : DifferentiableOn ℂ f (Metric.ball c R) := hf.mono Metric.ball_subset_closedBall
      have hlin : DifferentiableOn ℂ (fun z : ℂ => deriv f c * (z - c)) (Metric.ball c R) :=
        (differentiableOn_id.sub (differentiableOn_const c)).const_mul (deriv f c)
      exact h1.sub ((differentiableOn_const (f c)).add hlin)
    have hdc : DiffContOnCl ℂ ψ (Metric.ball u r) :=
      hψ_big.diffContOnCl_ball (Metric.closedBall_subset_ball' hlt)
    -- the Cauchy bound on the boundary circle of the disc of radius `r` about `u`
    have hsphere : ∀ z ∈ Metric.sphere u r, ‖ψ z‖ ≤ K * (3 * w / 2) ^ 2 := by
      intro z hz
      have hzr : ‖z - u‖ = r := by simpa [dist_eq_norm] using hz
      have hzc : ‖z - c‖ ≤ 3 * w / 2 := by
        calc ‖z - c‖ = ‖(z - u) + (u - c)‖ := by ring_nf
          _ ≤ ‖z - u‖ + ‖u - c‖ := norm_add_le _ _
          _ = r + w := by rw [hzr, hwdef]
          _ = 3 * w / 2 := by rw [hrdef]; ring
      have hzcR : ‖z - c‖ ≤ R / 2 := by
        have : 3 * w / 2 ≤ R / 2 := by linarith
        linarith
      have h2z := h2 z hzcR
      have hKz : K * ‖z - c‖ ^ 2 ≤ K * (3 * w / 2) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hzc 2) hK
      calc ‖ψ z‖ = ‖f z - f c - deriv f c * (z - c)‖ := by
              simp only [hψdef, Pi.sub_apply, sub_sub]
        _ ≤ K * ‖z - c‖ ^ 2 := h2z
        _ ≤ K * (3 * w / 2) ^ 2 := hKz
    have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hrpos hdc hsphere
    -- `f` is differentiable at `u` (which lies in the open disc of radius `R` about `c`)
    have hmem : u ∈ Metric.ball c R := by
      rw [Metric.mem_ball, dist_eq_norm]
      rw [hwdef] at hwle; linarith
    have hdfu : DifferentiableAt ℂ f u :=
      hf.differentiableAt (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hmem)
        Metric.ball_subset_closedBall)
    have hg_at : DifferentiableAt ℂ (fun z : ℂ => f c + deriv f c * (z - c)) u := by fun_prop
    have hderiv : deriv ψ u = deriv f u - deriv f c := by
      rw [hψdef, deriv_sub hdfu hg_at]
      congr 1
      have hg' : HasDerivAt (fun z : ℂ => f c + deriv f c * (z - c)) (deriv f c) u := by
        have h : HasDerivAt (fun z : ℂ => deriv f c * (z - c)) (deriv f c * 1) u :=
          ((hasDerivAt_id u).sub_const c).const_mul (deriv f c)
        simpa using h.const_add (f c)
      exact hg'.deriv
    have hkey : (K * (3 * w / 2) ^ 2) / r = (9 / 2 * K) * w := by
      rw [hrdef]
      field_simp
      ring
    have hfinal : ‖deriv f u - deriv f c‖ ≤ (8 * K) * w := by
      calc ‖deriv f u - deriv f c‖ = ‖deriv ψ u‖ := by rw [hderiv]
        _ ≤ (K * (3 * w / 2) ^ 2) / r := hcauchy
        _ = (9 / 2 * K) * w := hkey
        _ ≤ (8 * K) * w := by
            apply mul_le_mul_of_nonneg_right _ (le_of_lt hwpos)
            nlinarith [hK]
    simpa [hwdef] using hfinal

namespace Work.L62

/-- The same statement under the name `Work.L62.Work.L62.deriv_lipschitz_of_second_order`, which is
the name `Submission/Work/L62/local_ratio_contraction.lean` refers to (this file originally carried
a duplicated `namespace Work.L62`).  Kept as a one-line alias so that consumer keeps building. -/
theorem deriv_lipschitz_of_second_order {f : ℂ → ℂ} {c : ℂ} {R K : ℝ} (hR : 0 < R) (hK : 0 ≤ K)
    (hf : DifferentiableOn ℂ f (Metric.closedBall c R))
    (h2 : ∀ u : ℂ, ‖u - c‖ ≤ R / 2 → ‖f u - f c - deriv f c * (u - c)‖ ≤ K * ‖u - c‖ ^ 2) :
    ∀ u : ℂ, ‖u - c‖ ≤ R / 4 → ‖deriv f u - deriv f c‖ ≤ (8 * K) * ‖u - c‖ :=
  _root_.Work.L62.deriv_lipschitz_of_second_order hR hK hf h2

end Work.L62

end Work.L62

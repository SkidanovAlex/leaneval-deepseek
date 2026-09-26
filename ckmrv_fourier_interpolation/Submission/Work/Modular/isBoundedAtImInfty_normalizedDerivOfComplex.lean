import Mathlib

/-!
# The normalized derivative preserves boundedness at `i∞`

If `f : ℍ → ℂ` is holomorphic on the upper half plane and bounded at `i∞`, then so is its
normalized derivative `D f = (2πi)⁻¹ f'`.

The proof is Cauchy's estimate.  For `z : ℍ` with `im z` large we apply the Schwarz/Cauchy
estimate `Complex.norm_deriv_le_div_of_mapsTo_ball` on the disk of centre `z` and radius
`im z / 2`.  That disk is contained in the region where `im ≥ im z / 2 ≥ A`, on which `f` is
bounded by `M`; hence `f` maps the disk into a bounded ball and `‖D f z‖ ≤ 4‖(2πi)⁻¹‖·M`,
uniformly in `z` with large imaginary part.
-/

namespace Work.Modular

theorem isBoundedAtImInfty_normalizedDerivOfComplex {f : UpperHalfPlane → ℂ}
    (hhol : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {z | 0 < z.im})
    (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) :
    UpperHalfPlane.IsBoundedAtImInfty (Derivative.normalizedDerivOfComplex f) := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hbdd ⊢
  obtain ⟨M, A, hMA⟩ := hbdd
  refine ⟨‖(2 * Real.pi * Complex.I)⁻¹‖ * (4 * max M 0), max (2 * A) 1, ?_⟩
  intro z hz
  simp only [UpperHalfPlane.im] at hz
  set c : ℂ := (z : ℂ) with hc
  set R : ℝ := c.im / 2 with hR
  have h2A : (2 : ℝ) * A ≤ c.im := le_trans (le_max_left _ _) hz
  have hz1 : (1 : ℝ) ≤ c.im := le_trans (le_max_right _ _) hz
  have hzA2 : A ≤ c.im / 2 := by linarith
  have hcim : c.im = z.im := by rw [hc, UpperHalfPlane.coe_im]
  have hzA : A ≤ z.im := by
    have h1 : A ≤ c.im := by linarith [hzA2, hz1]
    rwa [← hcim]
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hRpos : 0 < R := by rw [hR]; linarith
  have hRge : (1 : ℝ) / 2 ≤ R := by rw [hR]; linarith
  -- Points of the disk have imaginary part at least `im z / 2`.
  have him_bound : ∀ w : ℂ, dist w c < R → c.im / 2 ≤ w.im := by
    intro w hw
    rw [dist_eq_norm, norm_sub_rev] at hw
    have hle := Complex.abs_im_le_norm (c - w)
    rw [abs_le] at hle
    have hsub : (c - w).im = c.im - w.im := Complex.sub_im c w
    rw [hsub] at hle
    have hR' : R = c.im / 2 := hR
    linarith [hle.2, hw, hR']
  have hball : Metric.ball c R ⊆ {w : ℂ | 0 < w.im} := by
    intro w hw
    show 0 < w.im
    have h := him_bound w (Metric.mem_ball.mp hw)
    have hR' : R = c.im / 2 := hR
    linarith [h, hR', hRpos]
  have hdiff : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) (Metric.ball c R) :=
    hhol.mono hball
  have hcc : (f ∘ UpperHalfPlane.ofComplex) c = f z := by
    simp only [Function.comp_apply]
    rw [show UpperHalfPlane.ofComplex c = z by rw [hc, UpperHalfPlane.ofComplex_apply]]
  -- `f` maps the disk into a bounded ball.
  have hmaps : Set.MapsTo (f ∘ UpperHalfPlane.ofComplex) (Metric.ball c R)
      (Metric.closedBall ((f ∘ UpperHalfPlane.ofComplex) c) (2 * max M 0)) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hwpos : 0 < w.im := hball hw
    have hwA : A ≤ w.im := by
      have h := him_bound w (Metric.mem_ball.mp hw)
      linarith [h, hzA2]
    have h1 : ‖(f ∘ UpperHalfPlane.ofComplex) w‖ ≤ max M 0 := by
      rw [UpperHalfPlane.comp_ofComplex_of_im_pos f w hwpos]
      exact (hMA ⟨w, hwpos⟩ hwA).trans (le_max_left _ _)
    have h2 : ‖(f ∘ UpperHalfPlane.ofComplex) c‖ ≤ max M 0 := by
      rw [hcc]
      exact (hMA z hzA).trans (le_max_left _ _)
    calc ‖(f ∘ UpperHalfPlane.ofComplex) w - (f ∘ UpperHalfPlane.ofComplex) c‖
        ≤ ‖(f ∘ UpperHalfPlane.ofComplex) w‖ + ‖(f ∘ UpperHalfPlane.ofComplex) c‖ :=
          norm_sub_le _ _
      _ ≤ max M 0 + max M 0 := add_le_add h1 h2
      _ = 2 * max M 0 := by ring
  have hcauchy : ‖deriv (f ∘ UpperHalfPlane.ofComplex) c‖ ≤ (2 * max M 0) / R :=
    Complex.norm_deriv_le_div_of_mapsTo_ball hdiff hmaps hRpos
  have hbound : (2 * max M 0) / R ≤ 4 * max M 0 := by
    rw [div_le_iff₀ hRpos]
    nlinarith [hM0, hRge]
  have hmain : ‖Derivative.normalizedDerivOfComplex f z‖
      = ‖(2 * Real.pi * Complex.I)⁻¹‖ * ‖deriv (f ∘ UpperHalfPlane.ofComplex) c‖ := by
    rw [Derivative.normalizedDerivOfComplex, ← hc, norm_mul]
  rw [hmain]
  exact mul_le_mul_of_nonneg_left (hcauchy.trans hbound) (norm_nonneg _)

end Work.Modular

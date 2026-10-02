import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.TripodCert

open Complex Metric Set

/-- If `f : ℂ → ℂ` is complex-differentiable on the closed ball `closedBall z₀ R` and the real
part of its derivative is positive there, then `f` is injective on that ball.

Proof: for `z ≠ w` in the ball put `d = w - z` and consider
`φ t = re ((f (z + t*d) - f z) * conj d)` on `[0,1]`.  Since `f z = f w`, we have
`φ 0 = φ 1 = 0`.  The chain rule gives
`φ' t = re (deriv f (z+t*d) * d * conj d) = re (deriv f (z+t*d)) * ‖d‖² > 0` for `t ∈ (0,1)`.
Rolle's theorem (`exists_hasDerivAt_eq_zero`) produces an interior zero of `φ'`, a
contradiction. -/
theorem injOn_closedBall_of_re_deriv_pos {z₀ : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (hd : ∀ z ∈ Metric.closedBall z₀ R, DifferentiableAt ℂ f z)
    (hpos : ∀ z ∈ Metric.closedBall z₀ R, 0 < (deriv f z).re) :
    Set.InjOn f (Metric.closedBall z₀ R) := by
  intro z hz w hw hzw
  by_contra hne
  set d : ℂ := w - z with hddef
  have hdne : d ≠ 0 := by
    rw [hddef, sub_ne_zero]
    exact fun h => hne h.symm
  -- the segment from `z` to `w` lies in the ball
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, z + (t : ℂ) * d ∈ Metric.closedBall z₀ R := by
    intro t ht
    have ht0 : 0 ≤ t := ht.1
    have hz' : ‖z - z₀‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    have hw' : ‖w - z₀‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsplit : z + (t : ℂ) * d - z₀
        = ((1 - t : ℝ) : ℂ) * (z - z₀) + (t : ℂ) * (w - z₀) := by
      rw [hddef]; push_cast; ring
    rw [hsplit]
    calc ‖((1 - t : ℝ) : ℂ) * (z - z₀) + (t : ℂ) * (w - z₀)‖
        ≤ ‖((1 - t : ℝ) : ℂ) * (z - z₀)‖ + ‖(t : ℂ) * (w - z₀)‖ := norm_add_le _ _
      _ = (1 - t) * ‖z - z₀‖ + t * ‖w - z₀‖ := by
            rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
              Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2]), abs_of_nonneg ht0]
      _ ≤ (1 - t) * R + t * R :=
            add_le_add (mul_le_mul_of_nonneg_left hz' (by linarith [ht.2]))
              (mul_le_mul_of_nonneg_left hw' ht0)
      _ = R := by ring
  -- continuity of the auxiliary function on `[0,1]`
  have hcont : ContinuousOn
      (fun t : ℝ => ((f (z + (t : ℂ) * d) - f z) * starRingEnd ℂ d).re) (Set.Icc (0 : ℝ) 1) := by
    have hfc : ContinuousOn f (Metric.closedBall z₀ R) :=
      fun x hx => (hd x hx).continuousAt.continuousWithinAt
    have hg : ContinuousOn (fun t : ℝ => z + (t : ℂ) * d) (Set.Icc (0 : ℝ) 1) :=
      (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
    have hcomp : ContinuousOn (fun t : ℝ => f (z + (t : ℂ) * d)) (Set.Icc (0 : ℝ) 1) :=
      ContinuousOn.comp' hfc hg (fun t ht => hmem t ht)
    have h2 : ContinuousOn (fun t : ℝ => (f (z + (t : ℂ) * d) - f z) * starRingEnd ℂ d)
        (Set.Icc (0 : ℝ) 1) :=
      (hcomp.sub continuousOn_const).mul continuousOn_const
    have h3 : ContinuousOn (fun t : ℝ => ((f (z + (t : ℂ) * d) - f z) * starRingEnd ℂ d).re)
        (Set.Icc (0 : ℝ) 1) := Complex.continuous_re.comp_continuousOn h2
    simpa only [Function.comp_def] using h3
  -- the derivative of the auxiliary function
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => ((f (z + (s : ℂ) * d) - f z) * starRingEnd ℂ d).re)
        (((deriv f (z + (t : ℂ) * d) * d) * starRingEnd ℂ d).re) t := by
    intro t ht
    have hwt : z + (t : ℂ) * d ∈ Metric.closedBall z₀ R := hmem t (Set.Ioo_subset_Icc_self ht)
    have hg : HasDerivAt (fun s : ℝ => z + (s : ℂ) * d) d t := by
      have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := by
        simpa using (hasDerivAt_id t).ofReal_comp
      have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * d) (1 * d) t := h1.mul_const d
      have h3 : HasDerivAt (fun s : ℝ => z + (s : ℂ) * d) (1 * d) t := h2.const_add z
      simpa using h3
    have hf' : HasDerivAt f (deriv f (z + (t : ℂ) * d)) (z + (t : ℂ) * d) :=
      (hd _ hwt).hasDerivAt
    have hcomp : HasDerivAt (fun s : ℝ => f (z + (s : ℂ) * d))
        (deriv f (z + (t : ℂ) * d) * d) t := HasDerivAt.comp t hf' hg
    have h1 : HasDerivAt (fun s : ℝ => f (z + (s : ℂ) * d) - f z)
        (deriv f (z + (t : ℂ) * d) * d) t := hcomp.sub_const (f z)
    have h2 : HasDerivAt (fun s : ℝ => (f (z + (s : ℂ) * d) - f z) * starRingEnd ℂ d)
        ((deriv f (z + (t : ℂ) * d) * d) * starRingEnd ℂ d) t := h1.mul_const _
    have h3 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h2
    simpa [Function.comp_def] using h3
  -- the auxiliary function takes the same value at `0` and at `1`
  have hφ0 : (fun s : ℝ => ((f (z + (s : ℂ) * d) - f z) * starRingEnd ℂ d).re) 0
      = (fun s : ℝ => ((f (z + (s : ℂ) * d) - f z) * starRingEnd ℂ d).re) 1 := by
    have h1 : z + d = w := by rw [hddef]; ring
    simp [h1, hzw]
  -- Rolle
  obtain ⟨c, hc, hc0⟩ :=
    exists_hasDerivAt_eq_zero (f := fun s : ℝ =>
        ((f (z + (s : ℂ) * d) - f z) * starRingEnd ℂ d).re)
      (f' := fun t : ℝ => (((deriv f (z + (t : ℂ) * d) * d) * starRingEnd ℂ d).re))
      (a := 0) (b := 1) one_pos hcont hφ0 hderiv
  have hval : 0 < (((deriv f (z + (c : ℂ) * d) * d) * starRingEnd ℂ d).re) := by
    have hcball : z + (c : ℂ) * d ∈ Metric.closedBall z₀ R :=
      hmem c (Set.Ioo_subset_Icc_self hc)
    have hre : 0 < (deriv f (z + (c : ℂ) * d)).re := hpos _ hcball
    have hdpos : 0 < ‖d‖ ^ 2 := by
      have hdpos' : 0 < ‖d‖ := norm_pos_iff.mpr hdne
      positivity
    have heq : ((deriv f (z + (c : ℂ) * d) * d) * starRingEnd ℂ d).re
        = (deriv f (z + (c : ℂ) * d)).re * ‖d‖ ^ 2 := by
      rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
    rw [heq]
    exact mul_pos hre hdpos
  rw [hc0] at hval
  exact (lt_irrefl 0) hval

end Work.TripodCert

import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Filter Metric

/-- If `τ` is complex-analytic on the ball of radius `δ` around the real point `x`, and `τ` equals
its complex conjugate (`star`) at real points `t` arbitrarily close to `x`, then `τ` equals `star`
at every real point in a neighbourhood of `x`.

Equivalently: if the imaginary part of `τ` vanishes *frequently* near `x`, then it vanishes on a
neighbourhood of `x`.  This is the identity theorem applied to the real-analytic function
`t ↦ (τ ↑t).im`: a zero of a non-zero analytic function is isolated, so a frequently vanishing
analytic function is locally identically zero. -/
theorem eqOn_real_of_frequently_real {τ : ℂ → ℂ} {x : ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hτ : AnalyticOnNhd ℂ τ (Metric.ball (x : ℂ) δ))
    (h : Filter.Frequently (fun t : ℝ => τ (t : ℂ) = star (τ (t : ℂ))) (nhdsWithin x {x}ᶜ)) :
    ∃ ε > 0, ∀ t : ℝ, |t - x| < ε → τ (t : ℂ) = star (τ (t : ℂ)) := by
  refine ⟨δ, hδ, fun t ht => ?_⟩
  -- `t ↦ (τ ↑t).im` is real-analytic on the real ball of radius `δ` around `x`.
  have hf : AnalyticOnNhd ℝ (fun t : ℝ => Complex.imCLM (τ (t : ℂ))) (Metric.ball x δ) := by
    intro t ht
    -- the real point `t` inside the real ball maps into the complex ball, by isometry of `↑·`.
    have hmem : (t : ℂ) ∈ Metric.ball (x : ℂ) δ := by
      rw [Metric.mem_ball, Complex.isometry_ofReal.dist_eq]
      exact Metric.mem_ball.mp ht
    have h1 : AnalyticAt ℝ τ (t : ℂ) := (hτ (t : ℂ) hmem).restrictScalars
    have h2 : AnalyticAt ℝ (fun s : ℝ => τ (s : ℂ)) t :=
      h1.comp (Complex.ofRealCLM.analyticAt t)
    exact AnalyticAt.comp (g := ⇑Complex.imCLM) (f := fun s : ℝ => τ (s : ℂ))
      (Complex.imCLM.analyticAt _) h2
  -- the imaginary part vanishes frequently near `x`.
  have hfreq : ∃ᶠ z in nhdsWithin x {x}ᶜ,
      (fun t : ℝ => Complex.imCLM (τ (t : ℂ))) z = 0 := by
    refine h.mono (fun z hz => ?_)
    exact (Complex.conj_eq_iff_im).1 (by rw [eq_comm]; exact hz)
  -- identity theorem on the (preconnected) ball.
  have hzero := hf.eqOn_zero_of_preconnected_of_frequently_eq_zero
    Metric.isPreconnected_ball (Metric.mem_ball_self hδ) hfreq
  have htball : t ∈ Metric.ball x δ := by
    rw [Metric.mem_ball, Real.dist_eq]; exact ht
  have hz0 : Complex.imCLM (τ (t : ℂ)) = 0 := hzero htball
  exact ((Complex.conj_eq_iff_im (z := τ (t : ℂ))).2 hz0).symm

end Work.ELRig

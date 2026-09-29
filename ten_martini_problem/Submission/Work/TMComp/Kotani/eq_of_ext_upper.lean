import Mathlib
import Submission.Work.TMComp.Kotani.GlueDefs

namespace Work.TMComp.Kotani

/-- Two analytic functions which agree with the same `m`-function `mfun α lam · x` on the
upper half of two balls `B(c,r)`, `B(c',r')` (with `c, c'` real) agree at every real point
lying in both balls.  This is the two-centred form of the identity principle used when the
local continuations of `mfun` are built around different real centres. -/
theorem eq_of_ext_upper {α lam : ℝ} {c r c' r' : ℝ} {f g : ℂ → ℂ} {x : ℝ}
    (hr : 0 < r) (hr' : 0 < r')
    (hf : AnalyticOnNhd ℂ f (Metric.ball (c : ℂ) r))
    (hg : AnalyticOnNhd ℂ g (Metric.ball (c' : ℂ) r'))
    (hfu : ∀ z ∈ Metric.ball (c : ℂ) r, 0 < z.im → f z = Work.TMComp.Kotani.mfun α lam z x)
    (hgu : ∀ z ∈ Metric.ball (c' : ℂ) r', 0 < z.im → g z = Work.TMComp.Kotani.mfun α lam z x)
    {w : ℂ} (hw : w ∈ Metric.ball (c : ℂ) r) (hw' : w ∈ Metric.ball (c' : ℂ) r')
    (hwr : w.im = 0) :
    f w = g w := by
  set U : Set ℂ := Metric.ball (c : ℂ) r ∩ Metric.ball (c' : ℂ) r' with hU
  have hfU : AnalyticOnNhd ℂ f U := hf.mono (fun z hz => hz.1)
  have hgU : AnalyticOnNhd ℂ g U := hg.mono (fun z hz => hz.2)
  have hUconv : Convex ℝ U := (convex_ball (c : ℂ) r).inter (convex_ball (c' : ℂ) r')
  have hwU : w ∈ U := ⟨hw, hw'⟩
  have hdw : dist w (c : ℂ) < r := Metric.mem_ball.mp hw
  have hdw' : dist w (c' : ℂ) < r' := Metric.mem_ball.mp hw'
  -- the radius of a ball around `w` contained in `U`
  set s : ℝ := min (r - dist w (c : ℂ)) (r' - dist w (c' : ℂ)) with hs
  have hs_pos : 0 < s := by
    rw [hs]; exact lt_min (by linarith) (by linarith)
  have hs_le : s ≤ r - dist w (c : ℂ) := by rw [hs]; exact min_le_left _ _
  have hs_le' : s ≤ r' - dist w (c' : ℂ) := by rw [hs]; exact min_le_right _ _
  have hcl : w ∈ closure ({z | f z = g z} \ {w}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    -- a point `b` of `U` with positive imaginary part, arbitrarily close to `w`
    set t : ℝ := min s ε / 2 with ht
    have ht_pos : 0 < t := by
      rw [ht]; exact div_pos (lt_min hs_pos hε) (by norm_num)
    have ht_lt_s : t < s := by
      rw [ht]; linarith [min_le_left s ε, lt_min hs_pos hε]
    have ht_lt_ε : t < ε := by
      rw [ht]; linarith [min_le_right s ε, lt_min hs_pos hε]
    set b : ℂ := w + (t : ℂ) * Complex.I with hb
    have hdbw : dist w b = t := by
      rw [dist_eq_norm, show w - b = -((t : ℂ) * Complex.I) by rw [hb]; ring, norm_neg,
        norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht_pos]
    have hb_im : b.im = t := by rw [hb]; simp [Complex.add_im, Complex.mul_im, hwr]
    have hb_mem1 : b ∈ Metric.ball (c : ℂ) r := by
      rw [Metric.mem_ball]
      calc dist b (c : ℂ) ≤ dist b w + dist w (c : ℂ) := dist_triangle _ _ _
        _ = t + dist w (c : ℂ) := by rw [dist_comm, hdbw]
        _ < r := by linarith
    have hb_mem2 : b ∈ Metric.ball (c' : ℂ) r' := by
      rw [Metric.mem_ball]
      calc dist b (c' : ℂ) ≤ dist b w + dist w (c' : ℂ) := dist_triangle _ _ _
        _ = t + dist w (c' : ℂ) := by rw [dist_comm, hdbw]
        _ < r' := by linarith
    have hbim_pos : 0 < b.im := by rw [hb_im]; exact ht_pos
    have hb_eq : f b = g b := by
      rw [hfu b hb_mem1 hbim_pos, hgu b hb_mem2 hbim_pos]
    have hb_ne : b ≠ w := by
      intro h
      have := congrArg Complex.im h
      rw [hb_im, hwr] at this
      linarith
    exact ⟨b, ⟨hb_eq, hb_ne⟩, by rw [hdbw]; exact ht_lt_ε⟩
  have hEqOn := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure hfU hgU
    hUconv.isPreconnected hwU hcl
  exact hEqOn hwU

end Work.TMComp.Kotani

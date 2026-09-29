import Mathlib
import Submission.Work.C17.seventeen_defs

namespace Work.C17I

open Complex Filter
open scoped Topology

/-- Guidance from the requester (area C17, input for `Work.C17.relation_to_LC`).

# `D_y` preserves the logarithm structure, raising the pole order by one

For `s > 0` write `lens = ball (s:ℂ) δ ∩ ball 0 s` (the points in the ball with positive real part
after the shift by `s`).  Suppose `A`, `G` are holomorphic on `ball (s:ℂ) δ`, `F` is holomorphic on
the lens, and on the lens `F` agrees with `A · log (s - ·) + G / (· - s)^m`.  Then `D_y F`, where
`D_y F (z) = F' z · (z-1)²/(z²-2z)` is `Work.C17.Dy`, agrees on the lens with
`(D_y A) · log (s - ·) + G' / (· - s)^(m+1)` for some `G'` holomorphic on the *ball*.

The two hypotheses `z ≠ 0` and `z ≠ 2` for `z ∈ ball (s:ℂ) δ` are needed so that the factor
`(z-1)²/(z²-2z) = 1/(D_y z)` is holomorphic on the ball (without them the claim is false: the pole of
`D_y F` at `0` cannot be absorbed).  In the application `δ ≤ s/2` and `δ ≤ (1-s)/2`, so both hold.

Computation: on the lens `s - z` has positive real part, so `log (s - ·)` is holomorphic there with
derivative `1/(· - s)`.  Hence on the lens
`F' = A' log (s-·) + A/(·-s) + G'/(·-s)^m - m G/(·-s)^(m+1)`, and multiplying by
`(z-1)²/(z²-2z)` gives the claim with `G' := (A·(·-s)^m + G'(·-s) - m G) · (z-1)²/(z²-2z)`, which is
holomorphic on the ball by the two hypotheses.

Used downstream together with `Work.C17I.logcoeff_eq_zero` (proved): the log-coefficient of
`D_y^k F` is `D_y^k A` and the "non-log part" is a holomorphic function divided by `(·-s)^k`, which
is exactly the input shape of the extraction result.

Helper auxiliary results may be added above the claim; do not change the claim. -/
theorem dy_log_struct {s : ℝ} {δ : ℝ} (hδ : 0 < δ) (hs : 0 < s) {m : ℕ} {F A G : ℂ → ℂ}
    (hz0 : ∀ z ∈ Metric.ball (s : ℂ) δ, z ≠ 0)
    (hz2 : ∀ z ∈ Metric.ball (s : ℂ) δ, z ≠ 2)
    (hFd : DifferentiableOn ℂ F (Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) s))
    (hA : DifferentiableOn ℂ A (Metric.ball (s : ℂ) δ))
    (hG : DifferentiableOn ℂ G (Metric.ball (s : ℂ) δ))
    (h : ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) s,
      F z = A z * Complex.log (s - z) + G z / (z - s) ^ m) :
    ∃ G' : ℂ → ℂ, DifferentiableOn ℂ G' (Metric.ball (s : ℂ) δ) ∧
      ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) s,
        Work.C17.Dy F z = Work.C17.Dy A z * Complex.log (s - z) + G' z / (z - s) ^ (m + 1) := by
  classical
  -- The hypotheses `hδ`, `hs` (positivity of the radius and of the shift) and `hFd` (holomorphy of
  -- `F` on the lens) are part of the interface but are not needed for the computation below: the
  -- value of `deriv F z` on the lens is determined by the *model function* through `F =ᶠ H`.
  have _ := hδ
  have _ := hs
  have _ := hFd
  -- On the lens, `s - z` has positive real part, hence `log (s - ·)` is holomorphic there with
  -- derivative `1/(· - s)`.  The whole content is therefore the computation
  -- `(A' log(s-·) + A/(·-s) + Gd/(·-s)^m - mG/(·-s)^(m+1)) · (z-1)²/(z²-2z)`
  -- ` = Dy A · log(s-·) + (A(·-s)^m + Gd(·-s) - mG) · (z-1)²/(z²-2z) / (·-s)^(m+1)`.
  have hUopen : IsOpen (Metric.ball (s : ℂ) δ) := Metric.isOpen_ball
  -- the factor `(z-1)²/(z²-2z) = 1/(D_y z)` is holomorphic on the ball, because `z ≠ 0, 2` there
  have hc : DifferentiableOn ℂ (fun z : ℂ => (z - 1) ^ 2 / (z ^ 2 - 2 * z))
      (Metric.ball (s : ℂ) δ) := by
    refine DifferentiableOn.div ((differentiableOn_id.sub (differentiableOn_const 1)).pow 2)
      ((differentiableOn_id.pow 2).sub ((differentiableOn_const 2).mul differentiableOn_id)) ?_
    intro z hz
    rw [show z ^ 2 - 2 * z = z * (z - 2) by ring]
    exact mul_ne_zero (hz0 z hz) (sub_ne_zero.mpr (hz2 z hz))
  refine ⟨fun z => ((z - 1) ^ 2 / (z ^ 2 - 2 * z)) *
      (A z * (z - s) ^ m + deriv G z * (z - s) - (m : ℂ) * G z), ?_, ?_⟩
  · -- the new `G'` is holomorphic on the ball
    refine hc.mul ?_
    refine ((hA.mul ((differentiableOn_id.sub (differentiableOn_const (s : ℂ))).pow m)).add
      (((hG.deriv hUopen).mul (differentiableOn_id.sub (differentiableOn_const (s : ℂ)))))).sub
      ((differentiableOn_const (m : ℂ)).mul hG)
  · intro z hz
    obtain ⟨hzU, hzB⟩ := hz
    -- the lens is contained in the ball, so `‖z‖ < s`
    have hzn : ‖z‖ < s := by
      have h1 := hzB
      rw [Metric.mem_ball, Complex.dist_eq, sub_zero] at h1
      exact h1
    have hre : 0 < (s - z).re := by
      have h3 : z.re ≤ ‖z‖ := Complex.re_le_norm z
      rw [Complex.sub_re, Complex.ofReal_re]
      linarith
    have hsr : s - z ≠ 0 := by
      intro h0
      have : (s - z).re = 0 := by rw [h0]; simp
      linarith
    have hDne : z - s ≠ 0 := by
      intro h0
      exact hsr (by rw [show s - z = -(z - s) by ring, h0]; simp)
    -- `F` agrees with the model function `H` near `z`, hence the derivatives agree
    have hLmem : Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) s ∈ 𝓝 z :=
      (Metric.isOpen_ball.inter Metric.isOpen_ball).mem_nhds ⟨hzU, hzB⟩
    have heq : F =ᶠ[𝓝 z] (fun w : ℂ => A w * Complex.log (s - w) + G w / (w - s) ^ m) :=
      Filter.eventually_of_mem hLmem h
    have hderivF : deriv F z
        = deriv (fun w : ℂ => A w * Complex.log (s - w) + G w / (w - s) ^ m) z :=
      heq.deriv_eq
    have hAat : HasDerivAt A (deriv A z) z :=
      (hA.differentiableAt (hUopen.mem_nhds hzU)).hasDerivAt
    have hGat : HasDerivAt G (deriv G z) z :=
      (hG.differentiableAt (hUopen.mem_nhds hzU)).hasDerivAt
    -- `(log (s - ·))' = 1/(· - s)` on the lens
    have hlog : HasDerivAt (fun w : ℂ => Complex.log (s - w)) (1 / (z - s)) z := by
      have hinner : HasDerivAt (fun w : ℂ => (s : ℂ) - w) (-1) z :=
        (hasDerivAt_id' z).const_sub (s : ℂ)
      have hsl : (s - z) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hre)
      have hh := (Complex.hasDerivAt_log hsl).comp z hinner
      have hval : (s - z)⁻¹ * (-1) = 1 / (z - s) := by
        rw [one_div, show z - s = -(s - z) by ring, inv_neg]
        ring
      rwa [hval] at hh
    have hLogp : HasDerivAt (fun w : ℂ => A w * Complex.log (s - w))
        (deriv A z * Complex.log (s - z) + A z * (1 / (z - s))) z :=
      hAat.mul hlog
    -- the polar part: `(G/(·-s)^m)' = Gd/(·-s)^m - mG/(·-s)^(m+1)`
    have hGp : HasDerivAt (fun w : ℂ => G w / (w - s) ^ m)
        (deriv G z / (z - s) ^ m - (m : ℂ) * G z / (z - s) ^ (m + 1)) z := by
      have hp : HasDerivAt (fun w : ℂ => (w - s) ^ (-(m : ℤ)))
          (((-(m : ℤ) : ℤ) : ℂ) * (z - s) ^ (-(m : ℤ) - 1)) z := by
        have hh := (hasDerivAt_zpow (-(m : ℤ)) (z - s) (Or.inl hDne)).comp z
          ((hasDerivAt_id' z).sub_const (s : ℂ))
        simpa only [Function.comp_def, mul_one] using hh
      have hmul := hGat.mul hp
      have hdval : deriv G z * (z - s) ^ (-(m : ℤ))
            + G z * (((-(m : ℤ) : ℤ) : ℂ) * (z - s) ^ (-(m : ℤ) - 1))
          = deriv G z / (z - s) ^ m - (m : ℂ) * G z / (z - s) ^ (m + 1) := by
        rw [zpow_neg, zpow_natCast,
          show (-(m : ℤ) - 1) = -((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg,
          zpow_natCast]
        push_cast
        ring
      have hfun : (G * fun w : ℂ => (w - s) ^ (-(m : ℤ))) = fun w : ℂ => G w / (w - s) ^ m := by
        funext w
        simp only [Pi.mul_apply]
        rw [zpow_neg, zpow_natCast]
        rfl
      rw [hfun] at hmul
      rw [hdval] at hmul
      exact hmul
    have hH : HasDerivAt (fun w : ℂ => A w * Complex.log (s - w) + G w / (w - s) ^ m)
        (deriv A z * Complex.log (s - z) + A z * (1 / (z - s))
          + (deriv G z / (z - s) ^ m - (m : ℂ) * G z / (z - s) ^ (m + 1))) z :=
      hLogp.add hGp
    -- the algebraic rearrangement, with `(z-s)^(m+1) = (z-s)^m·(z-s)`
    have hfinal : (deriv A z * Complex.log (s - z) + A z * (1 / (z - s))
          + (deriv G z / (z - s) ^ m - (m : ℂ) * G z / (z - s) ^ (m + 1)))
            * (z - 1) ^ 2 / (z ^ 2 - 2 * z)
        = deriv A z * (z - 1) ^ 2 / (z ^ 2 - 2 * z) * Complex.log (s - z)
          + ((z - 1) ^ 2 / (z ^ 2 - 2 * z))
              * (A z * (z - s) ^ m + deriv G z * (z - s) - (m : ℂ) * G z)
            / (z - s) ^ (m + 1) := by
      rw [pow_succ]
      field_simp
      ring
    rw [Work.C17.Dy, Work.C17.Dy, hderivF, hH.deriv]
    exact hfinal

end Work.C17I


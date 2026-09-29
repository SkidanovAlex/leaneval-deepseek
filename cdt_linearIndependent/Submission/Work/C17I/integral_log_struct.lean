import Mathlib
import Submission.Work.C17.seventeen_defs
import Submission.Work.C17g.segment_primitive

/-!
# Structure of an antiderivative of `g · (κ·y₁·log(s−·) + h)`

Let `D = ball (s:ℂ) δ ∩ ball 0 ρ` with `ρ < s` (so that on `D` the function `s - ·` takes
values in the open right half plane and `log (s - ·)` is holomorphic on `D`), and suppose

* `J` is holomorphic on `ball (s:ℂ) δ` with `J' = g·y₁` and `J s = 0`;
* `F` is holomorphic on `D` with `F' = g·(κ·y₁·log(s−·) + h)`.

Then `F` agrees on `D` with `κ·J·log(s−·) + G/(·−s)` for a function `G` holomorphic on the whole
ball `ball (s:ℂ) δ`.

The proof: the function `z ↦ F z - κ·J z·log(s-z)` has derivative `g·h - κ·J/(z-s)` on `D`;
since `J s = 0`, the function `z ↦ g z·h z - κ·dslope J s z` is holomorphic on the ball and
equals it there.  Its primitive `R` (Morera on a disc) therefore differs from `F - κ·J·log(s-·)`
by a constant `a` on `D` (a convex, hence preconnected, set).  The function
`G z = (z - s)·(R z + a)` is holomorphic on the ball and does the job.
-/

namespace Work.C17I

open Complex Metric

/-- `‖(s : ℂ)‖ = s` for `0 < s`. -/
lemma il_norm_coe {s : ℝ} (hs : 0 < s) : ‖(s : ℂ)‖ = s := by
  have h1 : ‖(s : ℂ)‖ ^ 2 = s ^ 2 := by rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  nlinarith [norm_nonneg (s : ℂ)]

/-- On the disc `ball 0 ρ`, the real part of `s - z` is positive when `ρ < s`. -/
lemma il_re_pos {s ρ : ℝ} (hρ : ρ < s) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) ρ) : 0 < (s - z).re := by
  have hzn : ‖z‖ < ρ := by rw [Metric.mem_ball, Complex.dist_eq, sub_zero] at hz; exact hz
  have hre : z.re ≤ ‖z‖ := Complex.re_le_norm z
  rw [Complex.sub_re, Complex.ofReal_re]
  linarith

/-- The point `s` is not in the disc `ball 0 ρ` when `ρ < s`. -/
lemma il_ne_s {s ρ : ℝ} (hs : 0 < s) (hρ : ρ < s) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) ρ) : z ≠ (s : ℂ) := by
  have hzn : ‖z‖ < ρ := by rw [Metric.mem_ball, Complex.dist_eq, sub_zero] at hz; exact hz
  intro h
  rw [h, il_norm_coe hs] at hzn
  linarith

/-- On the disc `ball 0 ρ` (with `ρ < s`), `log (s - ·)` is holomorphic with derivative
`1/(· - s)`. -/
lemma il_log_deriv {s ρ : ℝ} (hρ : ρ < s) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) ρ) :
    HasDerivAt (fun w : ℂ => Complex.log (s - w)) (1 / (z - s)) z := by
  have hre := il_re_pos hρ hz
  have hinner : HasDerivAt (fun w : ℂ => (s : ℂ) - w) (-1) z :=
    (hasDerivAt_id' z).const_sub (s : ℂ)
  have hsl : (s - z) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hre)
  have hh := (Complex.hasDerivAt_log hsl).comp z hinner
  have hval : (s - z)⁻¹ * (-1) = 1 / (z - s) := by
    rw [one_div, show z - s = -(s - z) by ring, inv_neg]
    ring
  rwa [hval] at hh

/-- The derivative identity behind the lemma: under the two ODE hypotheses, the function
`F - κ·J·log(s - ·)` has derivative `g·h - κ·J/(· - s)` on the lens. -/
lemma il_sub_log_deriv {s δ ρ : ℝ} (hρ : ρ < s)
    {g h y1 J F : ℂ → ℂ} {κ : ℂ}
    (hJ' : ∀ z ∈ Metric.ball (s : ℂ) δ, HasDerivAt J (g z * y1 z) z)
    (hF' : ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
        HasDerivAt F (g z * (κ * y1 z * Complex.log (s - z) + h z)) z) :
    ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
      HasDerivAt (fun w => F w - κ * J w * Complex.log (s - w))
        (g z * h z - κ * J z * (1 / (z - s))) z := by
  intro z hz
  have hlog := il_log_deriv hρ hz.2
  have hJat : HasDerivAt J (g z * y1 z) z := hJ' z hz.1
  have hJk : HasDerivAt (fun w => κ * J w) (κ * (g z * y1 z)) z := hJat.const_mul κ
  have hmul := hJk.mul hlog
  have hF := hF' z hz
  have hsub := hF.sub hmul
  have hval : g z * (κ * y1 z * Complex.log (s - z) + h z)
      - (κ * (g z * y1 z) * Complex.log (s - z) + κ * J z * (1 / (z - s)))
      = g z * h z - κ * J z * (1 / (z - s)) := by ring
  rw [hval] at hsub
  exact hsub

/-- Away from `c`, the difference quotient `dslope J c` is `(J · - J c)/(· - c)`; when
`J c = 0` this is `J · · (1/(· - c))`. -/
lemma il_dslope {J : ℂ → ℂ} {c z : ℂ} (hz : z ≠ c) (hJc : J c = 0) :
    dslope J c z = J z * (1 / (z - c)) := by
  rw [dslope_of_ne J hz, slope_def_field, hJc, sub_zero, div_eq_mul_inv, one_div]

theorem integral_log_struct {s δ ρ : ℝ} (hδ : 0 < δ) (hs : 0 < s) (hρ : ρ < s)
    (hne : (Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ).Nonempty)
    {g h y1 J F : ℂ → ℂ} {κ : ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball (s : ℂ) δ))
    (hh : DifferentiableOn ℂ h (Metric.ball (s : ℂ) δ))
    (hy1 : DifferentiableOn ℂ y1 (Metric.ball (s : ℂ) δ))
    (hJ : DifferentiableOn ℂ J (Metric.ball (s : ℂ) δ))
    (hJ' : ∀ z ∈ Metric.ball (s : ℂ) δ, HasDerivAt J (g z * y1 z) z)
    (hJs : J (s : ℂ) = 0)
    (hF : DifferentiableOn ℂ F (Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ))
    (hF' : ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
        HasDerivAt F (g z * (κ * y1 z * Complex.log (s - z) + h z)) z) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (s : ℂ) δ) ∧
      ∀ z ∈ Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ,
        F z = κ * J z * Complex.log (s - z) + G z / (z - s) := by
  classical
  have _ := hne
  have _ := hy1
  have _ := hF
  -- The "logarithmic coefficient" function `g·h - κ·(J - J s)/(· - s)` is holomorphic on the ball.
  have hBdiff : DifferentiableOn ℂ (fun z => g z * h z - κ * dslope J (s : ℂ) z)
      (Metric.ball (s : ℂ) δ) := by
    refine (hg.mul hh).sub ((differentiableOn_const κ).mul ?_)
    exact (Complex.differentiableOn_dslope (Metric.ball_mem_nhds (s : ℂ) hδ)).mpr hJ
  -- Morera on a disc: it has a primitive `R` on the ball.
  obtain ⟨R, hR⟩ := hBdiff.isExactOn_ball
  -- On the lens, `F - κ·J·log(s - ·)` has the same derivative as `R`.
  have hderiv := il_sub_log_deriv hρ hJ' hF'
  have hAfd : DifferentiableOn ℂ (fun w => F w - κ * J w * Complex.log (s - w))
      (Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ) :=
    fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt
  have hRd : DifferentiableOn ℂ R (Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ) :=
    fun z hz => (hR z hz.1).differentiableAt.differentiableWithinAt
  have hDopen : IsOpen (Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ) :=
    Metric.isOpen_ball.inter Metric.isOpen_ball
  have hDpre : IsPreconnected (Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ) :=
    ((convex_ball (s : ℂ) δ).inter (convex_ball (0 : ℂ) ρ)).isPreconnected
  have hdereq : Set.EqOn (deriv (fun w => F w - κ * J w * Complex.log (s - w))) (deriv R)
      (Metric.ball (s : ℂ) δ ∩ Metric.ball (0 : ℂ) ρ) := by
    intro z hz
    rw [(hderiv z hz).deriv, (hR z hz.1).deriv]
    simp only []
    rw [il_dslope (il_ne_s hs hρ hz.2) hJs]
    ring
  -- Hence they differ by a constant on the (convex, hence preconnected) lens.
  obtain ⟨a, ha⟩ := IsOpen.exists_eq_add_of_deriv_eq hDopen hDpre hAfd hRd hdereq
  refine ⟨fun z => (z - (s : ℂ)) * (R z + a), ?_, ?_⟩
  · refine (differentiableOn_id.sub (differentiableOn_const (s : ℂ))).mul ?_
    refine DifferentiableOn.add ?_ (differentiableOn_const a)
    intro z hz
    exact (hR z hz).differentiableAt.differentiableWithinAt
  · intro z hz
    have hzs : z - (s : ℂ) ≠ 0 := sub_ne_zero.mpr (il_ne_s hs hρ hz.2)
    have h1 : F z - κ * J z * Complex.log (s - z) = R z + a := ha hz
    have h2 : F z = κ * J z * Complex.log (s - z) + (R z + a) := by
      have h3 := eq_add_of_sub_eq h1
      rwa [add_comm] at h3
    have hGdiv : (z - (s : ℂ)) * (R z + a) / (z - (s : ℂ)) = R z + a :=
      mul_div_cancel_left₀ (R z + a) hzs
    rw [hGdiv]
    exact h2

end Work.C17I

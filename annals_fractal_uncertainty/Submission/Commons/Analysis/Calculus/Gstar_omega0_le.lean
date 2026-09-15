import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace Commons.Analysis.Calculus

set_option autoImplicit false

/-! ## Helper lemmas for the Beurling--Malliavin growth functional of `ω₀`

We prove that the spherical maximal function of the auxiliary weight
`ω₀(x) = -χ(‖x‖)·‖x‖/(log(2+‖x‖))²` is controlled by `3·(1 + r/(log(2+r))²)`.
The key analytic input is the monotonicity of `s ↦ s/(log(2+s))²` on `[0,∞)`,
which in turn follows from the elementary inequality `2 - 4/u ≤ log u` for `u ≥ 2`. -/

/-- For `u ≥ 2` we have `2 - 4/u ≤ log u`.  This is the elementary inequality behind the
monotonicity of `s ↦ s/(log(2+s))²`.  It follows from the standard two-sided bound
`2(x-1)/(x+1) ≤ log x` (`Real.le_log_one_add_of_nonneg`) with `x = u - 1`. -/
lemma Gstar_log_ge_two_sub (u : ℝ) (hu : 2 ≤ u) : 2 - 4 / u ≤ Real.log u := by
  have hu1 : 0 ≤ u - 1 := by linarith
  have h1 : 2 * (u - 1) / ((u - 1) + 2) ≤ Real.log (1 + (u - 1)) :=
    Real.le_log_one_add_of_nonneg hu1
  have h1' : 2 * (u - 1) / (u + 1) ≤ Real.log u := by
    rw [show (1:ℝ) + (u - 1) = u by ring, show (u - 1) + 2 = u + 1 by ring] at h1
    exact h1
  have hu0 : 0 < u := by linarith
  have h2 : 2 - 4 / u ≤ 2 * (u - 1) / (u + 1) := by
    have h : 2 * (u - 1) / (u + 1) - (2 - 4 / u) = 4 / (u * (u + 1)) := by
      field_simp
      ring
    have hpos : 0 ≤ 4 / (u * (u + 1)) := by positivity
    linarith
  linarith

/-- Derivative of `s ↦ s/(log(2+s))²` at a positive point. -/
lemma Gstar_hasDerivAt_div_log_sq (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun s : ℝ => s / (Real.log (2 + s))^2)
      (((Real.log (2 + x))^2 - x * (2 * (Real.log (2 + x))^(2-1) * (1/(2+x)))) /
        ((Real.log (2 + x))^2)^2) x := by
  have hlog : HasDerivAt (fun s : ℝ => Real.log (2 + s)) (1/(2+x)) x := by
    have h1 : HasDerivAt (fun s : ℝ => (2 : ℝ) + s) 1 x := (hasDerivAt_id x).const_add 2
    have h2 := h1.log (by linarith : (2:ℝ) + x ≠ 0)
    simpa using h2
  have hd : HasDerivAt (fun s : ℝ => (Real.log (2 + s))^2)
      (2 * (Real.log (2 + x))^(2-1) * (1/(2+x))) x := hlog.pow 2
  have hne : (Real.log (2 + x))^2 ≠ 0 := by
    have : 0 < Real.log (2 + x) := Real.log_pos (by linarith)
    positivity
  have := (hasDerivAt_id x).fun_div hd hne
  simpa using this

/-- The map `s ↦ s/(log(2+s))²` is monotone increasing on `[0,∞)`. -/
lemma Gstar_monotoneOn_div_log_sq :
    MonotoneOn (fun s : ℝ => s / (Real.log (2+s))^2) (Set.Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
  · apply ContinuousOn.div continuousOn_id
    · apply ContinuousOn.pow
      apply ContinuousOn.log
      · exact continuousOn_const.add continuousOn_id
      · intro s hs
        have hs' : (0:ℝ) ≤ s := hs
        linarith
    · intro s hs
      have hs' : (0:ℝ) ≤ s := hs
      have : 1 < 2 + s := by linarith
      exact pow_ne_zero 2 (Real.log_pos this).ne'
  · intro x hx
    have hx' : (0:ℝ) < x := by simpa using hx
    exact (Gstar_hasDerivAt_div_log_sq x hx').differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : (0:ℝ) < x := by simpa using hx
    have hd := Gstar_hasDerivAt_div_log_sq x hx'
    rw [hd.deriv]
    have hL : 0 < Real.log (2 + x) := Real.log_pos (by linarith)
    have hkey : 0 ≤ Real.log (2 + x) - 2 * x / (2 + x) := by
      have h1 : 2 - 4 / (2 + x) ≤ Real.log (2 + x) := Gstar_log_ge_two_sub (2+x) (by linarith)
      have h2 : 2 * x / (2 + x) = 2 - 4 / (2 + x) := by
        field_simp
        ring
      linarith
    have hnum : 0 ≤ (Real.log (2 + x))^2 -
        x * (2 * (Real.log (2 + x))^(2-1) * (1/(2+x))) := by
      have heq : (Real.log (2 + x))^2 - x * (2 * (Real.log (2 + x))^(2-1) * (1/(2+x)))
          = Real.log (2 + x) * (Real.log (2 + x) - 2 * x / (2 + x)) := by
        ring
      rw [heq]
      exact mul_nonneg (le_of_lt hL) hkey
    apply div_nonneg hnum
    positivity

/-- A supremum of real numbers, each bounded above by a nonnegative `a`, is at most `a`.
This version handles an empty index type as well (where the supremum is `0`). -/
lemma Gstar_iSup_le_real {ι : Type*} (f : ι → ℝ) (a : ℝ) (h : ∀ i, f i ≤ a) (ha : 0 ≤ a) :
    (⨆ i, f i) ≤ a := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [iSup_of_empty', Real.sSup_empty]; exact ha
  · exact ciSup_le h

/-- The core integral bound for a single point `x` with `‖x‖ = r > 0`. -/
lemma Gstar_integral_bound {d : ℕ} (r : ℝ) (hr : 0 < r)
    (x : EuclideanSpace ℝ (Fin d)) (hx : ‖x‖ = r) :
    (∫ t in (1/2:ℝ)..2,
        |-(Real.smoothTransition (‖t • x‖ / 5 - 1) *
            (‖t • x‖ / (Real.log (2 + ‖t • x‖))^2))|)
      ≤ 3 * (1 + r / (Real.log (2 + r))^2) := by
  set c : ℝ := 2 * r / (Real.log (2 + 2*r))^2 with hc
  have hpoint : ∀ t ∈ Set.Icc (1/2:ℝ) 2,
      |-(Real.smoothTransition (‖t • x‖ / 5 - 1) *
          (‖t • x‖ / (Real.log (2 + ‖t • x‖))^2))| ≤ c := by
    intro t ht
    have ht1 : (0:ℝ) < t := by linarith [ht.1]
    have hnorm : ‖t • x‖ = t * r := by
      rw [norm_smul, hx, Real.norm_eq_abs, abs_of_nonneg (le_of_lt ht1)]
    rw [hnorm, abs_neg]
    have hb_nonneg : 0 ≤ t * r / (Real.log (2 + t*r))^2 :=
      div_nonneg (by positivity) (sq_nonneg _)
    have hchi : |Real.smoothTransition (t*r/5 - 1)| ≤ 1 := by
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
      exact Real.smoothTransition.le_one _
    have hstep1 : |Real.smoothTransition (t*r/5 - 1) * (t * r / (Real.log (2 + t*r))^2)| ≤
        1 * (t * r / (Real.log (2 + t*r))^2) := by
      rw [abs_mul, abs_of_nonneg hb_nonneg]
      exact mul_le_mul_of_nonneg_right hchi hb_nonneg
    have hstep2 : t * r / (Real.log (2 + t*r))^2 ≤ 2 * r / (Real.log (2 + 2*r))^2 := by
      have h1 : t*r ∈ Set.Ici (0:ℝ) := by simp; positivity
      have h2 : 2*r ∈ Set.Ici (0:ℝ) := by simp; positivity
      have h3 : t*r ≤ 2*r := by nlinarith [ht.2]
      have := Gstar_monotoneOn_div_log_sq h1 h2 h3
      simpa using this
    calc |Real.smoothTransition (t*r/5 - 1) * (t * r / (Real.log (2 + t*r))^2)|
        ≤ 1 * (t * r / (Real.log (2 + t*r))^2) := hstep1
      _ = t * r / (Real.log (2 + t*r))^2 := one_mul _
      _ ≤ 2 * r / (Real.log (2 + 2*r))^2 := hstep2
      _ = c := by rw [hc]
  have hcont : Continuous (fun t : ℝ =>
      |-(Real.smoothTransition (‖t • x‖ / 5 - 1) *
          (‖t • x‖ / (Real.log (2 + ‖t • x‖))^2))|) := by
    have hx_cont : Continuous (fun t : ℝ => t • x) := by fun_prop
    have hnorm_cont : Continuous (fun t : ℝ => ‖t • x‖) := hx_cont.norm
    have harg : Continuous (fun t : ℝ => ‖t • x‖ / 5 - 1) :=
      (hnorm_cont.div_const 5).sub continuous_const
    have hchi : Continuous (fun t : ℝ => Real.smoothTransition (‖t • x‖ / 5 - 1)) :=
      Real.smoothTransition.continuous.comp harg
    have hlog : Continuous (fun t : ℝ => Real.log (2 + ‖t • x‖)) := by
      apply Continuous.log
      · exact continuous_const.add hnorm_cont
      · intro t
        have : 0 ≤ ‖t • x‖ := norm_nonneg _
        linarith
    have hden : Continuous (fun t : ℝ => (Real.log (2 + ‖t • x‖))^2) := hlog.pow 2
    have hden0 : ∀ (t : ℝ), (Real.log (2 + ‖t • x‖))^2 ≠ 0 := by
      intro t
      have h1 : 1 < 2 + ‖t • x‖ := by have := norm_nonneg (t • x); linarith
      have h2 : 0 < Real.log (2 + ‖t • x‖) := Real.log_pos h1
      positivity
    have hquot : Continuous (fun t : ℝ => ‖t • x‖ / (Real.log (2 + ‖t • x‖))^2) :=
      hnorm_cont.div hden hden0
    have := (hchi.mul hquot).neg.abs
    simpa using this
  have hmono : (∫ t in (1/2:ℝ)..2,
      |-(Real.smoothTransition (‖t • x‖ / 5 - 1) *
          (‖t • x‖ / (Real.log (2 + ‖t • x‖))^2))|)
      ≤ ∫ t in (1/2:ℝ)..2, c :=
    intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable _ _)
      intervalIntegrable_const hpoint
  rw [intervalIntegral.integral_const] at hmono
  have hconst : (2 - 1/2 : ℝ) • c = 3 * r / (Real.log (2 + 2*r))^2 := by
    rw [hc, smul_eq_mul]; ring
  rw [hconst] at hmono
  have hL1pos : 0 < (Real.log (2 + r))^2 := by
    have : 0 < Real.log (2 + r) := Real.log_pos (by linarith)
    positivity
  have hden : (Real.log (2 + r))^2 ≤ (Real.log (2 + 2*r))^2 := by
    apply pow_le_pow_left₀ (Real.log_nonneg (by linarith))
    apply Real.log_le_log (by linarith)
    linarith
  have h1 : 3 * r / (Real.log (2 + 2*r))^2 ≤ 3 * r / (Real.log (2 + r))^2 :=
    div_le_div_of_nonneg_left (by positivity) hL1pos hden
  have h2 : 3 * r / (Real.log (2 + r))^2 ≤ 3 * (1 + r / (Real.log (2 + r))^2) := by
    have : 3 * (1 + r / (Real.log (2 + r))^2) = 3 + 3 * r / (Real.log (2 + r))^2 := by
      ring
    rw [this]; linarith
  linarith

/-- **The Beurling–Malliavin growth functional of the auxiliary weight.**  For
`ω₀(x) = -χ(‖x‖)·‖x‖/(log(2+‖x‖))²` (`χ(r) = smoothTransition (r/5 - 1)`), the spherical maximal
function `r ↦ sup_{‖x‖=r} ∫_{1/2}^2 |ω₀(t•x)| dt` is bounded by `K·(1 + r/(log(2+r))²)`. -/
theorem Gstar_omega0_le {d : ℕ} :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, 0 < r →
      (⨆ x : {x : EuclideanSpace ℝ (Fin d) // ‖x‖ = r},
        ∫ t in (1 / 2 : ℝ)..2,
          |-(Real.smoothTransition (‖t • (x : EuclideanSpace ℝ (Fin d))‖ / 5 - 1)
              * (‖t • (x : EuclideanSpace ℝ (Fin d))‖ /
                 (Real.log (2 + ‖t • (x : EuclideanSpace ℝ (Fin d))‖)) ^ 2))|)
        ≤ K * (1 + r / (Real.log (2 + r)) ^ 2) := by
  refine ⟨3, by norm_num, fun r hr => ?_⟩
  apply Gstar_iSup_le_real
  · intro x
    exact Gstar_integral_bound r hr (x : EuclideanSpace ℝ (Fin d)) x.2
  · have hL : 0 < Real.log (2 + r) := Real.log_pos (by linarith)
    have : 0 ≤ r / (Real.log (2 + r)) ^ 2 := div_nonneg (le_of_lt hr) (sq_nonneg _)
    nlinarith

end Commons.Analysis.Calculus
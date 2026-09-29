import Mathlib
import Submission.Work.A14D.chainZDefs

/-!
# The analytic cleared class identity for a solution `y9` of the Zagier operator `L_Z`

`L_Z y = (P y')' + R y` with `P = z(1−z)(1−9z)`, `R = 9z − 3` (`Work.A14D.LZ`).  The
`y`-derivative is `∂_y = (1/y') ∂_x` with `y = z²/(z−1)`, i.e. `∂_y f = ρ · f'` where
`ρ = (X−1)²/(X²−2X)`.  `Work.A14D.chainZDefs` supplies the *cleared* chain
`DZpoly k, AZpoly k, BZpoly k ∈ ℚ[X]` whose class in `ℚ(X)e₀ ⊕ ℚ(X)e₁` is the class of
`∂_y^k` (`Work.A14D.chainZ_rat`).  This file proves the analytic half: for any holomorphic
solution `y9` of `L_Z` on the disc `ball ninth δ` (`Work.A14D.Y9`), and every `z` in that
disc with `z ≠ ninth`,
  `DZpoly k (z) * (∂_y^k y9)(z) = AZpoly k (z) * y9 z + BZpoly k (z) * y9'(z)`.

The proof is the clearing recursion: differentiating the identity for `k` gives the identity
for the derivatives, and the ODE removes the second derivative; the algebra is `ana_step`.
-/

namespace Work.A14D

open Polynomial

open scoped Topology

noncomputable section

/-! ## Generic calculus helpers (independent of the operator) -/

/-- The polynomial function `w ↦ p(w)` (with `p` over `ℚ` read in `ℂ`) has derivative
`p'(z)` — the `eval₂` version of `Polynomial.hasDerivAt`. -/
lemma hasDerivAt_eval₂ (p : Polynomial ℚ) (z : ℂ) :
    HasDerivAt (fun w => p.eval₂ (algebraMap ℚ ℂ) w) ((p.derivative).eval₂ (algebraMap ℚ ℂ) z) z := by
  have h := Polynomial.hasDerivAt (p.map (algebraMap ℚ ℂ)) z
  rw [Polynomial.derivative_map, Polynomial.eval_map] at h
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with w
  exact Polynomial.eval₂_eq_eval_map (algebraMap ℚ ℂ) (x := w)

lemma deriv_eval₂ (p : Polynomial ℚ) (z : ℂ) :
    deriv (fun w => p.eval₂ (algebraMap ℚ ℂ) w) z = (p.derivative).eval₂ (algebraMap ℚ ℂ) z :=
  (hasDerivAt_eval₂ p z).deriv

lemma differentiableAt_eval₂ (p : Polynomial ℚ) (z : ℂ) :
    DifferentiableAt ℂ (fun w => p.eval₂ (algebraMap ℚ ℂ) w) z :=
  (hasDerivAt_eval₂ p z).differentiableAt

/-- The product rule for a polynomial function and an arbitrary differentiable function. -/
lemma deriv_mul_eval₂ (p : Polynomial ℚ) (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z) :
    deriv (fun w => p.eval₂ (algebraMap ℚ ℂ) w * f w) z
      = (p.derivative).eval₂ (algebraMap ℚ ℂ) z * f z + p.eval₂ (algebraMap ℚ ℂ) z * deriv f z := by
  rw [show (fun w => p.eval₂ (algebraMap ℚ ℂ) w * f w)
        = (fun w => p.eval₂ (algebraMap ℚ ℂ) w) * f from rfl,
    deriv_mul (differentiableAt_eval₂ p z) hf, deriv_eval₂]

/-- Additivity of `deriv` in the shape produced by `fun w => f w + g w`. -/
lemma deriv_add_fun (f g : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℂ f z)
    (hg : DifferentiableAt ℂ g z) :
    deriv (fun w => f w + g w) z = deriv f z + deriv g z := by
  rw [show (fun w => f w + g w) = f + g from rfl, deriv_add hf hg]

/-- Analyticity of `w ↦ (w-1)²`. -/
lemma analyticAt_sq_sub_one (z : ℂ) : AnalyticAt ℂ (fun w : ℂ => (w - 1) ^ 2) z := by
  have h : (fun w : ℂ => (w - 1) ^ 2) = (fun w : ℂ => w - 1) ^ 2 := rfl
  rw [h]
  exact ((analyticAt_id.sub analyticAt_const).pow 2)

/-- Analyticity of `w ↦ w² - 2w`. -/
lemma analyticAt_sq_sub_two (z : ℂ) : AnalyticAt ℂ (fun w : ℂ => w ^ 2 - 2 * w) z := by
  have h : (fun w : ℂ => w ^ 2 - 2 * w) = (fun w : ℂ => w ^ 2) - (fun w : ℂ => 2 * w) := rfl
  rw [h]
  exact ((analyticAt_id.pow 2).sub (analyticAt_const.mul analyticAt_id))

/-- Clearing identity for one step, in the form of a pure field computation. -/
lemma ana_step {D A B dD dA dB P2 P1 P0 F dF y dy ddy : ℂ}
    (h1 : D * F = A * y + B * dy)
    (h2 : dD * F + D * dF = dA * y + A * dy + dB * dy + B * ddy)
    (h3 : P2 * ddy + P1 * dy + P0 * y = 0) :
    D ^ 2 * P2 * dF = (D * P2 * dA - P2 * dD * A - D * B * P0) * y
      + (D * P2 * (A + dB) - D * B * P1 - P2 * dD * B) * dy := by
  linear_combination (D * P2) * h2 - (P2 * dD) * h1 + (D * B) * h3

/-! ## The theorem -/

theorem chainZ_ana {y9 : ℂ → ℂ} {δ : ℝ} (hY : Work.A14D.Y9 y9 δ) :
    ∀ k : ℕ, ∀ z : ℂ, z ∈ Metric.ball Work.A14D.ninth δ → z ≠ Work.A14D.ninth →
      (Work.A14D.DZpoly k).eval₂ (algebraMap ℚ ℂ) z * Work.A14D.DyIter k y9 z
        = (Work.A14D.AZpoly k).eval₂ (algebraMap ℚ ℂ) z * y9 z
          + (Work.A14D.BZpoly k).eval₂ (algebraMap ℚ ℂ) z * deriv y9 z := by
  obtain ⟨hδpos, hδle, hydiff, hyval, hode⟩ := hY
  have hBopen : IsOpen (Metric.ball ninth δ) := Metric.isOpen_ball
  have hAnal : AnalyticOn ℂ y9 (Metric.ball ninth δ) := hydiff.analyticOn hBopen
  have hy9diff : ∀ z ∈ Metric.ball ninth δ, DifferentiableAt ℂ y9 z :=
    fun z hz => (hAnal.analyticAt (hBopen.mem_nhds hz)).differentiableAt
  have hdy9diff : ∀ z ∈ Metric.ball ninth δ, DifferentiableAt ℂ (deriv y9) z :=
    fun z hz => (hAnal.analyticAt (hBopen.mem_nhds hz)).deriv.differentiableAt
  -- all iterates of `∂_y` applied to `y9` are analytic on the disc
  have hDi : ∀ k : ℕ, ∀ z ∈ Metric.ball ninth δ, AnalyticAt ℂ (DyIter k y9) z := by
    intro k
    induction k with
    | zero =>
        intro z hz
        simpa [DyIter] using hAnal.analyticAt (hBopen.mem_nhds hz)
    | succ k ih =>
        intro z hz
        have hzden : z ^ 2 - 2 * z ≠ 0 := sq_sub_two_ne_zero_of_mem_ball_ninth hδle hz
        rw [show DyIter (k + 1) y9
            = (fun w : ℂ => deriv (DyIter k y9) w * (w - 1) ^ 2) / (fun w : ℂ => w ^ 2 - 2 * w) from by
          funext w; simp [DyIter, Function.iterate_succ_apply', Dy]]
        exact (((ih z hz).deriv.mul (analyticAt_sq_sub_one z)).div
          (analyticAt_sq_sub_two z) hzden)
  have hGopen : IsOpen (Metric.ball ninth δ \ {ninth}) :=
    Metric.isOpen_ball.sdiff isClosed_singleton
  intro k
  induction k with
  | zero =>
      intro z hz hzn
      simp only [DZpoly_zero, AZpoly_zero, BZpoly_zero, Polynomial.eval₂_one,
        Polynomial.eval₂_zero, DyIter, Function.iterate_zero, id_eq, one_mul, zero_mul,
        add_zero]
  | succ k ih =>
      intro z hz hzn
      have hzB : z ∈ Metric.ball ninth δ := hz
      have hWne : z ^ 2 - 2 * z ≠ 0 := sq_sub_two_ne_zero_of_mem_ball_ninth hδle hz
      have hdy : DifferentiableAt ℂ (DyIter k y9) z := (hDi k z hz).differentiableAt
      have h1 : (DZpoly k).eval₂ (algebraMap ℚ ℂ) z * DyIter k y9 z
          = (AZpoly k).eval₂ (algebraMap ℚ ℂ) z * y9 z
            + (BZpoly k).eval₂ (algebraMap ℚ ℂ) z * deriv y9 z := ih z hz hzn
      have hder_eq : deriv (fun w => (DZpoly k).eval₂ (algebraMap ℚ ℂ) w * DyIter k y9 w) z
          = deriv (fun w => (AZpoly k).eval₂ (algebraMap ℚ ℂ) w * y9 w
              + (BZpoly k).eval₂ (algebraMap ℚ ℂ) w * deriv y9 w) z := by
        have hev : (fun w => (DZpoly k).eval₂ (algebraMap ℚ ℂ) w * DyIter k y9 w)
            =ᶠ[𝓝 z] (fun w => (AZpoly k).eval₂ (algebraMap ℚ ℂ) w * y9 w
              + (BZpoly k).eval₂ (algebraMap ℚ ℂ) w * deriv y9 w) := by
          filter_upwards [hGopen.mem_nhds (show z ∈ Metric.ball ninth δ \ {ninth} from
            ⟨hz, by simpa using hzn⟩)] with w hw
          exact ih w hw.1 (by simpa using hw.2)
        exact hev.deriv_eq
      have hL : deriv (fun w => (DZpoly k).eval₂ (algebraMap ℚ ℂ) w * DyIter k y9 w) z
          = (DZpoly k).derivative.eval₂ (algebraMap ℚ ℂ) z * DyIter k y9 z
            + (DZpoly k).eval₂ (algebraMap ℚ ℂ) z * deriv (DyIter k y9) z :=
        deriv_mul_eval₂ _ _ _ hdy
      have hR : deriv (fun w => (AZpoly k).eval₂ (algebraMap ℚ ℂ) w * y9 w
              + (BZpoly k).eval₂ (algebraMap ℚ ℂ) w * deriv y9 w) z
          = (AZpoly k).derivative.eval₂ (algebraMap ℚ ℂ) z * y9 z
            + (AZpoly k).eval₂ (algebraMap ℚ ℂ) z * deriv y9 z
            + (BZpoly k).derivative.eval₂ (algebraMap ℚ ℂ) z * deriv y9 z
            + (BZpoly k).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv y9) z := by
        have hfun : (fun w => (AZpoly k).eval₂ (algebraMap ℚ ℂ) w * y9 w
              + (BZpoly k).eval₂ (algebraMap ℚ ℂ) w * deriv y9 w)
            = (fun w => (AZpoly k).eval₂ (algebraMap ℚ ℂ) w * y9 w)
              + (fun w => (BZpoly k).eval₂ (algebraMap ℚ ℂ) w * deriv y9 w) := rfl
        rw [hfun,
            deriv_add (f := fun w => (AZpoly k).eval₂ (algebraMap ℚ ℂ) w * y9 w)
              (g := fun w => (BZpoly k).eval₂ (algebraMap ℚ ℂ) w * deriv y9 w)
              ((differentiableAt_eval₂ _ _).mul (hy9diff z hzB))
              ((differentiableAt_eval₂ _ _).mul (hdy9diff z hzB)),
            deriv_mul_eval₂ _ _ _ (hy9diff z hzB),
            deriv_mul_eval₂ _ _ _ (hdy9diff z hzB)]
        ring
      have h2 : (DZpoly k).derivative.eval₂ (algebraMap ℚ ℂ) z * DyIter k y9 z
            + (DZpoly k).eval₂ (algebraMap ℚ ℂ) z * deriv (DyIter k y9) z
          = (AZpoly k).derivative.eval₂ (algebraMap ℚ ℂ) z * y9 z
            + (AZpoly k).eval₂ (algebraMap ℚ ℂ) z * deriv y9 z
            + (BZpoly k).derivative.eval₂ (algebraMap ℚ ℂ) z * deriv y9 z
            + (BZpoly k).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv y9) z :=
        hL.symm.trans (hder_eq.trans hR)
      have h3 : (pZq).eval₂ (algebraMap ℚ ℂ) z * deriv (deriv y9) z
            + (pZq').eval₂ (algebraMap ℚ ℂ) z * deriv y9 z
            + (rZq).eval₂ (algebraMap ℚ ℂ) z * y9 z = 0 := by
        have h := hode z hzB
        rw [LZ] at h
        rw [← pZq_eval₂, ← pZq'_eval₂, ← rZq_eval₂] at h
        exact h
      have hstep := ana_step h1 h2 h3
      have hWmul : (z ^ 2 - 2 * z) * ((z - 1) ^ 2 / (z ^ 2 - 2 * z)) = (z - 1) ^ 2 :=
        mul_div_cancel₀ _ hWne
      rw [show DyIter (k + 1) y9 z
            = deriv (DyIter k y9) z * (z - 1) ^ 2 / (z ^ 2 - 2 * z) from by
          simp [DyIter, Function.iterate_succ_apply', Dy],
        DZpoly_eval₂_succ, AZpoly_eval₂_succ, BZpoly_eval₂_succ]
      linear_combination (z - 1) ^ 2 * hstep
        + ((DZpoly k).eval₂ (algebraMap ℚ ℂ) z ^ 2 * (pZq).eval₂ (algebraMap ℚ ℂ) z
            * deriv (DyIter k y9) z) * hWmul

end

end Work.A14D

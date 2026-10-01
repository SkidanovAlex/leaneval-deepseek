import Mathlib
import Submission.Work.NumberTheory.Linnik.scratch_reF

open MeasureTheory

/-!
# Condition 2 for the triangle test function (Heath-Brown §8)

Heath-Brown's §8 test function `f(t) = x₀ - t` for `0 ≤ t ≤ x₀` (`f = 0` for `t ≥ x₀`) — the
"triangle" — is the simplest admissible test function for the explicit formula of §6.  Both
*Condition 1* (`f ≥ 0`) and *Condition 2* (`Re ∫₀^{x₀} e^{-zt} f(t) dt ≥ 0` for `Re z ≥ 0`) are
elementary for it; the present file proves Condition 2, i.e. the `hFnn` hypothesis of
`Commons.NumberTheory.Linnik.lemma6_3_full` for the triangle.

The mathematical content is the real-variable inequality

`∫₀^X e^{-σt} cos(y t) (X - t) dt ≥ 0`   (`σ ≥ 0`, `X ≥ 0`),

which we obtain from a double integration by parts.  Put `ψ(t) = (1 - cos(y t))/y²` (`y ≠ 0`;
`y = 0` is trivial).  Then `ψ'' = cos(y·)`, `ψ(0) = ψ'(0) = 0`, `ψ ≥ 0`, while the weight
`w(t) = e^{-σt}(X - t)` satisfies `w(X) = 0`, `w'(X) = -e^{-σX} ≤ 0` and
`w''(t) = e^{-σt}(σ²(X-t) + 2σ) ≥ 0` on `[0,X]` (this is exactly where `σ ≥ 0` is used).  Since
`d/dt (w ψ' - w' ψ) = w ψ'' - w'' ψ`, the fundamental theorem of calculus gives

`∫₀^X w ψ'' = ∫₀^X w'' ψ + e^{-σX} ψ(X)`,

a sum of two non-negative terms.  (Equivalently: the exponential weight is a positive mixture of
triangular Fejér kernels `(T - t)⁺`, whose cosine transforms `(1 - cos(Ty))/y²` are non-negative.)

This converts `Re e^{-zt}` into `e^{-(Re z)t} cos((Im z)t)` and the triangle `(x₀-t)⁺` into `x₀ - t`
on `[0, x₀]`, which yields the complex statement.
-/

namespace Work.LinnikAreas

/-- **Integration by parts for a second derivative.**  If `w` and `ψ` are twice differentiable on
`[0,X]` (with the stated derivative functions) then

`∫₀^X w ψ'' = ∫₀^X w'' ψ + (w X ψ' X - w' X ψ X) - (w 0 ψ' 0 - w' 0 ψ 0)`.

This is the FTC applied to `g = w ψ' - w' ψ`, whose derivative is `w ψ'' - w'' ψ`; the boundary
terms at `0` may be dropped when `ψ(0) = ψ'(0) = 0`. -/
private theorem integral_mul_second_deriv_eq {X : ℝ} {w w' w'' ψ ψ' ψ'' : ℝ → ℝ}
    (hw : ∀ t ∈ Set.uIcc 0 X, HasDerivAt w (w' t) t)
    (hw' : ∀ t ∈ Set.uIcc 0 X, HasDerivAt w' (w'' t) t)
    (hψ : ∀ t ∈ Set.uIcc 0 X, HasDerivAt ψ (ψ' t) t)
    (hψ' : ∀ t ∈ Set.uIcc 0 X, HasDerivAt ψ' (ψ'' t) t)
    (hint1 : IntervalIntegrable (fun t => w t * ψ'' t) volume (0:ℝ) X)
    (hint2 : IntervalIntegrable (fun t => w'' t * ψ t) volume (0:ℝ) X) :
    (∫ t in (0:ℝ)..X, w t * ψ'' t)
      = (∫ t in (0:ℝ)..X, w'' t * ψ t)
        + (w X * ψ' X - w' X * ψ X) - (w 0 * ψ' 0 - w' 0 * ψ 0) := by
  have hg : ∀ t ∈ Set.uIcc 0 X, HasDerivAt (fun t => w t * ψ' t - w' t * ψ t)
      (w t * ψ'' t - w'' t * ψ t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => w t * ψ' t) (w' t * ψ' t + w t * ψ'' t) t :=
      (hw t ht).mul (hψ' t ht)
    have h2 : HasDerivAt (fun t => w' t * ψ t) (w'' t * ψ t + w' t * ψ' t) t :=
      (hw' t ht).mul (hψ t ht)
    exact (h1.sub h2).congr_deriv (by ring)
  have hint : IntervalIntegrable (fun t => w t * ψ'' t - w'' t * ψ t) volume (0:ℝ) X :=
    hint1.sub hint2
  have hmain := intervalIntegral.integral_eq_sub_of_hasDerivAt hg hint
  rw [intervalIntegral.integral_sub hint1 hint2] at hmain
  calc (∫ t in (0:ℝ)..X, w t * ψ'' t)
      = (∫ t in (0:ℝ)..X, w'' t * ψ t)
          + ((∫ t in (0:ℝ)..X, w t * ψ'' t) - (∫ t in (0:ℝ)..X, w'' t * ψ t)) := by ring
    _ = (∫ t in (0:ℝ)..X, w'' t * ψ t)
          + (w X * ψ' X - w' X * ψ X - (w 0 * ψ' 0 - w' 0 * ψ 0)) := by rw [hmain]
    _ = (∫ t in (0:ℝ)..X, w'' t * ψ t)
          + (w X * ψ' X - w' X * ψ X) - (w 0 * ψ' 0 - w' 0 * ψ 0) := by ring

private theorem hasDerivAt_exp_mul_sub (σ X t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(σ * t)) * (X - t))
      (-Real.exp (-(σ * t)) * (σ * (X - t) + 1)) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-(σ * t))) (Real.exp (-(σ * t)) * (-σ)) t := by
    have h : HasDerivAt (fun t : ℝ => -(σ * t)) (-σ) t := by
      simpa using (hasDerivAt_id t).const_mul (-σ)
    exact h.exp
  have h2 : HasDerivAt (fun t : ℝ => X - t) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub X
  exact (h1.mul h2).congr_deriv (by ring)

private theorem hasDerivAt_negExp_mul (σ X t : ℝ) :
    HasDerivAt (fun t : ℝ => -Real.exp (-(σ * t)) * (σ * (X - t) + 1))
      (Real.exp (-(σ * t)) * (σ ^ 2 * (X - t) + 2 * σ)) t := by
  have h1 : HasDerivAt (fun t : ℝ => -Real.exp (-(σ * t))) (Real.exp (-(σ * t)) * σ) t := by
    have h : HasDerivAt (fun t : ℝ => Real.exp (-(σ * t))) (Real.exp (-(σ * t)) * (-σ)) t := by
      have h2 : HasDerivAt (fun t : ℝ => -(σ * t)) (-σ) t := by
        simpa using (hasDerivAt_id t).const_mul (-σ)
      exact h2.exp
    exact h.neg.congr_deriv (by ring)
  have h2 : HasDerivAt (fun t : ℝ => σ * (X - t) + 1) (-σ) t := by
    have h3 : HasDerivAt (fun t : ℝ => X - t) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub X
    simpa using (h3.const_mul σ)
  exact (h1.mul h2).congr_deriv (by ring)

private theorem hasDerivAt_psi (y t : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun t : ℝ => (1 - Real.cos (y * t)) / y ^ 2) (Real.sin (y * t) / y) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.cos (y * t)) (-Real.sin (y * t) * y) t := by
    have h : HasDerivAt (fun t : ℝ => y * t) y t := by
      simpa using (hasDerivAt_id t).const_mul y
    exact h.cos
  have h2 : HasDerivAt (fun t : ℝ => 1 - Real.cos (y * t)) (Real.sin (y * t) * y) t := by
    have h := h1.const_sub (1:ℝ)
    exact h.congr_deriv (by ring)
  exact (h2.div_const (y^2)).congr_deriv (by field_simp)

private theorem hasDerivAt_psi' (y t : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.sin (y * t) / y) (Real.cos (y * t)) t := by
  have h1 : HasDerivAt (fun t : ℝ => Real.sin (y * t)) (Real.cos (y * t) * y) t := by
    have h : HasDerivAt (fun t : ℝ => y * t) y t := by
      simpa using (hasDerivAt_id t).const_mul y
    exact h.sin
  exact (h1.div_const y).congr_deriv (by field_simp)

/-- **The real-variable inequality behind Condition 2.**  For `σ ≥ 0`, `X ≥ 0` and any real `y`,

`∫₀^X e^{-σt} cos(y t) (X - t) dt ≥ 0`.

Proof: the `y = 0` case has a non-negative integrand.  For `y ≠ 0`, `ψ(t) = (1-cos(y t))/y²` is
`≥ 0` with `ψ'' = cos(y·)` and `ψ(0) = ψ'(0) = 0`, and `w(t) = e^{-σt}(X-t)` satisfies `w(X) = 0`,
`w'(X) = -e^{-σX}` and `w'' ≥ 0` on `[0,X]`; `integral_mul_second_deriv_eq` turns `∫ w ψ''` into
`∫ w'' ψ + e^{-σX} ψ(X)`, a sum of non-negative terms. -/
private theorem cos_exp_triangle_nonneg (σ y X : ℝ) (hσ : 0 ≤ σ) (hX : 0 ≤ X) :
    0 ≤ ∫ t in (0:ℝ)..X, Real.exp (-(σ * t)) * Real.cos (y * t) * (X - t) := by
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    apply intervalIntegral.integral_nonneg hX
    intro t ht
    have h2 : 0 ≤ X - t := by linarith [ht.2]
    have he : Real.exp (-(σ * t)) * Real.cos (0 * t) * (X - t)
        = Real.exp (-(σ * t)) * (X - t) := by
      rw [zero_mul, Real.cos_zero, mul_one]
    rw [he]
    exact mul_nonneg (Real.exp_nonneg _) h2
  · have hkey : (∫ t in (0:ℝ)..X, Real.exp (-(σ * t)) * Real.cos (y * t) * (X - t))
        = (∫ t in (0:ℝ)..X,
            Real.exp (-(σ * t)) * (σ^2 * (X - t) + 2 * σ) * ((1 - Real.cos (y * t)) / y^2))
          + Real.exp (-(σ * X)) * ((1 - Real.cos (y * X)) / y^2) := by
      set W : ℝ → ℝ := fun t => Real.exp (-(σ * t)) * (X - t) with hW
      set W' : ℝ → ℝ := fun t => -Real.exp (-(σ * t)) * (σ * (X - t) + 1) with hW'
      set W'' : ℝ → ℝ := fun t => Real.exp (-(σ * t)) * (σ ^ 2 * (X - t) + 2 * σ) with hW''
      set Ψ : ℝ → ℝ := fun t => (1 - Real.cos (y * t)) / y ^ 2 with hΨ
      set Ψ' : ℝ → ℝ := fun t => Real.sin (y * t) / y with hΨ'
      set Ψ'' : ℝ → ℝ := fun t => Real.cos (y * t) with hΨ''
      have hd1 : ∀ t ∈ Set.uIcc (0:ℝ) X, HasDerivAt W (W' t) t := by
        intro t _
        rw [hW, hW']
        exact hasDerivAt_exp_mul_sub σ X t
      have hd2 : ∀ t ∈ Set.uIcc (0:ℝ) X, HasDerivAt W' (W'' t) t := by
        intro t _
        rw [hW', hW'']
        exact hasDerivAt_negExp_mul σ X t
      have hd3 : ∀ t ∈ Set.uIcc (0:ℝ) X, HasDerivAt Ψ (Ψ' t) t := by
        intro t _
        rw [hΨ, hΨ']
        exact hasDerivAt_psi y t hy
      have hd4 : ∀ t ∈ Set.uIcc (0:ℝ) X, HasDerivAt Ψ' (Ψ'' t) t := by
        intro t _
        rw [hΨ', hΨ'']
        exact hasDerivAt_psi' y t hy
      have hcont1 : Continuous fun t => W t * Ψ'' t := by
        rw [hW, hΨ'']
        fun_prop
      have hcont2 : Continuous fun t => W'' t * Ψ t := by
        rw [hW'', hΨ]
        fun_prop
      have hint1 : IntervalIntegrable (fun t => W t * Ψ'' t) volume (0:ℝ) X :=
        hcont1.intervalIntegrable _ _
      have hint2 : IntervalIntegrable (fun t => W'' t * Ψ t) volume (0:ℝ) X :=
        hcont2.intervalIntegrable _ _
      have hkey0 := integral_mul_second_deriv_eq hd1 hd2 hd3 hd4 hint1 hint2
      -- the boundary term: `ψ(0) = ψ'(0) = 0`, `w(X) = 0`, `w'(X) = -e^{-σX}`
      have hbracket : (W X * Ψ' X - W' X * Ψ X) - (W 0 * Ψ' 0 - W' 0 * Ψ 0)
          = Real.exp (-(σ * X)) * ((1 - Real.cos (y * X)) / y ^ 2) := by
        simp only [hW, hW', hW'', hΨ, hΨ', hΨ'']
        simp only [sub_self, mul_zero, Real.exp_zero, Real.sin_zero, Real.cos_zero, sub_zero,
          zero_sub, zero_mul, one_mul, mul_one, zero_div]
        ring
      have hL : (∫ t in (0:ℝ)..X, W t * Ψ'' t)
          = ∫ t in (0:ℝ)..X, Real.exp (-(σ * t)) * Real.cos (y * t) * (X - t) := by
        rw [hW, hΨ'']
        apply intervalIntegral.integral_congr
        intro t _
        show Real.exp (-(σ * t)) * (X - t) * Real.cos (y * t)
          = Real.exp (-(σ * t)) * Real.cos (y * t) * (X - t)
        ring
      have hR : (∫ t in (0:ℝ)..X, W'' t * Ψ t)
          = ∫ t in (0:ℝ)..X,
              Real.exp (-(σ * t)) * (σ^2 * (X - t) + 2 * σ) * ((1 - Real.cos (y * t)) / y^2) := by
        rw [hW'', hΨ]
      calc (∫ t in (0:ℝ)..X, Real.exp (-(σ * t)) * Real.cos (y * t) * (X - t))
          = (∫ t in (0:ℝ)..X, W t * Ψ'' t) := hL.symm
        _ = (∫ t in (0:ℝ)..X, W'' t * Ψ t)
              + (W X * Ψ' X - W' X * Ψ X) - (W 0 * Ψ' 0 - W' 0 * Ψ 0) := hkey0
        _ = (∫ t in (0:ℝ)..X, W'' t * Ψ t)
              + (W X * Ψ' X - W' X * Ψ X - (W 0 * Ψ' 0 - W' 0 * Ψ 0)) := by ring
        _ = (∫ t in (0:ℝ)..X, W'' t * Ψ t)
              + Real.exp (-(σ * X)) * ((1 - Real.cos (y * X)) / y ^ 2) := by rw [hbracket]
        _ = (∫ t in (0:ℝ)..X,
              Real.exp (-(σ * t)) * (σ^2 * (X - t) + 2 * σ) * ((1 - Real.cos (y * t)) / y^2))
              + Real.exp (-(σ * X)) * ((1 - Real.cos (y * X)) / y ^ 2) := by rw [hR]
    rw [hkey]
    apply add_nonneg
    · -- `w'' ≥ 0` and `ψ ≥ 0` on `[0,X]`, so `∫ w'' ψ ≥ 0`
      apply intervalIntegral.integral_nonneg hX
      intro t ht
      apply mul_nonneg
      · apply mul_nonneg (Real.exp_nonneg _)
        have h1 : 0 ≤ σ ^ 2 * (X - t) := mul_nonneg (sq_nonneg σ) (by linarith [ht.2])
        linarith [hσ]
      · exact div_nonneg (by linarith [Real.cos_le_one (y * t)]) (by positivity)
    · -- the boundary term `e^{-σX} ψ(X) ≥ 0`
      apply mul_nonneg (Real.exp_nonneg _)
      exact div_nonneg (by linarith [Real.cos_le_one (y * X)]) (by positivity)

/-- **Assembly step.**  Given the real-variable inequality `∫₀^X e^{-σt} cos(yt) (X-t) dt ≥ 0`
(`σ ≥ 0`, `X ≥ 0`), the Laplace transform of the triangle `f(t) = (x₀ - t)⁺` has non-negative real
part on the closed right half-plane.  The reduction is: `(x₀-t)⁺ = x₀-t` on `[0,x₀]`, the real part
commutes with the interval integral, and `Re e^{-zt} = e^{-(Re z)t} cos((Im z)t)`. -/
private theorem triangle_hFnn_of_core
    (hcore : ∀ σ y X : ℝ, 0 ≤ σ → 0 ≤ X →
      0 ≤ ∫ t in (0:ℝ)..X, Real.exp (-(σ * t)) * Real.cos (y * t) * (X - t))
    {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(z * (t : ℂ))) * (((max (x₀ - t) 0 : ℝ)) : ℂ)).re := by
  intro z hz
  have hle : (0:ℝ) ≤ x₀ := le_of_lt hx₀
  have hcont : Continuous fun t : ℝ =>
      Complex.exp (-(z * (t : ℂ))) * (((max (x₀ - t) 0 : ℝ)) : ℂ) := by fun_prop
  have hint : IntervalIntegrable
      (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) * (((max (x₀ - t) 0 : ℝ)) : ℂ)) volume
      (0:ℝ) x₀ := hcont.intervalIntegrable _ _
  rw [Commons.NumberTheory.Linnik.re_laplace_eq (z := z) (x₀ := x₀)
    (f := fun t : ℝ => max (x₀ - t) 0) hint]
  have hmax : (∫ t in (0:ℝ)..x₀,
        Real.exp (-(z.re * t)) * Real.cos (z.im * t) * max (x₀ - t) 0)
      = ∫ t in (0:ℝ)..x₀, Real.exp (-(z.re * t)) * Real.cos (z.im * t) * (x₀ - t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    simp only [max_eq_left (show (0:ℝ) ≤ x₀ - t by linarith [ht.2])]
  rw [hmax]
  exact hcore z.re z.im x₀ hz hle

/-- **Condition 2 for the triangle test function** (Heath-Brown §8: “the simplest choice of `f`,
namely `f(t) = x₀-t` for `0 ≤ t ≤ x₀`, `0` for `t ≥ x₀`, for which Conditions 1 and 2 are easily
verified”).  The Laplace transform of the triangle has non-negative real part on the closed right
half-plane: `Re ∫₀^{x₀} e^{-zt}(x₀-t)⁺ dt ≥ 0` for `Re z ≥ 0`.

This is the `hFnn` hypothesis of `Commons.NumberTheory.Linnik.lemma6_3_full`.  Proof: the closed form
`∫₀^{x₀} e^{-zt}(x₀-t)dt = (x₀z - 1 + e^{-x₀z})/z²` (equal to `x₀²/2` at `z = 0`), together with the
elementary estimate `Re ∫₀^{x₀} e^{-σt}(x₀-t)cos(ty)dt ≥ 0` for `σ ≥ 0` (at `σ = 0` this is
`(1-cos(x₀y))/y² ≥ 0`; for `σ > 0`, `w = x₀ z`, `Re((w-1+e^{-w})/w²) ≥ 0`). -/
theorem triangle_hFnn {x₀ : ℝ} (hx₀ : 0 < x₀) :
    ∀ z : ℂ, 0 ≤ z.re →
      0 ≤ (∫ t in (0:ℝ)..x₀,
        Complex.exp (-(z * (t : ℂ))) * (((max (x₀ - t) 0 : ℝ)) : ℂ)).re :=
  triangle_hFnn_of_core cos_exp_triangle_nonneg hx₀

end Work.LinnikAreas

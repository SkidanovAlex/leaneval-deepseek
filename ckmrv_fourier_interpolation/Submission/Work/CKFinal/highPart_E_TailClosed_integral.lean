/-
# The `high` part of the CKMRV layer as a closed form plus a finite integral

`Work.Asymptotics.highPart G τ r` is the closed form of `4 sin²(πr²/2) ∫_1^∞ 𝒢(τ,it) e^{-πr²t}dt`,
while `Work.Asymptotics.E_TailClosed G B τ r` is the closed form of the same expression with the
threshold `B` in place of `1`.  Subtracting the two closed forms leaves the contribution of the
*finite* interval `(1,B)`, which is an ordinary (absolutely convergent) Bochner integral; this is
the identity

  `highPart G τ r = E_TailClosed G B τ r
      + sinSq r * ∫_1^B Aexp G τ t · e^{-πr²t} dt`.

The two closed forms both have the shape `tcLambda G • τ (πr²)` evaluated at two different
thresholds, so the identity is equivalent to the statement that the function

  `B ↦ E_TailClosed G B τ r + sinSq r * ∫_1^B Aexp G τ t · e^{-πr²t} dt`

is constant, equal to `highPart G τ r` at `B = 1`.  We prove constancy by differentiating in `B`:
the derivative of the closed form is `- sinSq r` times the integrand (this is where the two
regularising factors `(πr²)² psi1(πr²) = (πr²-2π)² psi1(πr²-2π) = 2 - 2cos(πr²) = sinSq r` are
used), which is exactly cancelled by the fundamental theorem of calculus for the interval
integral.  This route is uniform in `B` and in `r`: no convergence hypothesis and no separate
treatment of the degenerate values `r = 0` and `πr² = 2π` is needed.

## Main results

* `Work.CKFinal.highPart_E_TailClosed_integral` — the identity above.
-/
import Mathlib
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.E_TailClosed

noncomputable section

open MeasureTheory Filter Topology UpperHalfPlane

namespace Work.CKFinal

open Work.Asymptotics

/-! ## Derivative of `Complex.exp (-(c * b))` and of the affine piece `(c b + 1) e^{-cb}` -/

/-- The derivative of `b ↦ exp (-(c * b))` with respect to the *real* variable `b`. -/
lemma highPart_ETC_hasDerivAt_exp_neg_mul_c (c : ℂ) (B : ℝ) :
    HasDerivAt (fun b : ℝ => Complex.exp (-(c * (b : ℂ))))
      (-(c * Complex.exp (-(c * (B : ℂ))))) B := by
  have h1 : HasDerivAt (fun b : ℝ => (b : ℂ)) (1 : ℂ) B := by
    simpa using HasDerivAt.ofReal_comp (hasDerivAt_id B)
  have h2 : HasDerivAt (fun b : ℝ => -(c * (b : ℂ))) (-c) B := by
    simpa only [neg_mul, mul_one] using (h1.const_mul (-c))
  have h3 := (Complex.hasDerivAt_exp (-(c * (B : ℂ)))).comp B h2
  rw [Function.comp_def] at h3
  refine h3.congr_deriv ?_
  ring

/-- The derivative of `b ↦ K (c b + 1) exp (-(c b))` with respect to the real variable `b`. -/
lemma highPart_ETC_hasDerivAt_const_mul_affine_mul_exp_neg (c K : ℂ) (B : ℝ) :
    HasDerivAt (fun b : ℝ => K * (c * (b : ℂ) + 1) * Complex.exp (-(c * (b : ℂ))))
      (K * (-(c ^ 2 * (B : ℂ) * Complex.exp (-(c * (B : ℂ)))))) B := by
  have hlin : HasDerivAt (fun b : ℝ => c * (b : ℂ) + 1) c B := by
    have h1 : HasDerivAt (fun b : ℝ => (b : ℂ)) (1 : ℂ) B := by
      simpa using HasDerivAt.ofReal_comp (hasDerivAt_id B)
    have h2 : HasDerivAt (fun b : ℝ => c * (b : ℂ)) c B := by
      simpa using h1.const_mul c
    simpa using h2.add_const 1
  have hexp := highPart_ETC_hasDerivAt_exp_neg_mul_c c B
  have h3 : HasDerivAt (fun b : ℝ => (c * (b : ℂ) + 1) * Complex.exp (-(c * (b : ℂ))))
      (c * Complex.exp (-(c * (B : ℂ)))
        + (c * (B : ℂ) + 1) * (-(c * Complex.exp (-(c * (B : ℂ)))))) B := hlin.mul hexp
  have h4 := h3.const_mul K
  refine (h4.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with b
    exact mul_assoc K (c * (b : ℂ) + 1) (Complex.exp (-(c * (b : ℂ))))
  · ring

/-! ## Derivative of the closed form `tcLambda` in its threshold -/

/-- **The derivative of `B ↦ tcLambda G B w u` in the threshold `B`.**  Writing `λ = u` and
`μ = u - 2π` for the two exponents, the derivative is

  `-[(λ² psiC λ) e^{-λB} (G₀₀ + iB G₀₁) + (μ² psiC μ) e^{-μB} (G₁₀ + iB G₁₁)]`,

which is the closed form of `-B`-derivative of the two regularised moment integrals. -/
lemma highPart_ETC_hasDerivAt_tcLambda_B (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (w : UpperHalfPlane) (u B : ℝ) :
    HasDerivAt (fun b : ℝ => tcLambda G b w u)
      (-(((u : ℂ) ^ 2 * psiC u)
            * (Complex.exp (-((u : ℂ) * (B : ℂ))) * (G 0 0 w + (B : ℂ) * Complex.I * G 0 1 w))
          + (((u - 2 * Real.pi : ℝ) : ℂ) ^ 2 * psiC (u - 2 * Real.pi))
            * (Complex.exp (-(((u - 2 * Real.pi : ℝ) : ℂ) * (B : ℂ)))
                * (G 1 0 w + (B : ℂ) * Complex.I * G 1 1 w)))) B := by
  have h1 := ((highPart_ETC_hasDerivAt_exp_neg_mul_c (u : ℂ) B).const_mul
    ((u : ℂ) * psiC u)).mul_const (G 0 0 w)
  have h2 := (highPart_ETC_hasDerivAt_const_mul_affine_mul_exp_neg (u : ℂ)
    (Complex.I * psiC u) B).mul_const (G 0 1 w)
  have h3 := ((highPart_ETC_hasDerivAt_exp_neg_mul_c (((u - 2 * Real.pi : ℝ) : ℂ)) B).const_mul
      (((u - 2 * Real.pi : ℝ) : ℂ) * psiC (u - 2 * Real.pi))).mul_const (G 1 0 w)
  have h4 := (highPart_ETC_hasDerivAt_const_mul_affine_mul_exp_neg (((u - 2 * Real.pi : ℝ) : ℂ))
      (Complex.I * psiC (u - 2 * Real.pi)) B).mul_const (G 1 1 w)
  have hsum := ((h1.add h2).add h3).add h4
  refine (hsum.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with b
    simp only [tcLambda, Pi.add_apply]
  · ring

/-! ## Derivative of `E_TailClosed` in the threshold -/

/-- The two regularising identities at `λ = πr²` and `μ = πr² - 2π`:
`λ² psiC λ = μ² psiC μ = sinSq r`. -/
lemma highPart_ETC_sq_mul_psiC (r : ℝ) :
    ((Real.pi * r ^ 2 : ℝ) : ℂ) ^ 2 * psiC (Real.pi * r ^ 2) = sinSq r
      ∧ ((Real.pi * r ^ 2 - 2 * Real.pi : ℝ) : ℂ) ^ 2 * psiC (Real.pi * r ^ 2 - 2 * Real.pi)
          = sinSq r := by
  constructor
  · have h1 := sq_mul_psi1 (Real.pi * r ^ 2)
    rw [sinSq_eq_two_sub_two_cos r, psiC, ← h1]
    push_cast
    ring
  · have h1 := sq_mul_psi1 (Real.pi * r ^ 2 - 2 * Real.pi)
    rw [sinSq_eq_two_sub_two_cos_sub r, psiC, ← h1]
    push_cast
    ring

/-- **The derivative of `B ↦ E_TailClosed G B w r`.**  It is `- sinSq r` times the `Aexp`
integrand at the threshold. -/
lemma highPart_ETC_hasDerivAt_E_TailClosed_B (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (w : UpperHalfPlane) (r B : ℝ) :
    HasDerivAt (fun b : ℝ => E_TailClosed G b w r)
      (-(sinSq r * (Aexp G w B * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (B : ℂ)))))) B := by
  have h := highPart_ETC_hasDerivAt_tcLambda_B G w (Real.pi * r ^ 2) B
  have hfun : (fun b : ℝ => E_TailClosed G b w r)
      = fun b : ℝ => tcLambda G b w (Real.pi * r ^ 2) := by
    funext b; rfl
  rw [hfun]
  refine h.congr_deriv ?_
  obtain ⟨hsinL, hsinM⟩ := highPart_ETC_sq_mul_psiC r
  have hargT : Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (B : ℂ)))
      = Complex.exp (-(((Real.pi * r ^ 2 : ℝ) : ℂ) * (B : ℂ))) := by
    congr 1; push_cast; ring
  have hexp2 : Complex.exp (-((((Real.pi * r ^ 2 - 2 * Real.pi : ℝ)) : ℂ) * (B : ℂ)))
      = Complex.exp (2 * Real.pi * B)
        * Complex.exp (-(((Real.pi * r ^ 2 : ℝ) : ℂ) * (B : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [hargT]
  simp only [Aexp]
  rw [hsinL, hsinM, hexp2]
  ring

/-- At the threshold `B = 1` the closed form of the tail is exactly `highPart`. -/
lemma highPart_ETC_E_TailClosed_one (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (w : UpperHalfPlane) (r : ℝ) :
    E_TailClosed G 1 w r = highPart G w r := by
  rw [E_TailClosed, tcLambda, highPart_eq_sum]
  simp only [psiC, hiA, hiB, mul_one, Complex.ofReal_one]
  ring

/-! ## The identity -/

/-- **`highPart` is the closed form of the tail plus the finite interval integral.** -/
theorem highPart_E_TailClosed_integral (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) (B r : ℝ) :
    Work.Asymptotics.highPart G τ r
      = Work.Asymptotics.E_TailClosed G B τ r
        + Work.Asymptotics.sinSq r * ∫ t in (1 : ℝ)..B,
            Work.Asymptotics.Aexp G τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
  set g : ℝ → ℂ := fun t => Aexp G τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
    with hg
  set D : ℝ → ℂ := fun b => E_TailClosed G b τ r + sinSq r * (∫ t in (1 : ℝ)..b, g t)
    - highPart G τ r with hD
  have hgc : Continuous g := by
    rw [hg]
    simp only [Aexp]
    fun_prop
  have hDderiv : ∀ b : ℝ, HasDerivAt D 0 b := by
    intro b
    have h1 := highPart_ETC_hasDerivAt_E_TailClosed_B G τ r b
    have h2 : HasDerivAt (fun u : ℝ => ∫ t in (1 : ℝ)..u, g t) (g b) b :=
      intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable 1 b)
        (hgc.stronglyMeasurableAtFilter volume (𝓝 b)) hgc.continuousAt
    have h3 := (h1.add (h2.const_mul (sinSq r))).sub_const (highPart G τ r)
    refine h3.congr_deriv ?_
    rw [hg]
    ring
  have hDone : D 1 = 0 := by
    show E_TailClosed G 1 τ r + sinSq r * (∫ t in (1 : ℝ)..1, g t) - highPart G τ r = 0
    rw [intervalIntegral.integral_same, mul_zero, add_zero,
      highPart_ETC_E_TailClosed_one G τ r, sub_self]
  have hconst := is_const_of_deriv_eq_zero (𝕜 := ℝ) (f := D)
    (fun b => (hDderiv b).differentiableAt) (fun b => (hDderiv b).deriv) B 1
  have hDB : E_TailClosed G B τ r + sinSq r * (∫ t in (1 : ℝ)..B, g t)
      - highPart G τ r = 0 := by
    show D B = 0
    rw [hconst, hDone]
  exact (sub_eq_zero.mp hDB).symm

end Work.CKFinal

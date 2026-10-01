import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs

/-!
# `tf72conv_eq_f` — the convolution `g ∗ g` is the explicit polynomial `f`

Heath-Brown (1992), Lemma 7.2: the test function of the variational problem of §7 is
`f = g ∗ g`, where `g t = λ max 0 (1 - λ²t²)` is the continuous, even, non-negative
function supported in `[-1/λ, 1/λ]`.  On `[0, 2/λ]` the convolution is the explicit
polynomial

  `f x = (λ/30) (2 - λx)³ (4 + 6λx + λ²x²)`.

In the notation of `testFn72_defs` this is the identity

  `tf72conv lam t = tf72f lam t`   for `0 ≤ t ≤ 2/λ`,

which is what this file proves.  The proof is a direct computation:

* `tf72conv_eq_interval` restricts the full-line Lebesgue integral to the support
  interval `[t - 1/λ, 1/λ]` (the only place where `g s · g (t - s) ≠ 0`);
* `tf72g_mul_eq_poly` identifies the integrand with the polynomial
  `λ²(1 - λ²s²)(1 - λ²(t-s)²)` there (the two `max 0`'s are inactive);
* `tf72conv_subst` rescales `u = λs`, which turns the integral into
  `λ ∫_{λt-1}^{1} (1-u²)(1-(λt-u)²) du`;
* `tf72conv_poly_integral` evaluates that last integral as
  `(1/30)(2-x)³(4+6x+x²)` at `x = λt` (fundamental theorem of calculus with the
  explicit antiderivative `(1-x²)u + xu² + (x²-2)u³/3 - xu⁴/2 + u⁵/5`).

The final step is one polynomial identity, `tf72f_eq_poly`.
-/

namespace Work.ZeroFreeTables

/-- The polynomial integral behind HB Lemma 7.2: for the integrand
`(1-u²)(1-(x-u)²)` (which is `≥ 0` on `u ∈ [x-1,1]` when `0 ≤ x ≤ 2`, cf. the
convolution integrand), one has
`∫_{x-1}^{1} (1-u²)(1-(x-u)²) du = (1/30)(2-x)³(4+6x+x²)`.

The antiderivative of the integrand is
`(1-x²)u + xu² + (x²-2)u³/3 - xu⁴/2 + u⁵/5`, and the resulting identity in `x` is a
polynomial identity. -/
lemma tf72conv_poly_integral (x : ℝ) (hx : x ∈ Set.Icc 0 2) :
    (∫ u in (x-1)..1, (1-u^2)*(1-(x-u)^2)) = (1/30)*(2-x)^3*(4+6*x+x^2) := by
  have hderiv : ∀ u ∈ Set.uIcc (x-1) 1,
      HasDerivAt (fun y : ℝ => (1-x^2)*y + x*y^2 + ((x^2-2)/3)*y^3 - (x/2)*y^4 + y^5/5)
        ((1-u^2)*(1-(x-u)^2)) u := by
    intro u _
    have h1 : HasDerivAt (fun y : ℝ => (1-x^2)*y) (1-x^2) u := by
      simpa using (hasDerivAt_id u).const_mul (1-x^2)
    have h2 : HasDerivAt (fun y : ℝ => x*y^2) (x*(2*u)) u := by
      simpa using (hasDerivAt_pow 2 u).const_mul x
    have h3 : HasDerivAt (fun y : ℝ => ((x^2-2)/3)*y^3) (((x^2-2)/3)*(3*u^2)) u := by
      simpa using (hasDerivAt_pow 3 u).const_mul ((x^2-2)/3)
    have h4 : HasDerivAt (fun y : ℝ => (x/2)*y^4) ((x/2)*(4*u^3)) u := by
      simpa using (hasDerivAt_pow 4 u).const_mul (x/2)
    have h5 : HasDerivAt (fun y : ℝ => y^5/5) ((5*u^4)/5) u := by
      simpa using (hasDerivAt_pow 5 u).div_const 5
    exact ((((h1.add h2).add h3).sub h4).add h5).congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((by fun_prop : Continuous fun u : ℝ => (1-u^2)*(1-(x-u)^2)).intervalIntegrable _ _)]
  ring

/-- Change of variables `u = λs` in the rescaled convolution integrand: the affine
map `s ↦ λs` sends the interval `[t - 1/λ, 1/λ]` to `[λt - 1, 1]` and
`λ²(1-λ²s²)(1-λ²(t-s)²)` to `λ²(1-u²)(1-(λt-u)²)`, the Jacobian contributing `1/λ`. -/
lemma tf72conv_subst (lam t : ℝ) (hlam : lam ≠ 0) :
    (∫ s in (t - 1/lam)..(1/lam), lam^2 * (1 - lam^2*s^2) * (1 - lam^2*(t-s)^2))
      = lam * ∫ u in (lam*t - 1)..1, (1 - u^2) * (1 - (lam*t - u)^2) := by
  have hpt : Set.EqOn (fun s : ℝ => lam^2 * (1 - lam^2*s^2) * (1 - lam^2*(t-s)^2))
      (fun s : ℝ => lam^2 * (1 - (lam*s)^2) * (1 - (lam*t - lam*s)^2))
      (Set.uIcc (t - 1/lam) (1/lam)) := fun s _ => by ring
  rw [intervalIntegral.integral_congr hpt]
  rw [intervalIntegral.integral_comp_mul_left
        (fun u : ℝ => lam^2 * (1 - u^2) * (1 - (lam*t - u)^2)) hlam]
  have h1 : lam * (t - 1/lam) = lam*t - 1 := by
    rw [mul_sub, mul_one_div, div_self hlam]
  have h2 : lam * (1/lam) = 1 := by rw [mul_one_div, div_self hlam]
  rw [h1, h2, smul_eq_mul]
  rw [show (∫ u in (lam*t-1)..1, lam^2 * (1-u^2)*(1-(lam*t-u)^2))
      = lam^2 * ∫ u in (lam*t-1)..1, (1-u^2)*(1-(lam*t-u)^2) by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; ext u; ring]
  field_simp

/-- Support restriction of the convolution `g ∗ g`: for `t ∈ [0, 2/λ]` the integrand
`s ↦ g s · g (t-s)` vanishes outside `[t - 1/λ, 1/λ]`, so the full-line Lebesgue
integral equals the integral over that interval. -/
lemma tf72conv_eq_interval (lam t : ℝ) (hlam : 0 < lam) (ht : t ∈ Set.Icc 0 (2/lam)) :
    tf72conv lam t = ∫ s in (t - 1/lam)..(1/lam), tf72g lam s * tf72g lam (t - s) := by
  have htwo : (2:ℝ)/lam = 1/lam + 1/lam := by ring
  have hpos : (0:ℝ) < 1/lam := by positivity
  have hab : t - 1/lam ≤ 1/lam := by linarith [ht.2, htwo]
  unfold tf72conv
  have hzero : ∀ s : ℝ, s ∉ Set.Icc (t - 1/lam) (1/lam) →
      tf72g lam s * tf72g lam (t - s) = 0 := by
    intro s hs
    by_cases h1 : s < t - 1/lam
    · have hsub : 0 < t - s := by linarith [h1, ht.1, hpos]
      have h : 1/lam ≤ |t - s| := by rw [abs_of_pos hsub]; linarith
      rw [tf72g_supp lam hlam (t - s) h, mul_zero]
    · have h2 : 1/lam < s := by
        by_contra h
        push Not at h
        exact hs ⟨not_lt.mp h1, h⟩
      have hsub : 0 < s := by linarith [h2, hpos]
      have h : 1/lam ≤ |s| := by rw [abs_of_pos hsub]; linarith
      rw [tf72g_supp lam hlam s h, zero_mul]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-- On the support interval `[t - 1/λ, 1/λ]` (for `t ∈ [0, 2/λ]`) both arguments of
the convolution lie in `[-1/λ, 1/λ]`, so the two `max 0`'s in `tf72g` are inactive
and the integrand is the polynomial `λ²(1-λ²s²)(1-λ²(t-s)²)`. -/
lemma tf72g_mul_eq_poly (lam t s : ℝ) (hlam : 0 < lam) (ht : t ∈ Set.Icc 0 (2/lam))
    (hs : s ∈ Set.Icc (t - 1/lam) (1/lam)) :
    tf72g lam s * tf72g lam (t - s) = lam^2 * (1 - lam^2*s^2) * (1 - lam^2*(t-s)^2) := by
  have h1 : 0 ≤ 1 - lam^2*s^2 := by
    have hle : lam * s ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hs.2 hlam.le
      rwa [mul_one_div, div_self hlam.ne'] at h
    have hge : -1 ≤ lam * s := by
      have h' : -(1/lam) ≤ s := by linarith [hs.1, ht.1]
      have h := mul_le_mul_of_nonneg_left h' hlam.le
      rwa [mul_neg, mul_one_div, div_self hlam.ne'] at h
    nlinarith [hle, hge, sq_nonneg (lam*s)]
  have h2 : 0 ≤ 1 - lam^2*(t-s)^2 := by
    have hle : lam * (t - s) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left (show t - s ≤ 1/lam by linarith [hs.1]) hlam.le
      rwa [mul_one_div, div_self hlam.ne'] at h
    have hge : -1 ≤ lam * (t - s) := by
      have h' : -(1/lam) ≤ t - s := by linarith [hs.2, ht.1]
      have h := mul_le_mul_of_nonneg_left h' hlam.le
      rwa [mul_neg, mul_one_div, div_self hlam.ne'] at h
    nlinarith [hle, hge, sq_nonneg (lam*(t-s))]
  unfold tf72g
  rw [max_eq_right h1, max_eq_right h2]
  ring

/-- **Heath-Brown (1992), Lemma 7.2** (limiting case `θ → 0`): on `[0, 2/λ]` the
convolution `g ∗ g` of the auxiliary function `g t = λ max 0 (1-λ²t²)` equals the
explicit polynomial `(λ/30)(2-λt)³(4+6λt+λ²t²)`, i.e. `tf72conv lam t = tf72f lam t`. -/
theorem tf72conv_eq_f (lam : ℝ) (hlam : 0 < lam) (t : ℝ) (ht : t ∈ Set.Icc 0 (2/lam)) :
    Work.ZeroFreeTables.tf72conv lam t = Work.ZeroFreeTables.tf72f lam t := by
  have htwo : (2:ℝ)/lam = 1/lam + 1/lam := by ring
  have hab : t - 1/lam ≤ 1/lam := by linarith [ht.2, htwo]
  have hlt : lam * t ≤ 2 := by
    have h := mul_le_mul_of_nonneg_left ht.2 hlam.le
    rwa [mul_div_cancel₀ _ hlam.ne'] at h
  have hx : lam * t ∈ Set.Icc (0:ℝ) 2 := ⟨mul_nonneg hlam.le ht.1, hlt⟩
  calc tf72conv lam t
      = ∫ s in (t - 1/lam)..(1/lam), tf72g lam s * tf72g lam (t - s) :=
          tf72conv_eq_interval lam t hlam ht
    _ = ∫ s in (t - 1/lam)..(1/lam), lam^2 * (1 - lam^2*s^2) * (1 - lam^2*(t-s)^2) := by
          refine intervalIntegral.integral_congr fun s hs => ?_
          rw [Set.uIcc_of_le hab] at hs
          exact tf72g_mul_eq_poly lam t s hlam ht hs
    _ = lam * ∫ u in (lam*t - 1)..1, (1 - u^2) * (1 - (lam*t - u)^2) :=
          tf72conv_subst lam t hlam.ne'
    _ = lam * ((1/30)*(2 - lam*t)^3*(4 + 6*(lam*t) + (lam*t)^2)) := by
          rw [tf72conv_poly_integral (lam*t) hx]
    _ = tf72f lam t := by
          rw [tf72f_eq_poly lam hlam t ht]; ring

end Work.ZeroFreeTables

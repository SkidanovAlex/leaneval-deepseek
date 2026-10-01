/-
# `tf71conv_eq_f` — HB Lemma 7.1: the convolution `g ⊛ g` is the closed form `f`

Heath-Brown (1992), Lemma 7.1: with `ζ = λ tan θ`, `γ = θ/ζ` and
`g t = λ(1+tan²θ)(cos(ζt) − cos θ)` on `[-γ,γ]` (`0` outside), the convolution
`f = g ⊛ g` is given on `[0,2γ]` by the closed form `tf71cf` of `testFn71_defs`.
In the notation there, this is

  `tf71conv θ lam x = tf71f θ lam x`   for `0 ≤ x ≤ 2γ`.

The proof follows the same scheme as the `θ → 0` case (`tf72conv_eq_f`):

* `tf71conv_eq_interval` restricts the full-line Lebesgue integral to the support
  interval `[x - γ, γ]`;
* `tf71g_mul_eq_trig` identifies the integrand there with
  `A²(cos ζs − cos θ)(cos ζ(x-s) − cos θ)`, `A = λ(1+tan²θ)`;
* `tf71conv_subst` rescales `u = ζs`, turning the integral into
  `(A²/ζ) ∫_{ζx-θ}^{θ} (cos u − cos θ)(cos(ζx−u) − cos θ) du`;
* `tf71_trig_integral` evaluates that last integral in closed form;
* `tf71cf_algebra` is the final algebraic comparison with `tf71cf`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn71_defs

noncomputable section
open scoped Real
namespace Work.ZeroFreeTables

/-! ## The elementary trigonometric integral -/

/-- `∫_{φ-θ}^{θ} (cos u − cos θ)(cos(φ−u) − cos θ) du` in closed form.

The antiderivative is
`(1/2)cos φ·u + (1/4) sin(2u−φ) − cos θ sin u + cos θ sin(φ−u) + cos²θ·u`. -/
lemma tf71_trig_integral (φ θ : ℝ) :
    (∫ u in (φ - θ)..θ, (Real.cos u - Real.cos θ) * (Real.cos (φ - u) - Real.cos θ))
      = (1/2) * Real.cos φ * (2 * θ - φ) + (1/2) * Real.sin (2 * θ - φ)
        - 2 * Real.cos θ * Real.sin θ + 2 * Real.cos θ * Real.sin (φ - θ)
        + (Real.cos θ)^2 * (2 * θ - φ) := by
  have hcos : ∀ u : ℝ, Real.cos u * Real.cos (φ - u)
      = (1/2)*Real.cos φ + (1/2)*Real.cos (2*u - φ) := by
    intro u
    have e1 : Real.cos φ = Real.cos u * Real.cos (φ-u) - Real.sin u * Real.sin (φ-u) := by
      have h1 : u + (φ - u) = φ := by ring
      have h2 := Real.cos_add u (φ - u)
      rwa [h1] at h2
    have e2 : Real.cos (2*u - φ) = Real.cos u * Real.cos (φ-u) + Real.sin u * Real.sin (φ-u) := by
      have h2 : u + (u - φ) = 2*u - φ := by ring
      have h3 : u - φ = -(φ - u) := by ring
      rw [← h2, Real.cos_add, h3, Real.cos_neg, Real.sin_neg]
      ring
    linarith
  have hderiv : ∀ u ∈ Set.uIcc (φ - θ) θ,
      HasDerivAt (fun y : ℝ => (1/2)*Real.cos φ*y + (1/4)*Real.sin (2*y - φ) - Real.cos θ * Real.sin y
        + Real.cos θ * Real.sin (φ - y) + (Real.cos θ)^2 * y)
        ((Real.cos u - Real.cos θ) * (Real.cos (φ - u) - Real.cos θ)) u := by
    intro u _
    have h1 : HasDerivAt (fun y : ℝ => (1/2)*Real.cos φ * y) ((1/2)*Real.cos φ) u := by
      simpa using (hasDerivAt_id u).const_mul ((1/2)*Real.cos φ)
    have h2 : HasDerivAt (fun y : ℝ => (1/4)*Real.sin (2*y - φ)) ((1/4)*(2*Real.cos (2*u-φ))) u := by
      have hh : HasDerivAt (fun y : ℝ => 2*y - φ) 2 u := by
        simpa using ((hasDerivAt_id u).const_mul 2).sub_const φ
      exact ((hh.sin).const_mul (1/4)).congr_deriv (by ring)
    have h3 : HasDerivAt (fun y : ℝ => Real.cos θ * Real.sin y) (Real.cos θ * Real.cos u) u := by
      simpa using (hasDerivAt_id u).sin.const_mul (Real.cos θ)
    have h4 : HasDerivAt (fun y : ℝ => Real.cos θ * Real.sin (φ - y))
        (Real.cos θ * ((-1)*Real.cos (φ-u))) u := by
      have hh : HasDerivAt (fun y : ℝ => φ - y) (-1) u :=
        (hasDerivAt_id u).const_sub φ
      exact ((hh.sin).const_mul (Real.cos θ)).congr_deriv (by ring)
    have h5 : HasDerivAt (fun y : ℝ => (Real.cos θ)^2 * y) ((Real.cos θ)^2) u := by
      simpa using (hasDerivAt_id u).const_mul ((Real.cos θ)^2)
    have hsum : HasDerivAt (fun y : ℝ => (1/2)*Real.cos φ*y + (1/4)*Real.sin (2*y - φ) - Real.cos θ * Real.sin y
        + Real.cos θ * Real.sin (φ - y) + (Real.cos θ)^2 * y)
        ((((1/2)*Real.cos φ + (1/4)*(2*Real.cos (2*u-φ))) - Real.cos θ * Real.cos u)
          + (Real.cos θ * ((-1)*Real.cos (φ-u))) + (Real.cos θ)^2) u :=
      (((h1.add h2).sub h3).add h4).add h5
    refine hsum.congr_deriv ?_
    rw [show (1/2) * Real.cos φ + (1/4) * (2 * Real.cos (2*u - φ)) = Real.cos u * Real.cos (φ - u) from by
          rw [hcos u]; ring]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((by fun_prop : Continuous fun u : ℝ =>
          (Real.cos u - Real.cos θ) * (Real.cos (φ - u) - Real.cos θ)).intervalIntegrable _ _)]
  rw [show 2 * (φ - θ) - φ = φ - 2*θ from by ring, show φ - (φ - θ) = θ from by ring,
      show φ - 2*θ = -(2*θ - φ) from by ring, Real.sin_neg]
  ring

/-! ## Restriction of the convolution to its support interval -/

theorem tf71conv_eq_interval (θ lam x : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam)
    (hx : x ∈ Set.Icc 0 (2 * tf71γ θ lam)) :
    tf71conv θ lam x = ∫ s in (x - tf71γ θ lam)..(tf71γ θ lam), tf71g θ lam s * tf71g θ lam (x - s) := by
  have hγ := tf71γ_pos hθ0 hθ1 hlam
  have hab : x - tf71γ θ lam ≤ tf71γ θ lam := by linarith [hx.2]
  unfold tf71conv
  have hzero : ∀ s : ℝ, s ∉ Set.Icc (x - tf71γ θ lam) (tf71γ θ lam) →
      tf71g θ lam s * tf71g θ lam (x - s) = 0 := by
    intro s hs
    by_cases h1 : s < x - tf71γ θ lam
    · have hsub : tf71γ θ lam < x - s := by linarith
      have hpos : 0 < x - s := lt_trans hγ hsub
      have h : tf71γ θ lam ≤ |x - s| := by rw [abs_of_pos hpos]; exact le_of_lt hsub
      rw [tf71g_supp hθ0 hθ1 hlam (x - s) h, mul_zero]
    · have h2 : tf71γ θ lam < s := by
        by_contra h
        push Not at h
        exact hs ⟨not_lt.mp h1, h⟩
      have hpos : 0 < s := lt_trans hγ h2
      have h : tf71γ θ lam ≤ |s| := by rw [abs_of_pos hpos]; exact le_of_lt h2
      rw [tf71g_supp hθ0 hθ1 hlam s h, zero_mul]
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
      MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-! ## The integrand on the support interval -/

/-- On `[x - γ, γ]` (for `x ∈ [0, 2γ]`) both arguments of the convolution lie in
`[-γ, γ]`, so the two `if`s in `tf71g` are inactive and the integrand is
`λ²(1+tan²θ)²(cos ζs − cos θ)(cos ζ(x-s) − cos θ)`. -/
lemma tf71g_mul_eq_trig (θ lam x s : ℝ)
    (hx : x ∈ Set.Icc 0 (2 * tf71γ θ lam))
    (hs : s ∈ Set.Icc (x - tf71γ θ lam) (tf71γ θ lam)) :
    tf71g θ lam s * tf71g θ lam (x - s)
      = (lam * (1 + Real.tan θ ^ 2))^2 * (Real.cos (tf71ζ θ lam * s) - Real.cos θ)
          * (Real.cos (tf71ζ θ lam * x - tf71ζ θ lam * s) - Real.cos θ) := by
  have h1 : |s| ≤ tf71γ θ lam := by
    rw [abs_le]
    exact ⟨by linarith [hs.1, hx.1], hs.2⟩
  have h2 : |x - s| ≤ tf71γ θ lam := by
    rw [abs_le]
    exact ⟨by linarith [hs.2, hx.1], by linarith [hs.1]⟩
  unfold tf71g
  rw [if_pos h1, if_pos h2]
  rw [show tf71ζ θ lam * (x - s) = tf71ζ θ lam * x - tf71ζ θ lam * s from by ring]
  ring

/-! ## Change of variables `u = ζs` -/

/-- Change of variables `u = ζs` in the (rescaled) convolution integrand: the
affine map `s ↦ ζs` sends `[x - γ, γ]` to `[ζx - θ, θ]` and
`A²(cos ζs − cos θ)(cos ζ(x-s) − cos θ)` to `A²(cos u − cos θ)(cos(ζx − u) − cos θ)`,
the Jacobian contributing `1/ζ`. -/
lemma tf71conv_subst (θ lam x : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    (∫ s in (x - tf71γ θ lam)..(tf71γ θ lam),
        (lam * (1 + Real.tan θ ^ 2))^2 * (Real.cos (tf71ζ θ lam * s) - Real.cos θ)
          * (Real.cos (tf71ζ θ lam * x - tf71ζ θ lam * s) - Real.cos θ))
      = (lam * (1 + Real.tan θ ^ 2))^2 / tf71ζ θ lam
          * ∫ u in (tf71ζ θ lam * x - θ)..θ,
              (Real.cos u - Real.cos θ) * (Real.cos (tf71ζ θ lam * x - u) - Real.cos θ) := by
  have hζ : tf71ζ θ lam ≠ 0 := ne_of_gt (tf71ζ_pos hθ0 hθ1 hlam)
  have hζγ : tf71ζ θ lam * tf71γ θ lam = θ := tf71ζ_mul_γ hθ0 hθ1 hlam
  have hcongr : (∫ s in (x - tf71γ θ lam)..(tf71γ θ lam),
        (lam * (1 + Real.tan θ ^ 2))^2 * (Real.cos (tf71ζ θ lam * s) - Real.cos θ)
          * (Real.cos (tf71ζ θ lam * x - tf71ζ θ lam * s) - Real.cos θ))
      = ∫ s in (x - tf71γ θ lam)..(tf71γ θ lam),
        (fun u : ℝ => (lam * (1 + Real.tan θ ^ 2))^2 * (Real.cos u - Real.cos θ)
          * (Real.cos (tf71ζ θ lam * x - u) - Real.cos θ)) (tf71ζ θ lam * s) :=
    intervalIntegral.integral_congr (fun s _ => rfl)
  rw [hcongr, intervalIntegral.integral_comp_mul_left
        (fun u : ℝ => (lam * (1 + Real.tan θ ^ 2))^2 * (Real.cos u - Real.cos θ)
          * (Real.cos (tf71ζ θ lam * x - u) - Real.cos θ)) hζ]
  rw [show tf71ζ θ lam * (x - tf71γ θ lam) = tf71ζ θ lam * x - θ by rw [mul_sub, hζγ],
      hζγ, smul_eq_mul]
  rw [show (∫ u in (tf71ζ θ lam * x - θ)..θ,
        (fun u : ℝ => (lam * (1 + Real.tan θ ^ 2))^2 * (Real.cos u - Real.cos θ)
          * (Real.cos (tf71ζ θ lam * x - u) - Real.cos θ)) u)
      = (lam * (1 + Real.tan θ ^ 2))^2 * (∫ u in (tf71ζ θ lam * x - θ)..θ,
              (Real.cos u - Real.cos θ) * (Real.cos (tf71ζ θ lam * x - u) - Real.cos θ)) from by
        rw [show (∫ u in (tf71ζ θ lam * x - θ)..θ,
              (fun u : ℝ => (lam * (1 + Real.tan θ ^ 2))^2 * (Real.cos u - Real.cos θ)
                * (Real.cos (tf71ζ θ lam * x - u) - Real.cos θ)) u)
            = ∫ u in (tf71ζ θ lam * x - θ)..θ,
                (lam * (1 + Real.tan θ ^ 2))^2 * ((Real.cos u - Real.cos θ)
                  * (Real.cos (tf71ζ θ lam * x - u) - Real.cos θ)) from
              intervalIntegral.integral_congr (fun u _ => by ring),
            intervalIntegral.integral_const_mul]]
  rw [div_eq_mul_inv]
  ring

/-! ## The final algebraic comparison -/

theorem tf71cf_algebra (θ lam x : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam) :
    (lam * (1 + Real.tan θ ^ 2))^2 / tf71ζ θ lam
      * ((1/2) * Real.cos (tf71ζ θ lam * x) * (2 * θ - tf71ζ θ lam * x)
          + (1/2) * Real.sin (2 * θ - tf71ζ θ lam * x)
          - 2 * Real.cos θ * Real.sin θ
          + 2 * Real.cos θ * Real.sin (tf71ζ θ lam * x - θ)
          + Real.cos θ ^ 2 * (2 * θ - tf71ζ θ lam * x))
    = tf71cf θ lam x := by
  have hsinθ : Real.sin θ ≠ 0 := tf71_sinθ_ne hθ0 hθ1
  have hcosθ : Real.cos θ ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩)
  have hsin2 : Real.sin (2*θ) ≠ 0 := tf71_sin2θ_ne hθ0 hθ1
  have hI1 : (lam * (1 + Real.tan θ ^ 2)) * (tf71γ θ lam - x/2) * Real.sin (2*θ)
      = 2*θ - tf71ζ θ lam * x := by
    rw [tf71γ, tf71ζ, Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp
    ring_nf
    linear_combination (2*θ*Real.cos θ - Real.sin θ * lam * x) * Real.sin_sq_add_cos_sq θ
  have hI2 : lam * (2*tf71γ θ lam - x) * Real.sin θ = Real.cos θ * (2*θ - tf71ζ θ lam * x) := by
    rw [tf71γ, tf71ζ, Real.tan_eq_sin_div_cos]
    field_simp
  have h1 : (lam * (1 + Real.tan θ ^ 2)) * (tf71γ θ lam - x/2)
      = (2*θ - tf71ζ θ lam * x) / Real.sin (2*θ) := (eq_div_iff hsin2).mpr hI1
  have h2 : lam * (2*tf71γ θ lam - x)
      = Real.cos θ * (2*θ - tf71ζ θ lam * x) / Real.sin θ := (eq_div_iff hsinθ).mpr hI2
  have hAζ : (lam * (1 + Real.tan θ ^ 2)) / tf71ζ θ lam = 2 / Real.sin (2*θ) := by
    rw [tf71ζ, Real.tan_eq_sin_div_cos, Real.sin_two_mul]
    field_simp
    ring_nf
    linear_combination Real.sin_sq_add_cos_sq θ
  have hA2 : (lam * (1 + Real.tan θ ^ 2))^2 / tf71ζ θ lam
      = (lam * (1 + Real.tan θ ^ 2)) * (2 / Real.sin (2*θ)) := by
    rw [pow_two, mul_div_assoc, hAζ]
  have hB : (2 / Real.sin (2*θ))
      * ((1/2) * Real.cos (tf71ζ θ lam * x) * (2 * θ - tf71ζ θ lam * x)
          + (1/2) * Real.sin (2 * θ - tf71ζ θ lam * x)
          - 2 * Real.cos θ * Real.sin θ
          + 2 * Real.cos θ * Real.sin (tf71ζ θ lam * x - θ)
          + Real.cos θ ^ 2 * (2 * θ - tf71ζ θ lam * x))
      = ((lam * (1 + Real.tan θ ^ 2)) * (tf71γ θ lam - x/2) * Real.cos (tf71ζ θ lam * x)
          + lam * (2 * tf71γ θ lam - x) + Real.sin (2 * θ - tf71ζ θ lam * x) / Real.sin (2 * θ)
          - 2 * (1 + Real.sin (θ - tf71ζ θ lam * x) / Real.sin θ)) := by
    rw [h1, h2,
        show Real.sin (tf71ζ θ lam * x - θ) = -Real.sin (θ - tf71ζ θ lam * x) from by
          rw [show tf71ζ θ lam * x - θ = -(θ - tf71ζ θ lam * x) from by ring, Real.sin_neg],
        Real.sin_two_mul]
    field_simp
    ring
  have hcf : tf71cf θ lam x = (lam * (1 + Real.tan θ ^ 2)) *
      ((lam * (1 + Real.tan θ ^ 2)) * (tf71γ θ lam - x/2) * Real.cos (tf71ζ θ lam * x)
        + lam * (2 * tf71γ θ lam - x) + Real.sin (2 * θ - tf71ζ θ lam * x) / Real.sin (2 * θ)
        - 2 * (1 + Real.sin (θ - tf71ζ θ lam * x) / Real.sin θ)) := by
    unfold tf71cf; ring
  calc (lam * (1 + Real.tan θ ^ 2))^2 / tf71ζ θ lam
        * ((1/2) * Real.cos (tf71ζ θ lam * x) * (2 * θ - tf71ζ θ lam * x)
            + (1/2) * Real.sin (2 * θ - tf71ζ θ lam * x)
            - 2 * Real.cos θ * Real.sin θ
            + 2 * Real.cos θ * Real.sin (tf71ζ θ lam * x - θ)
            + Real.cos θ ^ 2 * (2 * θ - tf71ζ θ lam * x))
      = (lam * (1 + Real.tan θ ^ 2)) * (2 / Real.sin (2*θ))
        * ((1/2) * Real.cos (tf71ζ θ lam * x) * (2 * θ - tf71ζ θ lam * x)
            + (1/2) * Real.sin (2 * θ - tf71ζ θ lam * x)
            - 2 * Real.cos θ * Real.sin θ
            + 2 * Real.cos θ * Real.sin (tf71ζ θ lam * x - θ)
            + Real.cos θ ^ 2 * (2 * θ - tf71ζ θ lam * x)) := by rw [hA2]
    _ = (lam * (1 + Real.tan θ ^ 2)) * ((2 / Real.sin (2*θ))
        * ((1/2) * Real.cos (tf71ζ θ lam * x) * (2 * θ - tf71ζ θ lam * x)
            + (1/2) * Real.sin (2 * θ - tf71ζ θ lam * x)
            - 2 * Real.cos θ * Real.sin θ
            + 2 * Real.cos θ * Real.sin (tf71ζ θ lam * x - θ)
            + Real.cos θ ^ 2 * (2 * θ - tf71ζ θ lam * x))) := by rw [mul_assoc]
    _ = (lam * (1 + Real.tan θ ^ 2)) *
        ((lam * (1 + Real.tan θ ^ 2)) * (tf71γ θ lam - x/2) * Real.cos (tf71ζ θ lam * x)
          + lam * (2 * tf71γ θ lam - x) + Real.sin (2 * θ - tf71ζ θ lam * x) / Real.sin (2 * θ)
          - 2 * (1 + Real.sin (θ - tf71ζ θ lam * x) / Real.sin θ)) := by rw [hB]
    _ = tf71cf θ lam x := by rw [hcf]

/-! ## HB Lemma 7.1, the convolution identity -/

theorem tf71conv_eq_f (θ lam : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) (hlam : 0 < lam)
    (x : ℝ) (hx : x ∈ Set.Icc 0 (2 * Work.ZeroFreeTables.tf71γ θ lam)) :
    Work.ZeroFreeTables.tf71conv θ lam x = Work.ZeroFreeTables.tf71f θ lam x := by
  have hab : x - tf71γ θ lam ≤ tf71γ θ lam := by linarith [hx.2]
  calc tf71conv θ lam x
      = ∫ s in (x - tf71γ θ lam)..(tf71γ θ lam), tf71g θ lam s * tf71g θ lam (x - s) :=
          tf71conv_eq_interval θ lam x hθ0 hθ1 hlam hx
    _ = ∫ s in (x - tf71γ θ lam)..(tf71γ θ lam),
          (lam * (1 + Real.tan θ ^ 2))^2 * (Real.cos (tf71ζ θ lam * s) - Real.cos θ)
            * (Real.cos (tf71ζ θ lam * x - tf71ζ θ lam * s) - Real.cos θ) := by
          refine intervalIntegral.integral_congr fun s hs => ?_
          rw [Set.uIcc_of_le hab] at hs
          exact tf71g_mul_eq_trig θ lam x s hx hs
    _ = (lam * (1 + Real.tan θ ^ 2))^2 / tf71ζ θ lam
          * ∫ u in (tf71ζ θ lam * x - θ)..θ,
              (Real.cos u - Real.cos θ) * (Real.cos (tf71ζ θ lam * x - u) - Real.cos θ) :=
          tf71conv_subst θ lam x hθ0 hθ1 hlam
    _ = (lam * (1 + Real.tan θ ^ 2))^2 / tf71ζ θ lam
          * ((1/2) * Real.cos (tf71ζ θ lam * x) * (2 * θ - tf71ζ θ lam * x)
              + (1/2) * Real.sin (2 * θ - tf71ζ θ lam * x)
              - 2 * Real.cos θ * Real.sin θ
              + 2 * Real.cos θ * Real.sin (tf71ζ θ lam * x - θ)
              + Real.cos θ ^ 2 * (2 * θ - tf71ζ θ lam * x)) := by
          rw [tf71_trig_integral]
    _ = tf71cf θ lam x := tf71cf_algebra θ lam x hθ0 hθ1 hlam
    _ = tf71f θ lam x := by rw [tf71f, if_pos hx.1, min_eq_left hx.2]

end Work.ZeroFreeTables

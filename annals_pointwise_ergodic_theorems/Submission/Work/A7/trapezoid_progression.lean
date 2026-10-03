import Mathlib
import Submission.Work.A7.ModelApproxCore_M0_defs
import Submission.Work.A7.ModelApproxCore_trapezoid

namespace Work.A7

open MeasureTheory intervalIntegral

/-! ## Two elementary substitution/chain-rule lemmas for affine reparametrisations

The trapezoid comparison `ModelApproxCore_trapezoid` is stated at unit step.  To transfer it to
the arithmetic progression `m ↦ a + q m` (`q > 0`) one applies it to `t ↦ w (a + q t)` and
reparametrises the two resulting integrals.  The two reparametrisation tools are collected here:

* `integral_comp_affine` — the affine change of variables for an interval integral in an arbitrary
  real normed space;
* `iteratedDeriv_two_comp_affine` — the second-order chain rule for `t ↦ w (a + q t)`, which says
  that the second derivative is scaled by `q ^ 2`.
-/

/-- **Affine change of variables for the interval integral.**
For `q ≠ 0`,
`∫_{m₁}^{m₂} f (a + q t) dt = q⁻¹ ∫_{a + q m₁}^{a + q m₂} f`.

Obtained from `integral_comp_mul_left` (the substitution `t ↦ q t`) followed by
`integral_comp_add_left` (the translation `x ↦ a + x`); no regularity of `f` is needed since both
are identities for the (possibly orientation-reversing) interval integral. -/
lemma integral_comp_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (q : ℝ) (hq : q ≠ 0) (a m₁ m₂ : ℝ) :
    ∫ t in m₁..m₂, f (a + q * t) = q⁻¹ • ∫ x in (a + q * m₁)..(a + q * m₂), f x := by
  rw [intervalIntegral.integral_comp_mul_left (fun y : ℝ => f (a + y)) hq]
  rw [intervalIntegral.integral_comp_add_left]

/-- **The second-order chain rule for the affine reparametrisation `t ↦ a + q t`.**
For `w` of class `C²` and `q ≠ 0`,
`(w ∘ (a + q ·))'' t = q ^ 2 · w'' (a + q t)`
(`q ^ 2` is understood as the real scalar, hence the cast to `ℂ`).

This is `iteratedDeriv_comp_const_smul` for `f = w (a + ·)` at `n = 2`, combined with the
translation invariance `iteratedDeriv_comp_const_add`. -/
lemma iteratedDeriv_two_comp_affine (w : ℝ → ℂ) (hw : ContDiff ℝ 2 w) (a q t : ℝ) :
    iteratedDeriv 2 (fun s => w (a + q * s)) t = ((q ^ 2 : ℝ) : ℂ) * iteratedDeriv 2 w (a + q * t) := by
  have h := iteratedDeriv_comp_const_smul (f := fun y : ℝ => w (a + y))
      (n := 2) (hw.comp (by fun_prop : ContDiff ℝ 2 (fun y : ℝ => a + y))) (q : ℝ)
  have h2 := congrFun h t
  rw [iteratedDeriv_comp_const_add] at h2
  rw [h2]
  norm_num

/-- **The trapezoid comparison on an arithmetic progression of step `q`.**  For a `C²` function `w`
with `‖w‖ ≤ 1` and integers `m₁ ≤ m₂`,
`‖∑_{m=m₁}^{m₂} w(a + q m) − q⁻¹ ∫_{a+q m₁}^{a+q m₂} w‖ ≤ 1 + (q/8) ∫_{a+q m₁}^{a+q m₂} ‖w''‖`.
Proof: apply the already-proved `Work.A7.ModelApproxCore_trapezoid` to `t ↦ w (a + q t)` and use the
substitution rules for interval integrals (`intervalIntegral.integral_comp_mul_left`,
`integral_comp_add_left`) together with the chain rule
`iteratedDeriv 2 (fun t => w (a + q t)) t = q^2 * iteratedDeriv 2 w (a + q t)`. -/
theorem trapezoid_progression (w : ℝ → ℂ) (hw : ContDiff ℝ 2 w) (hw1 : ∀ t, ‖w t‖ ≤ 1)
    (q : ℕ) (hq : 0 < q) (a : ℤ) (m₁ m₂ : ℤ) (hm : m₁ ≤ m₂) :
    ‖(∑ m ∈ Finset.Icc m₁ m₂, w ((a : ℝ) + (q : ℝ) * (m : ℝ)))
        - ((q : ℝ))⁻¹
            * ∫ t in ((a : ℝ) + (q : ℝ) * (m₁ : ℝ))..((a : ℝ) + (q : ℝ) * (m₂ : ℝ)), w t‖
      ≤ 1 + ((q : ℝ) / 8)
          * ∫ t in ((a : ℝ) + (q : ℝ) * (m₁ : ℝ))..((a : ℝ) + (q : ℝ) * (m₂ : ℝ)),
              ‖iteratedDeriv 2 w t‖ := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hcomp : ContDiff ℝ 2 (fun t : ℝ => w ((a : ℝ) + (q : ℝ) * t)) := hw.comp (by fun_prop)
  -- The unit-step comparison applied to `t ↦ w (a + q t)`.
  have hkey := ModelApproxCore_trapezoid (fun t : ℝ => w ((a : ℝ) + (q : ℝ) * t)) hcomp
    (a := m₁) (b := m₂) hm
  -- Reparametrise the integral of `w`.
  have hI1 : (∫ t in (m₁ : ℝ)..(m₂ : ℝ), w ((a : ℝ) + (q : ℝ) * t))
      = ((q : ℝ))⁻¹ * ∫ t in ((a : ℝ) + (q : ℝ) * (m₁ : ℝ))..((a : ℝ) + (q : ℝ) * (m₂ : ℝ)), w t := by
    rw [integral_comp_affine w (q : ℝ) hq0 (a : ℝ) (m₁ : ℝ) (m₂ : ℝ), Complex.real_smul]
  -- Reparametrise the integral of `‖w''‖`, picking up the factor `q ^ 2 · q⁻¹ = q`.
  have hI2 : (∫ t in (m₁ : ℝ)..(m₂ : ℝ),
        ‖iteratedDeriv 2 (fun t : ℝ => w ((a : ℝ) + (q : ℝ) * t)) t‖)
      = (q : ℝ) * ∫ t in ((a : ℝ) + (q : ℝ) * (m₁ : ℝ))..((a : ℝ) + (q : ℝ) * (m₂ : ℝ)),
          ‖iteratedDeriv 2 w t‖ := by
    have hpt : ∀ t : ℝ, ‖iteratedDeriv 2 (fun s : ℝ => w ((a : ℝ) + (q : ℝ) * s)) t‖
        = (q : ℝ) ^ 2 * ‖iteratedDeriv 2 w ((a : ℝ) + (q : ℝ) * t)‖ := by
      intro t
      rw [iteratedDeriv_two_comp_affine w hw (a : ℝ) (q : ℝ) t, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (q : ℝ))]
    rw [intervalIntegral.integral_congr (fun t _ => hpt t), intervalIntegral.integral_const_mul]
    rw [integral_comp_affine (fun x : ℝ => ‖iteratedDeriv 2 w x‖) (q : ℝ) hq0 (a : ℝ) (m₁ : ℝ) (m₂ : ℝ)]
    rw [smul_eq_mul]
    field_simp
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hmR : (m₁ : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm
  have hends : ((a : ℝ) + (q : ℝ) * (m₁ : ℝ)) ≤ ((a : ℝ) + (q : ℝ) * (m₂ : ℝ)) := by
    have : (q : ℝ) * (m₁ : ℝ) ≤ (q : ℝ) * (m₂ : ℝ) := mul_le_mul_of_nonneg_left hmR hqnn
    linarith
  have hI : 0 ≤ ∫ t in ((a : ℝ) + (q : ℝ) * (m₁ : ℝ))..((a : ℝ) + (q : ℝ) * (m₂ : ℝ)),
      ‖iteratedDeriv 2 w t‖ :=
    intervalIntegral.integral_nonneg hends (fun t _ => norm_nonneg _)
  -- The endpoint term is at most `(1/2)(1 + 1) = 1` because `‖w‖ ≤ 1`.
  have hB : (1/2) * (‖w ((a : ℝ) + (q : ℝ) * (m₁ : ℝ))‖ + ‖w ((a : ℝ) + (q : ℝ) * (m₂ : ℝ))‖)
      ≤ 1 := by
    have h1 := hw1 ((a : ℝ) + (q : ℝ) * (m₁ : ℝ))
    have h2 := hw1 ((a : ℝ) + (q : ℝ) * (m₂ : ℝ))
    linarith
  calc ‖(∑ m ∈ Finset.Icc m₁ m₂, w ((a : ℝ) + (q : ℝ) * (m : ℝ)))
        - ((q : ℝ))⁻¹
            * ∫ t in ((a : ℝ) + (q : ℝ) * (m₁ : ℝ))..((a : ℝ) + (q : ℝ) * (m₂ : ℝ)), w t‖
      = ‖(∑ m ∈ Finset.Icc m₁ m₂, w ((a : ℝ) + (q : ℝ) * (m : ℝ)))
        - ∫ t in (m₁ : ℝ)..(m₂ : ℝ), w ((a : ℝ) + (q : ℝ) * t)‖ := by rw [hI1]
    _ ≤ (1/2) * (‖w ((a : ℝ) + (q : ℝ) * (m₁ : ℝ))‖ + ‖w ((a : ℝ) + (q : ℝ) * (m₂ : ℝ))‖)
        + (1/8) * ∫ t in (m₁ : ℝ)..(m₂ : ℝ),
            ‖iteratedDeriv 2 (fun t : ℝ => w ((a : ℝ) + (q : ℝ) * t)) t‖ := hkey
    _ = (1/2) * (‖w ((a : ℝ) + (q : ℝ) * (m₁ : ℝ))‖ + ‖w ((a : ℝ) + (q : ℝ) * (m₂ : ℝ))‖)
        + (1/8) * ((q : ℝ) * ∫ t in ((a : ℝ) + (q : ℝ) * (m₁ : ℝ))..((a : ℝ) + (q : ℝ) * (m₂ : ℝ)),
            ‖iteratedDeriv 2 w t‖) := by rw [hI2]
    _ ≤ 1 + ((q : ℝ) / 8) * ∫ t in ((a : ℝ) + (q : ℝ) * (m₁ : ℝ))..((a : ℝ) + (q : ℝ) * (m₂ : ℝ)),
            ‖iteratedDeriv 2 w t‖ := by
        nlinarith [hB, hI, hqnn]

end Work.A7

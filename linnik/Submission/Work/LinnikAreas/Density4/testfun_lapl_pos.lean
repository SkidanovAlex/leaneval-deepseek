/-
# Area 4 / HB §12 — `F(z) > 0`: positivity of the Laplace transform of the §7 test function

`Work.LinnikAreas.Density4.testfun_lapl_pos` states that for `π/2 < θ < π` and `λ̂ > 0` the Laplace
transform `FT θ λ̂ z = ∫₀^{2γ} e^{-zt} f(t) dt` of Heath-Brown's §7 test function is strictly
positive, for **every** real `z` (both signs of `z`!).  This is what lets §12 apply the test
function to the arguments `-λ₁`, `λ-λ₁` and `0` without any sign restriction on the transform.

## Where the positivity comes from

`f = g ⊛ g` with `g ≥ 0`, `g ≠ 0`, so `f ≥ 0` (`testfun_basic`) and `f` is *strictly* positive
throughout the interior `(0, 2γ)` of its support (this is `gT_pos`: for `|t| < γ` one has
`|ζt| < θ < π`, hence `cos(ζt) > cos θ`).  Since `t ↦ e^{-zt}` is strictly positive for every real
`z`, the integrand `t ↦ e^{-zt} f(t)` is strictly positive on the whole open interval
`(0, 2γ)` and its integral over `0..2γ` is strictly positive
(`intervalIntegral.intervalIntegral_pos_of_pos_on`).

The only non-formal input is the strict positivity of the *closed form* of `f` on `(0,2γ)`, i.e. of

* `W(θ,s) = (2θ-s)(cos s/2 + cos²θ) + sin(2θ-s)/2 - sin 2θ + 2 cosθ sin(s-θ)`.

Two ingredients, both proved in separate modules and imported here:

* `wT_bracket_eq_integral` — `W(θ,s)` is the convolution integral
  `∫_{s-θ}^{θ} (cos v - cos θ)(cos(s-v) - cos θ) dv` (HB §7's computation in the `s = ζx` variable);
* `cos_diff_prod_integral_pos` — that integral is strictly positive when `0 < θ < π` and
  `0 < s < 2θ`.

Since `f`'s support `[0,2γ]` corresponds to `s ∈ [0,2θ]`, and `λ̂²(1+tan²θ)²/ζ > 0`, this gives
`f > 0` on `(0,2γ)`, exactly the strict positivity of the integrand needed above.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.TestFun
import Submission.Work.LinnikAreas.Density4.wT_bracket_eq_integral
import Submission.Work.LinnikAreas.Density4.cos_diff_prod_integral_pos

open MeasureTheory
noncomputable section

namespace Work.LinnikAreas.Density4

/-- The **unclamped** closed form of HB's `f = g ⊛ g`, i.e. the branch expression appearing in the
definition of `fT` (which is the identity only on the support `[0,2γ]`). -/
def fTclosed (θ lam : ℝ) (x : ℝ) : ℝ :=
  lam ^ 2 * (1 + Real.tan θ ^ 2) ^ 2 *
    ( (2 * gammaT θ lam - x) * (Real.cos (zetaT θ lam * x) / 2 + Real.cos θ ^ 2)
      + Real.sin (2 * θ - zetaT θ lam * x) / (2 * zetaT θ lam)
      - Real.sin (2 * θ) / zetaT θ lam
      + 2 * Real.cos θ * Real.sin (zetaT θ lam * x - θ) / zetaT θ lam )

/-- The trig bracket `W(θ,s)` of `fT`'s closed form, normalised so that
`fTclosed θ λ̂ x = λ̂²(1+tan²θ)² W(θ, ζx)/ζ`. -/
def bracketT (θ s : ℝ) : ℝ :=
  (2 * θ - s) * (Real.cos s / 2 + Real.cos θ ^ 2) + Real.sin (2 * θ - s) / 2
    - Real.sin (2 * θ) + 2 * Real.cos θ * Real.sin (s - θ)

/-- `fT` is the clamped closed form `fTclosed`. -/
lemma fT_eq_fTclosed (θ lam x : ℝ) (hx : 0 ≤ x ∧ x ≤ 2 * gammaT θ lam) :
    fT θ lam x = fTclosed θ lam x := by
  unfold fT fTclosed
  rw [if_pos hx]

/-- The unclamped closed form is continuous (it is a polynomial in `cos` and `sin` of `x`). -/
lemma continuous_fTclosed (θ lam : ℝ) : Continuous (fTclosed θ lam) := by
  unfold fTclosed
  fun_prop

/-- The algebraic form of the closed form: `fTclosed θ λ̂ x = λ̂²(1+tan²θ)² · W(θ,ζx)/ζ`. -/
lemma fTclosed_eq_bracketT (θ lam x : ℝ) (hζ : zetaT θ lam ≠ 0) :
    fTclosed θ lam x =
      lam ^ 2 * (1 + Real.tan θ ^ 2) ^ 2 * (bracketT θ (zetaT θ lam * x) / zetaT θ lam) := by
  unfold fTclosed bracketT gammaT
  field_simp

/-- **The bracket `W` is strictly positive** on `0 < s < 2θ` for `0 < θ < π`: it is the convolution
integral of a strictly positive integrand (`wT_bracket_eq_integral` + `cos_diff_prod_integral_pos`). -/
lemma bracketT_pos (θ s : ℝ) (hθ0 : 0 < θ) (hθπ : θ < Real.pi) (hs0 : 0 < s)
    (hs2 : s < 2 * θ) : 0 < bracketT θ s := by
  have h := cos_diff_prod_integral_pos θ s hθ0 hθπ hs0 hs2
  rw [← wT_bracket_eq_integral θ s] at h
  simpa [bracketT] using h

/-- **HB §7: the test function is strictly positive on the interior of its support.**  For
`π/2 < θ < π`, `λ̂ > 0` and `0 < x < 2γ` (equivalently `0 < ζx < 2θ`) the closed form of
`f = g ⊛ g` is strictly positive: `f = g ⊛ g` with `g > 0` on `(-γ,γ)`. -/
lemma fTclosed_pos (θ lam x : ℝ) (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) (hlam : 0 < lam)
    (hx0 : 0 < x) (hx2 : x < 2 * gammaT θ lam) : 0 < fTclosed θ lam x := by
  have hζ := zetaT_pos hθ1 hθ2 hlam
  have hθ0 : 0 < θ := lt_trans (by linarith [Real.pi_pos]) hθ1
  have hs0 : 0 < zetaT θ lam * x := mul_pos hζ hx0
  have hs2 : zetaT θ lam * x < 2 * θ := by
    have h : zetaT θ lam * x < zetaT θ lam * (2 * gammaT θ lam) :=
      mul_lt_mul_of_pos_left hx2 hζ
    have h2 : zetaT θ lam * (2 * gammaT θ lam) = 2 * θ := by
      rw [gammaT]
      field_simp
    linarith
  rw [fTclosed_eq_bracketT θ lam x (ne_of_gt hζ)]
  exact mul_pos (mul_pos (by positivity) (by positivity))
    (div_pos (bracketT_pos θ (zetaT θ lam * x) hθ0 hθ2 hs0 hs2) hζ)

/-- **Positivity of the Laplace transform `F(z) = ∫₀^{2γ} e^{-zt} f(t) dt` of HB's §7 test
function**, for every real `z`: the integrand `t ↦ e^{-zt} f(t)` is strictly positive on
`(0, 2γ)`, since `f > 0` there (`fTclosed_pos`) and `e^{-zt} > 0` always. -/
theorem testfun_lapl_pos (θ lam z : ℝ) (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi)
    (hlam : 0 < lam) : 0 < Work.LinnikAreas.Density4.FT θ lam z := by
  have hγ := gammaT_pos hθ1 hθ2 hlam
  have hL : 0 < 2 * gammaT θ lam := by linarith
  -- the integrand `t ↦ e^{-zt} f(t)` is interval integrable: it agrees on `(0,2γ)` with the
  -- continuous function `t ↦ e^{-zt} fTclosed(t)`
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (-(z * t)) * fT θ lam t) volume 0
      (2 * gammaT θ lam) := by
    have hcont : Continuous (fun t : ℝ => Real.exp (-(z * t)) * fTclosed θ lam t) :=
      (Real.continuous_exp.comp (by fun_prop)).mul (continuous_fTclosed θ lam)
    have h0 : IntervalIntegrable (fun t : ℝ => Real.exp (-(z * t)) * fTclosed θ lam t) volume 0
        (2 * gammaT θ lam) := hcont.intervalIntegrable _ _
    refine h0.congr_uIoo ?_
    intro t ht
    rw [Set.uIoo_of_le hL.le] at ht
    simp only
    rw [fT_eq_fTclosed θ lam t ⟨ht.1.le, ht.2.le⟩]
  -- and strictly positive on the open interval `(0,2γ)`
  have hpos : ∀ t ∈ Set.Ioo (0 : ℝ) (2 * gammaT θ lam),
      0 < Real.exp (-(z * t)) * fT θ lam t := by
    intro t ht
    rw [fT_eq_fTclosed θ lam t ⟨ht.1.le, ht.2.le⟩]
    exact mul_pos (Real.exp_pos _) (fTclosed_pos θ lam t hθ1 hθ2 hlam ht.1 ht.2)
  rw [FT]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on hint hpos hL

end Work.LinnikAreas.Density4

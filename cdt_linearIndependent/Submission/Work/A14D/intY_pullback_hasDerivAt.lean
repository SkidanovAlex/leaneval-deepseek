import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.fourteen_subst_eval_disc
import Submission.Work.C17I.subst_eval_abs
import Submission.Work.C17I.hasSum_tsum_of_coeff_growth
import Submission.Work.C17I.yC_norm_lt_fifth
import Submission.Work.A14D.hasDerivAt_powSeries

/-!
# The chain rule for the pullbacks of the formal integrals `intY`

This module proves `Work.A14D.intY_pullback_hasDerivAt`: the analytic function obtained by
substituting the symmetrisation coordinate `y = x²/(x−1)` (`sympY`) into the formal integral
`intY f` and summing the resulting power series has derivative `dyC z · Σ_k [yᵏ]f · (yC z)ᵏ`,
i.e. `y'(z)` times the pullback of `f` at `z`.

The route is the chain rule for `Ψ ∘ yC`, where `Ψ(ζ) = Σ_k [yᵏ](intY f)·ζᵏ` is the power
series of the primitive — whose derivative is the power series `Σ_k [yᵏ]f·ζᵏ` because
`(k+1)·[y^{k+1}](intY f) = [yᵏ]f` — together with the classical "composition of convergent power
series" identity (`Work.C17I.subst_eval_abs`) which identifies the pullback of `intY f` with
`Ψ ∘ yC` on the disc `‖w‖ ≤ 35/100`.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology BigOperators

/-- The coefficients of `intY f` grow at the same geometric rate as those of `f` (with one extra
factor `R`): `[yᵏ](intY f) = [yᵏ⁻¹]f / k`. -/
private lemma intY_coeff_growth (f : PowerSeries ℚ) {C R : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hf : ∀ k : ℕ, ‖((PowerSeries.coeff k f : ℚ) : ℂ)‖ * R ^ k ≤ C) :
    ∀ k : ℕ, ‖((PowerSeries.coeff k (Submission.CDTPlan.intY f) : ℚ) : ℂ)‖ * R ^ k ≤ C * R := by
  intro k
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have h0 : PowerSeries.coeff 0 (Submission.CDTPlan.intY f) = 0 := by
      simp [Submission.CDTPlan.intY, PowerSeries.coeff_mk]
    rw [h0]
    simp only [Rat.cast_zero, norm_zero, zero_mul]
    positivity
  · have hcoeff : ((PowerSeries.coeff k (Submission.CDTPlan.intY f) : ℚ) : ℂ)
        = ((PowerSeries.coeff (k - 1) f : ℚ) : ℂ) / (k : ℂ) := by
      rw [Submission.CDTPlan.intY, PowerSeries.coeff_mk]
      rw [if_neg (Nat.pos_iff_ne_zero.mp hk)]
      push_cast
      rfl
    rw [hcoeff]
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    rw [norm_div, Complex.norm_natCast]
    have hpow : R ^ k = R * R ^ (k - 1) := by
      conv_lhs => rw [show k = (k - 1) + 1 from by omega]
      rw [pow_succ']
    have hle : ‖((PowerSeries.coeff (k - 1) f : ℚ) : ℂ)‖ ≤ C / R ^ (k - 1) := by
      rw [le_div_iff₀ (pow_pos hR _)]
      exact hf (k - 1)
    calc ‖((PowerSeries.coeff (k - 1) f : ℚ) : ℂ)‖ / (k : ℝ) * R ^ k
        ≤ (C / R ^ (k - 1)) / (k : ℝ) * R ^ k := by gcongr
      _ = C * R / (k : ℝ) := by rw [hpow]; field_simp
      _ ≤ C * R := by
          rw [div_le_iff₀ hkR]
          have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
          nlinarith [mul_pos hC hR]

/-- The pullback of `intY f` is `Ψ ∘ yC` on the disc `‖w‖ ≤ 35/100`, where
`Ψ(ζ) = Σ_k [yᵏ](intY f)·ζᵏ`: this is `Work.C17I.subst_eval_abs` applied to the integral. -/
private lemma intY_subst_eval (f : PowerSeries ℚ) {C R : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hR5 : 1 / 5 < R)
    (hf : ∀ k : ℕ, ‖((PowerSeries.coeff k f : ℚ) : ℂ)‖ * R ^ k ≤ C) :
    ∀ w : ℂ, ‖w‖ ≤ (35 : ℝ) / 100 →
      HasSum (fun k : ℕ =>
          ((PowerSeries.coeff k ((Submission.CDTPlan.intY f).subst Submission.CDT.sympY) : ℚ) : ℂ) * w ^ k)
        (∑' k : ℕ, ((PowerSeries.coeff k (Submission.CDTPlan.intY f) : ℚ) : ℂ) * (Work.C17.yC w) ^ k) := by
  intro w hw
  have hb := intY_coeff_growth f hC hR hf
  have hsum : HasSum (fun k : ℕ =>
      ‖((PowerSeries.coeff k Submission.CDT.sympY : ℚ) : ℂ)‖ * (35 / 100 : ℝ) ^ k)
      (((35 : ℝ) / 100) ^ 2 / (1 - 35 / 100)) :=
    Work.C17I.sympY_norm_hasSum (by norm_num) (by norm_num)
  have hgS := hsum.summable
  have hgR : (∑' k : ℕ,
      ‖((PowerSeries.coeff k Submission.CDT.sympY : ℚ) : ℂ)‖ * (35 / 100 : ℝ) ^ k) < R := by
    rw [hsum.tsum_eq]
    exact lt_of_lt_of_le (by norm_num) (le_of_lt hR5)
  have hg0 : PowerSeries.constantCoeff Submission.CDT.sympY = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Submission.CDT.coeff_sympY_zero
  have hkey := Work.C17I.subst_eval_abs (f := Submission.CDTPlan.intY f)
      (g := Submission.CDT.sympY) (C := C * R) (R := R) (ρ := 35 / 100) (z := w)
      (le_of_lt (mul_pos hC hR)) (by norm_num) hR hg0 hb hgS hgR hw
  have hw1 : ‖w‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have hsymp : (∑' m : ℕ, ((PowerSeries.coeff m Submission.CDT.sympY : ℚ) : ℂ) * w ^ m)
      = Work.C17.yC w := by
    rw [(Work.C17I.sympY_hasSum w hw1).tsum_eq]
  rw [hsymp] at hkey
  exact hkey

/-- The power series of the primitive has the power series of `f` as its derivative:
`Ψ = Σ_k [yᵏ](intY f)·ζᵏ` is differentiable on `‖ζ‖ < R` with
`Ψ'(ζ) = Σ_k [yᵏ]f·ζᵏ`. -/
private lemma intY_series_hasDerivAt (f : PowerSeries ℚ) {C R : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hf : ∀ k : ℕ, ‖((PowerSeries.coeff k f : ℚ) : ℂ)‖ * R ^ k ≤ C) :
    ∀ ζ : ℂ, ‖ζ‖ < R →
      HasDerivAt (fun ζ : ℂ =>
          ∑' k : ℕ, ((PowerSeries.coeff k (Submission.CDTPlan.intY f) : ℚ) : ℂ) * ζ ^ k)
        (∑' k : ℕ, ((PowerSeries.coeff k f : ℚ) : ℂ) * ζ ^ k) ζ := by
  intro ζ hζ
  have hb := intY_coeff_growth f hC hR hf
  -- the primitive's series converges on `‖ζ‖ < R`
  have hconv : ∀ z : ℂ, ‖z‖ < R →
      HasSum (fun k : ℕ =>
          ((PowerSeries.coeff k (Submission.CDTPlan.intY f) : ℚ) : ℂ) * z ^ k)
        (∑' k : ℕ, ((PowerSeries.coeff k (Submission.CDTPlan.intY f) : ℚ) : ℂ) * z ^ k) := by
    intro z hz
    refine Work.C17I.hasSum_tsum_of_coeff_growth (le_of_lt (mul_pos hC hR)) (inv_pos.mpr hR)
      (fun n => ?_) z ?_
    · have h1 : ‖((PowerSeries.coeff n (Submission.CDTPlan.intY f) : ℚ) : ℂ)‖
          ≤ (C * R) / R ^ n := by
        rw [le_div_iff₀ (pow_pos hR n)]; exact hb n
      calc ‖((PowerSeries.coeff n (Submission.CDTPlan.intY f) : ℚ) : ℂ)‖
          ≤ (C * R) / R ^ n := h1
        _ = (C * R) * (R⁻¹) ^ n := by rw [inv_pow, div_eq_mul_inv]
    · simp only [one_div, inv_inv]; exact hz
  -- differentiate the primitive's series term by term
  have hderiv := hasDerivAt_powSeries
    (fun k => ((PowerSeries.coeff k (Submission.CDTPlan.intY f) : ℚ) : ℂ)) hR
    (fun z : ℂ => ∑' k : ℕ,
      ((PowerSeries.coeff k (Submission.CDTPlan.intY f) : ℚ) : ℂ) * z ^ k) hconv ζ hζ
  -- `(k+1)·[y^{k+1}](intY f) = [yᵏ]f`
  have hval : (∑' n : ℕ, ((n : ℂ) + 1)
        * ((PowerSeries.coeff (n + 1) (Submission.CDTPlan.intY f) : ℚ) : ℂ) * ζ ^ n)
      = ∑' k : ℕ, ((PowerSeries.coeff k f : ℚ) : ℂ) * ζ ^ k := by
    refine tsum_congr fun n => ?_
    have hc : PowerSeries.coeff (n + 1) (Submission.CDTPlan.intY f)
        = PowerSeries.coeff n f / ((n + 1 : ℕ) : ℚ) := by
      rw [Submission.CDTPlan.intY, PowerSeries.coeff_mk, if_neg (by omega)]
      simp
    rw [hc]
    push_cast
    field_simp
  rw [hval] at hderiv
  exact hderiv

/-- The derivative of `yC` at a point different from `1` is `dyC`. -/
private lemma hasDerivAt_yC' (z : ℂ) (hz1 : z ≠ 1) :
    HasDerivAt yC (dyC z) z := by
  have h1 : HasDerivAt (fun w : ℂ => w ^ 2) (2 * z) z := by simpa using hasDerivAt_pow 2 z
  have h2 : HasDerivAt (fun w : ℂ => w - 1) 1 z := (hasDerivAt_id z).sub_const 1
  have h3 : HasDerivAt (fun w : ℂ => w ^ 2 / (w - 1))
      ((2 * z * (z - 1) - z ^ 2 * 1) / (z - 1) ^ 2) z :=
    h1.div h2 (by simpa using sub_ne_zero.mpr hz1)
  have heq : (2 * z * (z - 1) - z ^ 2 * 1) / (z - 1) ^ 2 = dyC z := by
    rw [dyC]; ring
  rw [heq] at h3
  exact h3

/-- Chain rule for the pullbacks of the formal integrals `intY`: for a `y`-series `f` whose
coefficients satisfy `‖[yᵏ]f‖ · Rᵏ ≤ C` with `1/5 < R` (so that the substitution estimates apply on
the disc `‖w‖ ≤ 34/100`, exactly as in `Work.A14D.fourteen_subst_eval_disc`), the *pullback* of
`intY f` (the analytic function `w ↦ Σ' k [xᵏ]((intY f).subst sympY)·wᵏ`) has derivative
`y'(z) · (the pullback of f at z) = dyC z · Σ' k [yᵏ]f · (yC z)ᵏ`.

Route: `PowerSeries.derivative (R := ℚ) (intY f) = f` (immediate from `intY`'s definition
`[yⁿ](intY f) = [yⁿ⁻¹]f / n`), so the chain rule `PowerSeries.derivative_subst` gives
`derivative ((intY f).subst sympY) = (f.subst sympY) * derivative sympY`; the derivative of a power
series is evaluated term by term (`Work.C17I.hasSum_tsum_of_coeff_growth`), the Cauchy product of
the two convergent series is evaluated at `yC z` (`Work.C17I.subst_eval_abs` for `f`, and
`Work.C17I.sympY_hasSum` together with the derivative of `sympY` for the second factor), yielding
the stated derivative.  This is what lets the three integral slots be handled by
primitive-existence on convex sets (`Work.C17g.linear_ode_convex`), exactly as the four `G`-slots
are handled by `∂_y` and `Work.C17I.DyIter_comp_yC`. -/
theorem intY_pullback_hasDerivAt (f : PowerSeries ℚ) {C R : ℝ} (hC : 0 < C) (hR : 0 < R)
    (hR5 : 1 / 5 < R) (hR1 : R ≤ 1)
    (hf : ∀ k : ℕ, ‖((PowerSeries.coeff k f : ℚ) : ℂ)‖ * R ^ k ≤ C) :
    ∀ z : ℂ, ‖z‖ ≤ (34 : ℝ) / 100 →
      HasDerivAt (fun w : ℂ => ∑' k : ℕ,
          ((PowerSeries.coeff k ((Submission.CDTPlan.intY f).subst Submission.CDT.sympY) : ℚ) : ℂ) * w ^ k)
        (dyC z * (∑' k : ℕ, ((PowerSeries.coeff k f : ℚ) : ℂ) * (yC z) ^ k)) z := by
  intro z hz
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hz
    norm_num at hz
  -- `‖yC z‖ < 1/5 < R`, so the primitive's power series is differentiable at `yC z`
  have hyz : ‖yC z‖ < R := lt_trans (Work.C17I.yC_norm_lt_fifth z hz) hR5
  have hD := intY_series_hasDerivAt f hC hR hf (yC z) hyz
  have hyCd : HasDerivAt yC (dyC z) z := hasDerivAt_yC' z hz1
  have hchain := hD.comp z hyCd
  -- the pullback equals `Ψ ∘ yC` on `‖w‖ ≤ 35/100`, a neighbourhood of `z`
  have hev : (fun w : ℂ => ∑' k : ℕ,
        ((PowerSeries.coeff k ((Submission.CDTPlan.intY f).subst Submission.CDT.sympY) : ℚ) : ℂ) * w ^ k)
      =ᶠ[𝓝 z] (fun w : ℂ => ∑' k : ℕ,
        ((PowerSeries.coeff k (Submission.CDTPlan.intY f) : ℚ) : ℂ) * (yC w) ^ k) := by
    have hball : z ∈ Metric.ball (0 : ℂ) ((35 : ℝ) / 100) := by
      rw [Metric.mem_ball, dist_zero_right]; linarith
    filter_upwards [Metric.isOpen_ball.mem_nhds hball] with w hw
    have hw' : ‖w‖ ≤ (35 : ℝ) / 100 := le_of_lt (by
      rwa [Metric.mem_ball, dist_zero_right] at hw)
    exact (intY_subst_eval f hC hR hR5 hf w hw').tsum_eq
  have hfin := hchain.congr_of_eventuallyEq hev
  have hval : (∑' k : ℕ, ((PowerSeries.coeff k f : ℚ) : ℂ) * (yC z) ^ k) * dyC z
      = dyC z * (∑' k : ℕ, ((PowerSeries.coeff k f : ℚ) : ℂ) * (yC z) ^ k) := mul_comm _ _
  rw [hval] at hfin
  exact hfin

end Work.A14D

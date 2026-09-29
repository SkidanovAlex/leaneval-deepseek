import Mathlib
import Submission.Work.C17.logP_defs

/-!
# `Pfun = κ·(Σ Fₙzⁿ) + Σ Kₙzⁿ` on the disc of radius `xs`

The unlikely series `P = logP a b ra rb rab r0` has coefficients
`cₙ = κ·Fₙ + Kₙ` (`Work.C17.logPCoeffQ_eq_kap_Ffun_add_Kfun`).  Here we convert that
*coefficient* statement into the corresponding statement about the functions, i.e. we
split the power series `Pfun` on the disc `‖z‖ < xs a b` using the two growth
hypotheses: `F` grows like `(1/xs)ⁿ` (a cusp) and `K` like `xsⁿ` (an overconvergent
remainder).  Both are dominated by polynomial × geometric series, so both terms are
summable on that disc and the `tsum` splits.
-/

namespace Work.C17

open scoped BigOperators

noncomputable section

/-- `∑ ((n+1)^k r^n)` converges for `‖r‖ < 1`: expand `(n+1)^k` by the binomial
theorem and use `Summable (fun n => (n : ℝ)^j * r ^ n)`. -/
lemma summable_one_add_pow_mul_geom (k : ℕ) {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * r ^ n) := by
  have hb : ∀ n : ℕ, ((n : ℝ) + 1) ^ k * r ^ n
      = ∑ j ∈ Finset.range (k + 1), ((k.choose j : ℝ) * ((n : ℝ) ^ j * r ^ n)) := by
    intro n
    rw [add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [one_pow, mul_one]
    ring
  refine (summable_sum ?_).congr (fun n => (hb n).symm)
  intro j hj
  exact (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) j hr).mul_left _

/-- If the norms of `f n` grow at most like `C·(n+1)^k·θⁿ`, then the power series
`Σ f n zⁿ` converges for `θ·‖z‖ < 1`.  (No sign condition on `C` is needed.) -/
lemma summable_of_norm_le_poly_geom (k : ℕ) {C θ : ℝ} (hθ : 0 ≤ θ)
    (f : ℕ → ℂ) (hf : ∀ n : ℕ, ‖f n‖ ≤ C * ((n : ℝ) + 1) ^ k * θ ^ n)
    {z : ℂ} (hz : θ * ‖z‖ < 1) : Summable (fun n : ℕ => f n * z ^ n) := by
  have hr0 : 0 ≤ θ * ‖z‖ := mul_nonneg hθ (norm_nonneg z)
  have hgnorm : ‖θ * ‖z‖‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hz
  have hg : Summable (fun n : ℕ => C * (((n : ℝ) + 1) ^ k * (θ * ‖z‖) ^ n)) :=
    (summable_one_add_pow_mul_geom k hgnorm).mul_left C
  refine Summable.of_norm_bounded hg fun n => ?_
  calc ‖f n * z ^ n‖ = ‖f n‖ * ‖z‖ ^ n := by rw [norm_mul, norm_pow]
    _ ≤ (C * ((n : ℝ) + 1) ^ k * θ ^ n) * ‖z‖ ^ n :=
        mul_le_mul_of_nonneg_right (hf n) (by positivity)
    _ = C * (((n : ℝ) + 1) ^ k * (θ * ‖z‖) ^ n) := by rw [mul_pow]; ring

/-- **Splitting the unlikely series.**  On the disc `‖z‖ < xs a b` of its radius of
convergence, `P = Σ cₙzⁿ` is `κ` times the cusp-type series `Σ Fₙzⁿ` plus the
overconvergent remainder `Σ Kₙzⁿ`. -/
theorem Pfun_eq_kap_Fsum_add_Ksum (a b : ℚ) (ra rb rab r0 : ℤ)
    (hrel : (ra : ℝ) * Submission.CDT.beukersEta (a : ℝ)
        + (rb : ℝ) * Submission.CDT.beukersEta (b : ℝ)
        + (rab : ℝ) * (Submission.CDT.beukersEta (a : ℝ) * Submission.CDT.beukersEta (b : ℝ))
        = (r0 : ℝ))
    (hxs : 0 < xs a b) (hxs1 : xs a b < 1) (C₁ C₂ : ℝ)
    (hF : ∀ n : ℕ, ‖(Ffun a b n : ℂ)‖ ≤ C₁ * ((n : ℝ) + 1) ^ 3 * (1 / (xs a b)) ^ n)
    (hK : ∀ n : ℕ, ‖(Kfun a b ra rb rab n : ℂ)‖ ≤ C₂ * ((n : ℝ) + 1) ^ 4 * (xs a b) ^ n)
    {z : ℂ} (hz : ‖z‖ < xs a b) :
    Pfun a b ra rb rab r0 z
      = (kap a b ra rab : ℂ) * (∑' n : ℕ, (Ffun a b n : ℂ) * z ^ n)
        + ∑' n : ℕ, (Kfun a b ra rb rab n : ℂ) * z ^ n := by
  -- the coefficient identity, cast to `ℂ`
  have hcoeff : ∀ n : ℕ,
      ((PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℂ)
        = (kap a b ra rab : ℂ) * (Ffun a b n : ℂ) + (Kfun a b ra rb rab n : ℂ) := by
    intro n
    rw [Submission.CDT.logP, PowerSeries.coeff_mk]
    have h := logPCoeffQ_eq_kap_Ffun_add_Kfun a b ra rb rab r0 hrel n
    have h' := congrArg (fun x : ℝ => (x : ℂ)) h
    rw [Complex.ofReal_add, Complex.ofReal_mul] at h'
    simpa [Complex.ofReal_ratCast] using h'
  -- convergence of the two pieces on the disc `‖z‖ < xs`
  have hθF : (1 / xs a b) * ‖z‖ < 1 := by
    rw [one_div_mul_eq_div]
    exact (div_lt_one hxs).mpr hz
  have hθK : xs a b * ‖z‖ < 1 := by
    have h1 : xs a b * ‖z‖ < xs a b * 1 := mul_lt_mul_of_pos_left (lt_trans hz hxs1) hxs
    linarith
  have hsumF : Summable (fun n : ℕ => (Ffun a b n : ℂ) * z ^ n) :=
    summable_of_norm_le_poly_geom (k := 3) (C := C₁) (θ := 1 / xs a b)
      (by positivity) (fun n => (Ffun a b n : ℂ)) hF hθF
  have hsumK : Summable (fun n : ℕ => (Kfun a b ra rb rab n : ℂ) * z ^ n) :=
    summable_of_norm_le_poly_geom (k := 4) (C := C₂) (θ := xs a b)
      hxs.le (fun n => (Kfun a b ra rb rab n : ℂ)) hK hθK
  -- the series `Pfun` itself, with the coefficient identity substituted
  rw [Pfun]
  rw [show (∑' n : ℕ,
        (↑(PowerSeries.coeff n (Submission.CDT.logP a b ra rb rab r0) : ℚ) : ℂ) * z ^ n)
      = ∑' n : ℕ,
        ((kap a b ra rab : ℂ) * ((Ffun a b n : ℂ) * z ^ n)
          + (Kfun a b ra rb rab n : ℂ) * z ^ n) from
    tsum_congr fun n => by rw [hcoeff n]; ring]
  rw [Summable.tsum_add (hsumF.mul_left _) hsumK, tsum_mul_left]

end

end Work.C17

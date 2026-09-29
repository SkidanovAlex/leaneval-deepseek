import Mathlib
import Submission.Work.CPull.defs
import Submission.Work.CPull.evp_subst
import Submission.Work.CPull.evp_add_mul
import Submission.Work.CPull.evp_sympPhi
import Submission.Work.C7.g_form
import Submission.Work.C7.evA_Lps
import Submission.Work.CPull.norm_coeff_B3_le

/-!
# Area CPull — the analytic value of `B₃` along `y = x²/(x−1)` at a small point

We prove the requested identity

```
HasSum (fun n => [yⁿ]B₃ · (x²/(x−1))ⁿ) (−(1/2)·log(1−x)²)        (‖x‖ < 1/2).
```

The route is the evaluation bridge `Work.CPull.evp_subst`, the coefficient bound
`Work.CPull.norm_coeff_B3_le`, the pullback identity `Work.C7.g_form`
(`B₃ ∘ y = −L²/2` with `L = log(1−x)`, `y = x²/(x−1)`) and the Taylor series of
`log(1−x)` (`Work.C7.hasSum_Lps`):

`evp B₃ (x²/(x−1)) = evp (B₃ ∘ y) x = evp (−L²/2) x = −(1/2)·(log(1−x))²`.

Since `‖x‖ < 1/2` gives `‖x²/(x−1)‖ < 1/2`, all the series converge absolutely. The
coefficients of `B₃` decay like `2·(1/4)ⁿ` and the ℓ¹ mass of `y` at `x` is `< 4`, which is
exactly what `evp_subst` needs.
-/

namespace Work.CPull

open PowerSeries

/-- Evaluation is compatible with negation (no summability needed: `tsum_neg` is unconditional). -/
lemma evp_neg (f : PowerSeries ℚ) (z : ℂ) : evp (-f) z = -evp f z := by
  rw [evp, evp]
  have h : (fun n => ((PowerSeries.coeff n (-f) : ℚ) : ℂ) * z ^ n)
      = fun n => -(((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n) := by
    funext n; rw [map_neg]; push_cast; ring
  rw [h, tsum_neg]

/-- Evaluation is compatible with multiplication by a constant series. -/
lemma evp_C_mul (c : ℚ) (f : PowerSeries ℚ) (z : ℂ) :
    evp (PowerSeries.C c * f) z = (c : ℂ) * evp f z := by
  rw [evp, evp]
  have h : (fun n => ((PowerSeries.coeff n (PowerSeries.C c * f) : ℚ) : ℂ) * z ^ n)
      = fun n => (c : ℂ) * (((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n) := by
    funext n; rw [PowerSeries.coeff_C_mul]; push_cast; ring
  rw [h, tsum_mul_left]

theorem hasSum_coeff_B3_yps (x : ℂ) (hx : ‖x‖ < 1 / 2) :
    HasSum (fun n : ℕ => ((PowerSeries.coeff n Submission.CDTPlan.B3 : ℚ) : ℂ) * (x ^ 2 / (x - 1)) ^ n)
      (-(1 / 2 : ℂ) * (Complex.log (1 - x)) ^ 2) := by
  have hx1 : ‖x‖ < 1 := by linarith
  -- `‖x²/(x−1)‖ < 1/2`
  have hz : ‖x ^ 2 / (x - 1)‖ < 1 / 2 := by
    have hxm1 : (1:ℝ)/2 < ‖x - 1‖ := by
      have h := abs_norm_sub_norm_le (1:ℂ) x
      rw [norm_one, ← norm_sub_rev x (1:ℂ)] at h
      have h2 := (abs_le.mp h).2
      linarith
    rw [norm_div, norm_pow]
    rw [div_lt_iff₀ (by linarith : (0:ℝ) < ‖x - 1‖)]
    nlinarith [norm_nonneg x, norm_nonneg (x-1)]
  -- `y = x²/(x−1)` has zero constant coefficient
  have hb0 : PowerSeries.constantCoeff Submission.CDT.sympY = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff]
    rw [Work.CPull.coeff_sympY_eq]; simp
  -- summability of the coefficient series of `y` at `x`
  have hgeom : Summable fun j : ℕ => ‖x‖ ^ j :=
    summable_geometric_of_norm_lt_one (by simpa using hx1 : ‖‖x‖‖ < 1)
  have hb : Summable fun j : ℕ => ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖x‖ ^ j := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hgeom
    rw [Work.CPull.coeff_sympY_eq j]
    split_ifs <;> simp
  -- its ℓ¹ mass `S` is `< 4`
  set S : ℝ := ∑' j : ℕ, ‖((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ)‖ * ‖x‖ ^ j with hSdef
  have hS4 : S < 4 := by
    have hle : S ≤ (∑' j : ℕ, ‖x‖ ^ j) := by
      rw [hSdef]
      refine Summable.tsum_le_tsum (fun j => ?_) hb hgeom
      rw [Work.CPull.coeff_sympY_eq j]
      split_ifs <;> simp
    have hval : (∑' j : ℕ, ‖x‖ ^ j) = (1 - ‖x‖)⁻¹ :=
      tsum_geometric_of_norm_lt_one (by simpa using hx1 : ‖‖x‖‖ < 1)
    have hinv : (1 - ‖x‖)⁻¹ < 4 := by
      rw [inv_lt_iff_one_lt_mul₀ (by linarith : (0:ℝ) < 1 - ‖x‖)]
      nlinarith [norm_nonneg x]
    linarith
  -- summability of the coefficient series of `B₃`, weighted by the mass of `y`
  have hf : Summable fun n : ℕ => ‖((PowerSeries.coeff n Submission.CDTPlan.B3 : ℚ) : ℂ)‖ * S ^ n := by
    have hSnn : 0 ≤ S := by rw [hSdef]; exact tsum_nonneg (fun j => by positivity)
    have h34 : S / 4 < 1 := by linarith
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_geometric_of_lt_one (by positivity : (0:ℝ) ≤ S / 4) h34).mul_left (2:ℝ))
    have h1 : ‖((PowerSeries.coeff n Submission.CDTPlan.B3 : ℚ) : ℂ)‖ ≤ 2 * (1/4:ℝ)^n :=
      norm_coeff_B3_le n
    have h2 : (0:ℝ) ≤ S ^ n := by positivity
    calc ‖((PowerSeries.coeff n Submission.CDTPlan.B3 : ℚ) : ℂ)‖ * S ^ n
        ≤ (2 * (1/4:ℝ)^n) * S ^ n := mul_le_mul_of_nonneg_right h1 h2
      _ = 2 * (S / 4) ^ n := by
          rw [mul_assoc, ← mul_pow]; ring
  -- `evp_subst`: evaluate `B₃ ∘ y` at `x` by evaluating `B₃` at `y(x)`
  have hsub := evp_subst Submission.CDTPlan.B3 Submission.CDT.sympY x hb0 hb hf
  have hsym : evp Submission.CDT.sympY x = x ^ 2 / (x - 1) := (evp_sympPhi x hx1).2
  have e1 : evp (Submission.CDTPlan.B3.subst Submission.CDT.sympY) x
      = evp Submission.CDTPlan.B3 (x ^ 2 / (x - 1)) := by
    rw [hsub.2, hsym]
  -- the pullback identity `B₃ ∘ y = −L²/2`
  have hg2 : Work.C7.g 2 = Submission.CDTPlan.B3.subst Work.C7.yps := by
    simp [Work.C7.g, Submission.CDTPlan.pureB]
  have hB3eq : Submission.CDTPlan.B3.subst Submission.CDT.sympY
      = -(PowerSeries.C (1/2:ℚ)) * (Work.C7.Lps * Work.C7.Lps) := by
    have h := Work.C7.g_form.2.1
    rw [hg2] at h
    rw [h, pow_two]
  -- the Taylor series of `log(1−x)` and its square
  have hLps : HasSum (fun n => ((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℂ) * x ^ n) (Complex.log (1 - x)) :=
    Work.C7.hasSum_Lps hx1
  have hLpsn : Summable fun n => ‖((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℂ) * x ^ n‖ := hLps.summable.norm
  have hmulLps := evpMul Work.C7.Lps Work.C7.Lps x hLpsn hLpsn
  have hLpsval : evp Work.C7.Lps x = Complex.log (1 - x) := hLps.tsum_eq
  -- the value of `evp B₃` at `x²/(x−1)`
  have hval : evp Submission.CDTPlan.B3 (x ^ 2 / (x - 1)) = -(1/2:ℂ) * (Complex.log (1 - x))^2 := by
    rw [← e1, hB3eq]
    rw [show -(PowerSeries.C (1/2:ℚ)) * (Work.C7.Lps * Work.C7.Lps)
        = -(PowerSeries.C (1/2:ℚ) * (Work.C7.Lps * Work.C7.Lps)) by ring]
    rw [evp_neg, evp_C_mul, hmulLps.2.2.2, hLpsval]
    ring
  -- summability of the coefficient series of `B₃` at `x²/(x−1)`
  have hsumm : Summable
      (fun n : ℕ => ((PowerSeries.coeff n Submission.CDTPlan.B3 : ℚ) : ℂ) * (x ^ 2 / (x - 1)) ^ n) := by
    have h34 : ‖x ^ 2 / (x - 1)‖ / 4 < 1 := by linarith [norm_nonneg (x ^ 2 / (x - 1))]
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one (by positivity : (0:ℝ) ≤ ‖x ^ 2 / (x - 1)‖ / 4) h34).mul_left (2:ℝ))
    rw [norm_mul, norm_pow]
    calc ‖((PowerSeries.coeff n Submission.CDTPlan.B3 : ℚ) : ℂ)‖ * ‖x ^ 2 / (x - 1)‖ ^ n
        ≤ (2 * (1/4:ℝ)^n) * ‖x ^ 2 / (x - 1)‖ ^ n :=
          mul_le_mul_of_nonneg_right (norm_coeff_B3_le n) (by positivity)
      _ = 2 * (‖x ^ 2 / (x - 1)‖ / 4) ^ n := by
          rw [mul_assoc, ← mul_pow]; ring
  have hval' : (∑' n : ℕ, ((PowerSeries.coeff n Submission.CDTPlan.B3 : ℚ) : ℂ) * (x ^ 2 / (x - 1)) ^ n)
      = -(1 / 2 : ℂ) * (Complex.log (1 - x)) ^ 2 := by
    show evp Submission.CDTPlan.B3 (x ^ 2 / (x - 1)) = _
    exact hval
  simpa only [hval'] using hsumm.hasSum

end Work.CPull

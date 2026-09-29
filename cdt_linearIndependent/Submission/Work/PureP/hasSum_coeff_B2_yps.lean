import Mathlib
import Submission.Work.CPull.hasSum_coeff_B3_yps
import Submission.Work.C7.g_form
import Submission.Work.CPull.defs
import Submission.Work.CPull.B2_coeff_bound

namespace Work.PureP

/-! Analytic value of the pure function `B₂` along `y = x²/(x-1)` at a small point.

The route is exactly the one used for `B₃` in `Work.CPull.hasSum_coeff_B3_yps`: the evaluation
bridge `Work.CPull.evp_subst`, the coefficient bound `Work.CPull.B2_coeff_bound`, the pullback
identity `Work.C7.g_form.1` (`B₂ ∘ y = 2y − c·L` with `c = cfun = x − φ = x(x−2)/(x−1)` and
`L = Lps = log(1−x)`), and the Taylor series of `log(1−x)` (`Work.C7.hasSum_Lps`).  The only new
ingredient is the analytic evaluation of the rational series `cfun` on the unit disc,
`evp cfun z = z(z−2)/(z−1)`, which follows from `cfun = X − sympPhi` and `evp sympPhi z = z/(z−1)`
(`Work.CPull.evp_sympPhi`).
-/

open PowerSeries

noncomputable section

/-- Evaluation is compatible with subtraction. -/
lemma evp_sub_cfun (f g : PowerSeries ℚ) (z : ℂ)
    (hf : Summable fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n)
    (hg : Summable fun n : ℕ => ((PowerSeries.coeff n g : ℚ) : ℂ) * z ^ n) :
    Work.CPull.evp (f - g) z = Work.CPull.evp f z - Work.CPull.evp g z := by
  rw [Work.CPull.evp, Work.CPull.evp, Work.CPull.evp]
  have h : (fun n : ℕ => ((PowerSeries.coeff n (f - g) : ℚ) : ℂ) * z ^ n)
      = fun n : ℕ => ((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n
          - ((PowerSeries.coeff n g : ℚ) : ℂ) * z ^ n := by
    funext n
    rw [map_sub]
    push_cast
    ring
  rw [h, Summable.tsum_sub hf hg]

/-- The coefficients of `cfun = x(x−2)/(x−1) = X − φ` are bounded by `2`. -/
lemma norm_coeff_cfun_le (n : ℕ) :
    ‖((PowerSeries.coeff n Work.C7.cfun : ℚ) : ℂ)‖ ≤ 2 := by
  have hc : ((PowerSeries.coeff n Work.C7.cfun : ℚ) : ℂ)
      = (((if n = 1 then (1 : ℚ) else 0) - (if n = 0 then (0 : ℚ) else -1) : ℚ) : ℂ) := by
    rw [Work.C7.cfun_eq_sympW, Work.C7.sympW_eq_X_sub_phi, map_sub,
      PowerSeries.coeff_X, Work.CPull.coeff_sympPhi_eq n]
  rw [hc]
  split_ifs <;> norm_num

/-- The analytic evaluation of the rational series `cfun` on the unit disc. -/
lemma evp_cfun (z : ℂ) (hz : ‖z‖ < 1) :
    Work.CPull.evp Work.C7.cfun z = z * (z - 2) / (z - 1) := by
  have hz1 : z ≠ 1 := by rintro rfl; simp at hz
  have hgeom : Summable fun j : ℕ => ‖z‖ ^ j :=
    summable_geometric_of_norm_lt_one (by simpa using hz : ‖(‖z‖ : ℝ)‖ < 1)
  have hXsumm : Summable fun n : ℕ =>
      ((PowerSeries.coeff n (PowerSeries.X : PowerSeries ℚ) : ℚ) : ℂ) * z ^ n := by
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hgeom
    rw [norm_mul, norm_pow, PowerSeries.coeff_X]
    split_ifs <;> simp
  have hPhisumm : Summable fun n : ℕ =>
      ((PowerSeries.coeff n Submission.CDT.sympPhi : ℚ) : ℂ) * z ^ n := by
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hgeom
    rw [norm_mul, norm_pow, Work.CPull.coeff_sympPhi_eq n]
    split_ifs <;> simp
  rw [Work.C7.cfun_eq_sympW, Work.C7.sympW_eq_X_sub_phi,
    evp_sub_cfun _ _ z hXsumm hPhisumm, Work.CPull.evp_X, (Work.CPull.evp_sympPhi z hz).1]
  field_simp
  ring

theorem hasSum_coeff_B2_yps (x : ℂ) (hx : ‖x‖ < 1 / 2) :
    HasSum (fun n : ℕ =>
        ((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ) * (x ^ 2 / (x - 1)) ^ n)
      (2 * (x ^ 2 / (x - 1)) - x * (x - 2) * Complex.log (1 - x) / (x - 1)) := by
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
  -- summability of the coefficient series of `B₂`, weighted by the mass of `y`
  have hf : Summable fun n : ℕ => ‖((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ)‖ * S ^ n := by
    have hSnn : 0 ≤ S := by rw [hSdef]; exact tsum_nonneg (fun j => by positivity)
    have h34 : S / 4 < 1 := by linarith
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_geometric_of_lt_one (by positivity : (0:ℝ) ≤ S / 4) h34).mul_left (3:ℝ))
    have h1 : ‖((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ)‖ ≤ 3 * (1/4:ℝ)^n :=
      Work.CPull.B2_coeff_bound n
    have h2 : (0:ℝ) ≤ S ^ n := by positivity
    calc ‖((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ)‖ * S ^ n
        ≤ (3 * (1/4:ℝ)^n) * S ^ n := mul_le_mul_of_nonneg_right h1 h2
      _ = 3 * (S / 4) ^ n := by
          rw [mul_assoc, ← mul_pow]; ring
  -- `evp_subst`: evaluate `B₂ ∘ y` at `x` by evaluating `B₂` at `y(x)`
  have hsub := Work.CPull.evp_subst Submission.CDTPlan.B2 Submission.CDT.sympY x hb0 hb hf
  have hsym : Work.CPull.evp Submission.CDT.sympY x = x ^ 2 / (x - 1) :=
    (Work.CPull.evp_sympPhi x hx1).2
  have e1 : Work.CPull.evp (Submission.CDTPlan.B2.subst Submission.CDT.sympY) x
      = Work.CPull.evp Submission.CDTPlan.B2 (x ^ 2 / (x - 1)) := by
    rw [hsub.2, hsym]
  -- the pullback identity `B₂ ∘ y = 2y − c·L`
  have hB2eq : Submission.CDTPlan.B2.subst Submission.CDT.sympY
      = 2 * Work.C7.yps - Work.C7.cfun * Work.C7.Lps := by
    have h := Work.C7.g_form.1
    have hg1 : Work.C7.g 1 = Submission.CDTPlan.B2.subst Work.C7.yps := by
      simp [Work.C7.g, Submission.CDTPlan.pureB]
    rw [hg1] at h
    exact h
  -- the Taylor series of `log(1−x)`
  have hLps : HasSum (fun n : ℕ => ((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℂ) * x ^ n)
      (Complex.log (1 - x)) := Work.C7.hasSum_Lps hx1
  have hLpsn : Summable fun n : ℕ => ‖((PowerSeries.coeff n Work.C7.Lps : ℚ) : ℂ) * x ^ n‖ :=
    hLps.summable.norm
  have hLpsval : Work.CPull.evp Work.C7.Lps x = Complex.log (1 - x) := hLps.tsum_eq
  -- summability of the coefficient series of `y` and of `cfun` at `x`
  have hypsn : Summable fun j : ℕ => ((PowerSeries.coeff j Submission.CDT.sympY : ℚ) : ℂ) * x ^ j :=
    (hb.congr (fun j => by rw [norm_mul, norm_pow])).of_norm
  have hcfunn : Summable fun n : ℕ => ‖((PowerSeries.coeff n Work.C7.cfun : ℚ) : ℂ) * x ^ n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hgeom.mul_left 2)
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (norm_coeff_cfun_le n) (by positivity)
  have hcfunn' : Summable fun n : ℕ => ((PowerSeries.coeff n Work.C7.cfun : ℚ) : ℂ) * x ^ n :=
    hcfunn.of_norm
  have hcfunval : Work.CPull.evp Work.C7.cfun x = x * (x - 2) / (x - 1) := evp_cfun x hx1
  -- the product `c·L` and the term `2y`
  have hmul := Work.CPull.evpMul Work.C7.cfun Work.C7.Lps x hcfunn hLpsn
  have hmulval : Work.CPull.evp (Work.C7.cfun * Work.C7.Lps) x
      = x * (x - 2) / (x - 1) * Complex.log (1 - x) := by
    rw [hmul.2.2.2, hcfunval, hLpsval]
  have h2ypsn : Summable fun n : ℕ => ((PowerSeries.coeff n (2 * Work.C7.yps) : ℚ) : ℂ) * x ^ n := by
    have h : (fun n : ℕ => ((PowerSeries.coeff n (2 * Work.C7.yps) : ℚ) : ℂ) * x ^ n)
        = fun n : ℕ => 2 * (((PowerSeries.coeff n Work.C7.yps : ℚ) : ℂ) * x ^ n) := by
      funext n
      rw [show (2 * Work.C7.yps : PowerSeries ℚ) = PowerSeries.C 2 * Work.C7.yps from rfl,
        PowerSeries.coeff_C_mul]
      push_cast; ring
    rw [h]
    exact hypsn.mul_left 2
  have h2yval : Work.CPull.evp (2 * Work.C7.yps) x = 2 * (x ^ 2 / (x - 1)) := by
    have h := Work.CPull.evp_C_mul (2:ℚ) Work.C7.yps x
    rw [show (PowerSeries.C (2:ℚ) * Work.C7.yps) = (2 * Work.C7.yps : PowerSeries ℚ) from rfl] at h
    rw [h, hsym]
    norm_num
  -- the value of `evp B₂` at `x²/(x−1)`
  have hval : Work.CPull.evp Submission.CDTPlan.B2 (x ^ 2 / (x - 1))
      = 2 * (x ^ 2 / (x - 1)) - x * (x - 2) * Complex.log (1 - x) / (x - 1) := by
    rw [← e1, hB2eq]
    rw [evp_sub_cfun (2 * Work.C7.yps) (Work.C7.cfun * Work.C7.Lps) x h2ypsn hmul.2.2.1,
      h2yval, hmulval, div_mul_eq_mul_div]
  -- summability of the coefficient series of `B₂` at `x²/(x−1)`
  have hsumm : Summable
      (fun n : ℕ => ((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ) * (x ^ 2 / (x - 1)) ^ n) := by
    have h34 : ‖x ^ 2 / (x - 1)‖ / 4 < 1 := by linarith [norm_nonneg (x ^ 2 / (x - 1))]
    refine Summable.of_norm ?_
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_geometric_of_lt_one (by positivity : (0:ℝ) ≤ ‖x ^ 2 / (x - 1)‖ / 4) h34).mul_left (3:ℝ))
    rw [norm_mul, norm_pow]
    calc ‖((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ)‖ * ‖x ^ 2 / (x - 1)‖ ^ n
        ≤ (3 * (1/4:ℝ)^n) * ‖x ^ 2 / (x - 1)‖ ^ n :=
          mul_le_mul_of_nonneg_right (Work.CPull.B2_coeff_bound n) (by positivity)
      _ = 3 * (‖x ^ 2 / (x - 1)‖ / 4) ^ n := by
          rw [mul_assoc, ← mul_pow]; ring
  have hval' : (∑' n : ℕ, ((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ) * (x ^ 2 / (x - 1)) ^ n)
      = 2 * (x ^ 2 / (x - 1)) - x * (x - 2) * Complex.log (1 - x) / (x - 1) := by
    show Work.CPull.evp Submission.CDTPlan.B2 (x ^ 2 / (x - 1)) = _
    exact hval
  simpa only [hval'] using hsumm.hasSum

end

end Work.PureP

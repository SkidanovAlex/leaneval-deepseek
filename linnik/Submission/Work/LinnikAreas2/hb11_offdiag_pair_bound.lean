import Mathlib
import Submission.Work.LinnikAreas2.PsiDefs2
import Submission.Work.LinnikAreas.Density4.Defs
import Submission.Work.LinnikAreas.Density4.Ssm_eq_line
import Submission.Work.LinnikAreas.Density4.mollSeries_eq
import Submission.Work.LinnikAreas.Density4.norm_lcmF_le_gen
import Submission.Work.LinnikAreas.Density4.integrable_gamma_line_mul
import Submission.Work.LinnikAreas.Density4.integrable_one_add_abs_rpow_exp
import Submission.Work.LinnikAreas.Density4.Ssm_fixed_bound
import Submission.Work.LinnikAreas.Density4.det_split
import Submission.Work.LinnikAreas.Density4.Sbig_approx
import Submission.Work.LinnikAreas.Density4.lamMax_div_log_small
import Submission.Work.LinnikAreas2.Hb11Defs
import Submission.Commons.Analysis.Complex.vertical_contour_shift
import Submission.Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one
import Submission.Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay
import Submission.Work.LinnikAreas.Density4.hb_lemma12_1
import Submission.Work.LinnikAreas2.psiS_one_eq_thetaS
import Submission.Work.LinnikAreas2.hb11_logpow_rpow_neg_threshold
import Submission.Work.LinnikAreas2.hb11_crude_bound
import Submission.Work.LinnikContract2.Bridge

open DirichletCharacter Complex MeasureTheory Filter
open scoped Classical BigOperators Topology Interval
noncomputable section

set_option maxHeartbeats 8000000

namespace Work.LinnikAreas2

open Work.LinnikAreas.Density4

/-!
## HB (11.16): the off-diagonal pair bound

The sum of HB (11.16) is the difference `Ssm X - Ssm Y` of the two smoothed Dirichlet sums of
the *mollified* coefficient with cut-offs `X = q^x` and `Y = q^u/L^2`.  Its kernel is `Ptw`
(`Hb11Defs`), the difference of the two exponential kernels, whose `Gamma`-pole at the origin is
removable.  The proof is: (1) the inverse Mellin representation on `Re s = 1`, (2) the contour
shift to `Re s = 1 - sigma.re - 1/k` (leftward, to where the AREA 1 (Burgess) bound applies at
`1 - 1/k`), and (3) the pointwise bound on the shifted line, whose gain is the factor
`X^{c1} + Y^{c1}`; the exponent accounting is `E + 2w/k - u/k < 0` because `u > 2w + 1/3`.
-/

/-- Continuity of `Gamma` on the vertical line `Re s = 1`. -/
lemma continuous_gamma_line_one :
    Continuous (fun t : ℝ => Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hinner : ContinuousAt (fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I) t := by fun_prop
  have houter : ContinuousAt (fun z : ℂ => Complex.Gamma z) ((1 : ℂ) + (t : ℂ) * Complex.I) :=
    Complex.continuousAt_Gamma _ (by
      intro m hm
      have h1 : (1 : ℝ) = -(m : ℝ) := by
        have h2 := congrArg Complex.re hm
        simpa using h2
      have h3 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith)
  exact houter.comp (f := fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I) hinner

/-- The line `Re s = 1` integrand of the *naive* (single-cut-off) representation is integrable:
`Gamma` decays exponentially, `Y^{1+it}` has modulus `Y`, and the character `L`-function and the
finite lcm-weight are bounded uniformly in `t`. -/
lemma integrable_naive_line_one (q : ℕ) [NeZero q] (hq : 2 ≤ q) {U V W Y : ℝ} (hU : 0 < U)
    (hUV : U ≤ V) (hV : 1 ≤ V) (hW : 1 ≤ W) (hY : 0 < Y) (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (σ : ℂ) (hσ : 0 < σ.re) :
    Integrable (fun t : ℝ => Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)
      * (Y : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)
      * DirichletCharacter.LFunction χ (σ + ((1 : ℂ) + (t : ℂ) * Complex.I))
      * lcmF q U V W χ (σ + ((1 : ℂ) + (t : ℂ) * Complex.I))) := by
  classical
  obtain ⟨Cg, hCgpos, hCg⟩ :=
    Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay 1 one_pos
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  set Csig : ℝ := 1 + |σ.im| with hCsigdef
  have hCsig0 : 0 ≤ Csig := by rw [hCsigdef]; positivity
  set DF : ℝ := (V * W) ^ (1 / (1 : ℝ)) * (1 + Real.log (V * W)) ^ 3 with hDFdef
  have hDF0 : 0 ≤ DF := by
    rw [hDFdef]
    refine mul_nonneg (Real.rpow_nonneg (by nlinarith) _) (pow_nonneg ?_ 3)
    have : (1 : ℝ) ≤ V * W := by nlinarith
    linarith [Real.log_nonneg this]
  set M : ℝ := 2 * Cg * Y * (Real.log q + 6 + Csig) * DF with hMdef
  have hbase : Integrable (fun t : ℝ => (1 + |t|) ^ (2 : ℝ) * Real.exp (-(Real.pi / 2 * |t|))) :=
    integrable_one_add_abs_rpow_exp 2 (Real.pi / 2) (by positivity)
  have hmaj : Integrable (fun t : ℝ =>
      M * ((1 + |t|) ^ (2 : ℝ) * Real.exp (-(Real.pi / 2 * |t|)))) := hbase.const_mul M
  have hYne : (Y : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hY
  have hline : Continuous (fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  have hcpow : Continuous (fun t : ℝ => (Y : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
    have hd : Differentiable ℂ (fun s : ℂ => (Y : ℂ) ^ s) :=
      differentiable_id.const_cpow (Or.inl hYne)
    exact hd.continuous.comp hline
  have hLc : Continuous (fun t : ℝ => DirichletCharacter.LFunction χ
      (σ + ((1 : ℂ) + (t : ℂ) * Complex.I))) :=
    (differentiable_LFunction hχ).continuous.comp (continuous_const.add hline)
  have hFc : Continuous (fun t : ℝ => lcmF q U V W χ (σ + ((1 : ℂ) + (t : ℂ) * Complex.I))) :=
    (differentiable_lcmF q U V W χ).continuous.comp (continuous_const.add hline)
  have hcont : Continuous (fun t : ℝ => Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)
      * (Y : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)
      * DirichletCharacter.LFunction χ (σ + ((1 : ℂ) + (t : ℂ) * Complex.I))
      * lcmF q U V W χ (σ + ((1 : ℂ) + (t : ℂ) * Complex.I))) :=
    ((continuous_gamma_line_one.mul hcpow).mul hLc).mul hFc
  refine hmaj.mono' hcont.aestronglyMeasurable ?_
  filter_upwards with t
  set s : ℂ := (1 : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsr : s.re = 1 := by simp [hsdef]
  have hsi : s.im = t := by simp [hsdef]
  have hΓ : ‖Complex.Gamma s‖ ≤ Cg * (1 + |t|) * Real.exp (-(Real.pi / 2 * |t|)) := by
    have h := hCg t
    rw [Real.rpow_one] at h
    rw [show -(Real.pi / 2) * |t| = -(Real.pi / 2 * |t|) by ring] at h
    have hs : s = (1 : ℂ) + Complex.I * (t : ℂ) := by rw [hsdef]; ring
    rw [hs]
    exact h
  have hcp : ‖(Y : ℂ) ^ s‖ = Y := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY, hsr, Real.rpow_one]
  have hrim : (σ + s).im = σ.im + t := by simp [Complex.add_im, hsi]
  have hrre : (σ + s).re = σ.re + 1 := by simp [Complex.add_re, hsr]
  have hLb : ‖DirichletCharacter.LFunction χ (σ + s)‖
      ≤ Real.log q + Real.log (2 + |(σ + s).im|) + 6 := by
    refine Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one χ hχ (σ + s) ?_
    rw [hrre]; linarith [hσ]
  have hFb : ‖lcmF q U V W χ (σ + s)‖ ≤ DF := by
    have hFb0 := norm_lcmF_le_gen q hU hUV hV hW χ (k := 1) le_rfl (s := σ + s) (by
      rw [hrre]; linarith [hσ])
    simpa [hDFdef, one_div] using hFb0
  have hB6 : Real.log q + Real.log (2 + |(σ + s).im|) + 6
      ≤ (Real.log q + 6 + Csig) * (2 * (1 + |t|)) := by
    rw [hrim]
    have h3 : Real.log (2 + |σ.im + t|) ≤ 2 + |σ.im| + |t| := by
      refine le_trans (Real.log_le_self (by positivity)) ?_
      have htri : |σ.im + t| ≤ |σ.im| + |t| := abs_add_le _ _
      linarith
    have h4 : 2 + |σ.im| + |t| ≤ Csig * (2 * (1 + |t|)) := by
      rw [hCsigdef]; nlinarith [abs_nonneg t, abs_nonneg σ.im]
    have hL0 : 0 ≤ Real.log q + 6 + Csig := by linarith
    have h1t : (1 : ℝ) ≤ 2 * (1 + |t|) := by linarith [abs_nonneg t]
    have h9 : Real.log q + 6 ≤ (Real.log q + 6) * (2 * (1 + |t|)) := by nlinarith [hL0]
    have hkey : (Real.log q + 6 + Csig) * (2 * (1 + |t|))
        = (Real.log q + 6) * (2 * (1 + |t|)) + Csig * (2 * (1 + |t|)) := by ring
    rw [hkey]; linarith
  have hnorm : ‖Complex.Gamma s * (Y : ℂ) ^ s * DirichletCharacter.LFunction χ (σ + s)
        * lcmF q U V W χ (σ + s)‖
      = ‖Complex.Gamma s‖ * ‖(Y : ℂ) ^ s‖ * ‖DirichletCharacter.LFunction χ (σ + s)‖
        * ‖lcmF q U V W χ (σ + s)‖ := by simp only [norm_mul]
  set A : ℝ := Cg * (1 + |t|) * Real.exp (-(Real.pi / 2 * |t|)) with hAdef
  set B : ℝ := Real.log q + Real.log (2 + |(σ + s).im|) + 6 with hBdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have : 0 ≤ Real.log (2 + |(σ + s).im|) :=
      Real.log_nonneg (by linarith [abs_nonneg (σ + s).im])
    linarith
  have h12 : ‖Complex.Gamma s‖ * ‖(Y : ℂ) ^ s‖ ≤ A * Y :=
    mul_le_mul hΓ (le_of_eq hcp) (norm_nonneg _) hA0
  have h34 : ‖DirichletCharacter.LFunction χ (σ + s)‖ * ‖lcmF q U V W χ (σ + s)‖ ≤ B * DF :=
    mul_le_mul hLb hFb (norm_nonneg _) hB0
  rw [hnorm]
  have step1 : (‖Complex.Gamma s‖ * ‖(Y : ℂ) ^ s‖)
      * (‖DirichletCharacter.LFunction χ (σ + s)‖ * ‖lcmF q U V W χ (σ + s)‖) ≤ (A * Y) * (B * DF) :=
    mul_le_mul h12 h34 (by positivity) (by positivity)
  have step2 : (A * Y) * (B * DF) ≤ (A * Y) * ((Real.log q + 6 + Csig) * (2 * (1 + |t|)) * DF) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right hB6 hDF0
  have step3 : (A * Y) * ((Real.log q + 6 + Csig) * (2 * (1 + |t|)) * DF)
      ≤ M * ((1 + |t|) ^ (2 : ℝ) * Real.exp (-(Real.pi / 2 * |t|))) := by
    rw [hMdef, hAdef]
    have he : (1 + |t|) ^ (2 : ℝ) = (1 + |t|) * (1 + |t|) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
    rw [he]
    have key : Cg * (1 + |t|) * Real.exp (-(Real.pi / 2 * |t|)) * Y
            * ((Real.log q + 6 + Csig) * (2 * (1 + |t|)) * DF)
          = 2 * Cg * Y * (Real.log q + 6 + Csig) * DF
            * ((1 + |t|) * (1 + |t|) * Real.exp (-(Real.pi / 2 * |t|))) := by ring
    rw [key]
  calc ‖Complex.Gamma s‖ * ‖(Y : ℂ) ^ s‖ * ‖DirichletCharacter.LFunction χ (σ + s)‖
        * ‖lcmF q U V W χ (σ + s)‖
      = (‖Complex.Gamma s‖ * ‖(Y : ℂ) ^ s‖)
        * (‖DirichletCharacter.LFunction χ (σ + s)‖ * ‖lcmF q U V W χ (σ + s)‖) := by ring
    _ ≤ (A * Y) * (B * DF) := step1
    _ ≤ (A * Y) * ((Real.log q + 6 + Csig) * (2 * (1 + |t|)) * DF) := step2
    _ ≤ M * ((1 + |t|) ^ (2 : ℝ) * Real.exp (-(Real.pi / 2 * |t|))) := step3

/-! ## The inverse Mellin representation of the difference on `Re s = 1` -/

/-- **HB (11.16), inverse Mellin step.**  The difference of the two cut-off smoothed sums of the
mollified coefficient is the integral of the difference kernel `Ptw` on `Re s = 1`. -/
theorem Ssm_sub_eq_Ptw_line (q : ℕ) [NeZero q] (hq : 2 ≤ q) (U V W X Y : ℝ)
    (χ : DirichletCharacter ℂ q) (σ : ℂ) (hU : 0 < U) (hUV : U ≤ V) (hW : 1 ≤ W) (hV : 1 ≤ V)
    (hX : 0 < X) (hY : 0 < Y) (hχ : χ ≠ 1) (hσ : 0 < σ.re) :
    Ssm q U V W X χ σ - Ssm q U V W Y χ σ
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, Ptw q U V W X Y χ σ ((1 : ℂ) + (t : ℂ) * Complex.I) := by
  have hW0 : 0 < W := lt_of_lt_of_le one_pos hW
  have h1 := Ssm_eq_naive_line q U V W X χ σ hU hUV hW0 hX hσ
  have h2 := Ssm_eq_naive_line q U V W Y χ σ hU hUV hW0 hY hσ
  rw [h1, h2]
  have hI1 := integrable_naive_line_one q hq hU hUV hV hW hX χ hχ σ hσ
  have hI2 := integrable_naive_line_one q hq hU hUV hV hW hY χ hχ σ hσ
  rw [← mul_sub, ← MeasureTheory.integral_sub hI1 hI2]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hs : ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
  beta_reduce
  rw [Ptw_eq_naive q U V W X Y χ σ ((1 : ℂ) + (t : ℂ) * Complex.I) hs]
  ring

/-! ## Continuity and `L¹`-bounds for `Gamma` on vertical lines with negative real part -/

/-- Continuity of `Gamma` on a vertical line of real part in `(-1,0)`. -/
lemma continuous_gamma_line_of_gt {c : ℝ} (hc1 : -1 < c) (hc0 : c < 0) :
    Continuous (fun t : ℝ => Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hinner : ContinuousAt (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) t := by fun_prop
  have houter : ContinuousAt (fun z : ℂ => Complex.Gamma z) ((c : ℂ) + (t : ℂ) * Complex.I) :=
    Complex.continuousAt_Gamma _ (by
      intro m hm
      have h2 : c = -(m : ℝ) := by
        have h := congrArg Complex.re hm
        simpa using h
      rcases Nat.eq_zero_or_pos m with h0 | hpos
      · rw [h0] at h2
        simp at h2
        linarith [hc0]
      · have h4 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hpos
        linarith [hc1])
  exact houter.comp (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) hinner

/-- `t ↦ ‖Γ(c+it)‖(2+|t|)` is integrable for `-1 < c < 0`: `Γ` has only a simple pole at the
origin, so dividing by `s` shifts the line to `Re = c + 1 > 0` at the cost of the constant
`1/|c|`. -/
lemma integrable_gamma_line_neg {c : ℝ} (hc1 : -1 < c) (hc2 : c < 0) :
    Integrable (fun t : ℝ => ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|)) := by
  have hc1' : (0 : ℝ) < c + 1 := by linarith
  have h := integrable_gamma_line_mul (c + 1) hc1'
  have hcne : c ≠ 0 := ne_of_lt hc2
  have hcabs : 0 < |c| := abs_pos.mpr hcne
  refine (h.const_mul (1 / |c|)).mono' ?_ ?_
  · exact ((continuous_gamma_line_of_gt hc1 hc2).norm.mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards with t
    have hsne : ((c : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have hre := congrArg Complex.re h0
      simp at hre
      exact hcne hre
    have hg : Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)
        = Complex.Gamma (((c : ℂ) + (t : ℂ) * Complex.I) + 1)
          / ((c : ℂ) + (t : ℂ) * Complex.I) := by
      rw [Complex.Gamma_add_one _ hsne]; field_simp
    have harg : ((c : ℂ) + (t : ℂ) * Complex.I) + 1
        = (((c + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
    have hnorm : |c| ≤ ‖((c : ℂ) + (t : ℂ) * Complex.I)‖ := by
      have h1 := Complex.abs_re_le_norm ((c : ℂ) + (t : ℂ) * Complex.I)
      simpa using h1
    have hgoal : ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖
        = ‖Complex.Gamma ((((c + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖
          / ‖((c : ℂ) + (t : ℂ) * Complex.I)‖ := by
      rw [hg, harg, norm_div]
    have hstep : (‖((c : ℂ) + (t : ℂ) * Complex.I)‖)⁻¹ ≤ (|c|)⁻¹ := by
      rw [inv_le_inv₀ (by positivity) hcabs]
      exact hnorm
    have h2 : 0 ≤ ‖Complex.Gamma ((((c + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ := norm_nonneg _
    have h3 : 0 ≤ 2 + |t| := by positivity
    rw [Real.norm_of_nonneg (by positivity :
      (0 : ℝ) ≤ ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|))]
    calc ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|)
        = ‖Complex.Gamma ((((c + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖
            / ‖((c : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) := by rw [hgoal]
      _ = ‖Complex.Gamma ((((c + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖
            * (‖((c : ℂ) + (t : ℂ) * Complex.I)‖)⁻¹ * (2 + |t|) := by rw [div_eq_mul_inv]
      _ ≤ ‖Complex.Gamma ((((c + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ * (|c|)⁻¹ * (2 + |t|) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep h2) h3
      _ = (1 / |c|) * (‖Complex.Gamma ((((c + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖
            * (2 + |t|)) := by rw [one_div]; ring

/-! ## The pointwise bound on the shifted line -/

/-- **HB (11.16), pointwise shifted-line bound.**  On the line `Re s = c₁ = 1 - σ.re - 1/k`
(where `Re (σ + s) = 1 - 1/k`, so AREA 1 applies) the regularised kernel is bounded by
`Cb(2+|t|)·‖Γ(c₁+it)‖·(X^{c₁} + Y^{c₁})·(VW)^{1/k}(1+log(VW))³`: the gain is the factor
`X^{c₁} + Y^{c₁}`, which is a negative power of `q`. -/
lemma norm_Ptw_shifted_pointwise (q : ℕ) [NeZero q] {U V W X Y : ℝ} (hU : 0 < U) (hUV : U ≤ V)
    (hV : 1 ≤ V) (hW : 1 ≤ W) (hX : 0 < X) (hY : 0 < Y) (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (σ : ℂ) {k : ℕ} (hk : 1 ≤ k) {Cb c₁ : ℝ}
    (hCb : 0 < Cb) (hc₁ : c₁ = 1 - σ.re - (k : ℝ)⁻¹) (hc₁neg : c₁ < 0)
    (hLbd : ∀ t : ℝ, ‖DirichletCharacter.LFunction χ (σ + ((c₁ : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ Cb * (2 + |t|)) :
    ∀ t : ℝ, ‖Ptw q U V W X Y χ σ ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Cb * (2 + |t|) * ‖Complex.Gamma ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖
        * ((X ^ c₁ + Y ^ c₁) * ((V * W) ^ (1 / (k : ℝ)) * (1 + Real.log (V * W)) ^ 3)) := by
  intro t
  set s : ℂ := (c₁ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsr : s.re = c₁ := by simp [hsdef]
  have hsne : s ≠ 0 := by
    intro h0
    have h1 := congrArg Complex.re h0
    simp at h1
    linarith [hc₁neg]
  have hcr : (σ + s).re = 1 - (k : ℝ)⁻¹ := by rw [Complex.add_re, hsr, hc₁]; ring
  have hF : ‖lcmF q U V W χ (σ + s)‖ ≤ (V * W) ^ (1 / (k : ℝ)) * (1 + Real.log (V * W)) ^ 3 :=
    norm_lcmF_le_gen q hU hUV hV hW χ hk hcr.ge
  have hXe : ‖(X : ℂ) ^ s‖ = X ^ c₁ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, hsr]
  have hYe : ‖(Y : ℂ) ^ s‖ = Y ^ c₁ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY, hsr]
  have htri : ‖(X : ℂ) ^ s - (Y : ℂ) ^ s‖ ≤ X ^ c₁ + Y ^ c₁ := by
    calc ‖(X : ℂ) ^ s - (Y : ℂ) ^ s‖ ≤ ‖(X : ℂ) ^ s‖ + ‖(Y : ℂ) ^ s‖ := norm_sub_le _ _
      _ = X ^ c₁ + Y ^ c₁ := by rw [hXe, hYe]
  have hL : ‖DirichletCharacter.LFunction χ (σ + s)‖ ≤ Cb * (2 + |t|) := hLbd t
  have hnorm : ‖Ptw q U V W X Y χ σ s‖
      = ‖Complex.Gamma s‖ * ‖(X : ℂ) ^ s - (Y : ℂ) ^ s‖
        * ‖DirichletCharacter.LFunction χ (σ + s)‖ * ‖lcmF q U V W χ (σ + s)‖ := by
    rw [Ptw_eq_naive q U V W X Y χ σ s hsne]
    simp only [norm_mul]
  have hX0 : 0 ≤ X ^ c₁ + Y ^ c₁ := by
    have h1 : 0 < X ^ c₁ := Real.rpow_pos_of_pos hX _
    have h2 : 0 < Y ^ c₁ := Real.rpow_pos_of_pos hY _
    linarith
  have hDF0 : 0 ≤ (V * W) ^ (1 / (k : ℝ)) * (1 + Real.log (V * W)) ^ 3 := by
    refine mul_nonneg (Real.rpow_nonneg (by nlinarith) _) (pow_nonneg ?_ 3)
    have : (1 : ℝ) ≤ V * W := by nlinarith
    linarith [Real.log_nonneg this]
  have hL0 : 0 ≤ Cb * (2 + |t|) := by positivity
  have hΓ0 : 0 ≤ ‖Complex.Gamma s‖ := norm_nonneg _
  have hm1 : ‖Complex.Gamma s‖ * ‖(X : ℂ) ^ s - (Y : ℂ) ^ s‖ ≤ ‖Complex.Gamma s‖ * (X ^ c₁ + Y ^ c₁) :=
    mul_le_mul_of_nonneg_left htri hΓ0
  have hm2 : (‖Complex.Gamma s‖ * ‖(X : ℂ) ^ s - (Y : ℂ) ^ s‖)
        * ‖DirichletCharacter.LFunction χ (σ + s)‖
      ≤ (‖Complex.Gamma s‖ * (X ^ c₁ + Y ^ c₁)) * (Cb * (2 + |t|)) :=
    mul_le_mul hm1 hL (norm_nonneg _) (mul_nonneg hΓ0 hX0)
  have hm3 : ((‖Complex.Gamma s‖ * ‖(X : ℂ) ^ s - (Y : ℂ) ^ s‖)
        * ‖DirichletCharacter.LFunction χ (σ + s)‖) * ‖lcmF q U V W χ (σ + s)‖
      ≤ ((‖Complex.Gamma s‖ * (X ^ c₁ + Y ^ c₁)) * (Cb * (2 + |t|)))
        * ((V * W) ^ (1 / (k : ℝ)) * (1 + Real.log (V * W)) ^ 3) :=
    mul_le_mul hm2 hF (norm_nonneg _) (mul_nonneg (mul_nonneg hΓ0 hX0) hL0)
  rw [hnorm]
  calc ‖Complex.Gamma s‖ * ‖(X : ℂ) ^ s - (Y : ℂ) ^ s‖
        * ‖DirichletCharacter.LFunction χ (σ + s)‖ * ‖lcmF q U V W χ (σ + s)‖
      = ((‖Complex.Gamma s‖ * ‖(X : ℂ) ^ s - (Y : ℂ) ^ s‖)
        * ‖DirichletCharacter.LFunction χ (σ + s)‖) * ‖lcmF q U V W χ (σ + s)‖ := by ring
    _ ≤ ((‖Complex.Gamma s‖ * (X ^ c₁ + Y ^ c₁)) * (Cb * (2 + |t|)))
        * ((V * W) ^ (1 / (k : ℝ)) * (1 + Real.log (V * W)) ^ 3) := hm3
    _ = Cb * (2 + |t|) * ‖Complex.Gamma s‖
        * ((X ^ c₁ + Y ^ c₁) * ((V * W) ^ (1 / (k : ℝ)) * (1 + Real.log (V * W)) ^ 3)) := by ring

/-! ## Integrability of the regularised kernel on the two lines of the shift -/

/-- Integrability of the regularised kernel on the shifted line `Re s = c₁ < 0`. -/
lemma integrable_Ptw_line_shifted (q : ℕ) [NeZero q] {U V W X Y : ℝ} (hU : 0 < U) (hUV : U ≤ V)
    (hV : 1 ≤ V) (hW : 1 ≤ W) (hX : 0 < X) (hY : 0 < Y) (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (σ : ℂ) {k : ℕ} (hk : 1 ≤ k) {Cb c₁ : ℝ}
    (hCb : 0 < Cb) (hc₁ : c₁ = 1 - σ.re - (k : ℝ)⁻¹) (hc₁gt : -1 < c₁) (hc₁neg : c₁ < 0)
    (hLbd : ∀ t : ℝ, ‖DirichletCharacter.LFunction χ (σ + ((c₁ : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ Cb * (2 + |t|)) :
    Integrable (fun t : ℝ => Ptw q U V W X Y χ σ ((c₁ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hbd := norm_Ptw_shifted_pointwise q hU hUV hV hW hX hY χ hχ σ hk hCb hc₁ hc₁neg hLbd
  have hΓint := integrable_gamma_line_neg hc₁gt hc₁neg
  set K : ℝ := Cb * ((X ^ c₁ + Y ^ c₁) * ((V * W) ^ (1 / (k : ℝ)) * (1 + Real.log (V * W)) ^ 3))
    with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    refine mul_nonneg hCb.le (mul_nonneg ?_ ?_)
    · have h1 : 0 < X ^ c₁ := Real.rpow_pos_of_pos hX _
      have h2 : 0 < Y ^ c₁ := Real.rpow_pos_of_pos hY _
      linarith
    · refine mul_nonneg (Real.rpow_nonneg (by nlinarith) _) (pow_nonneg ?_ 3)
      have : (1 : ℝ) ≤ V * W := by nlinarith
      linarith [Real.log_nonneg this]
  have hmaj : Integrable (fun t : ℝ =>
      K * (‖Complex.Gamma ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|))) := hΓint.const_mul K
  have hcont : Continuous (fun t : ℝ => Ptw q U V W X Y χ σ ((c₁ : ℂ) + (t : ℂ) * Complex.I)) := by
    have hline : Continuous (fun t : ℝ => (c₁ : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
    refine (differentiableOn_Ptw q U V W X Y χ hχ hX hY σ).continuousOn.comp_continuous hline ?_
    intro t
    show -1 < ((c₁ : ℂ) + (t : ℂ) * Complex.I).re
    simp
    exact hc₁gt
  refine hmaj.mono' hcont.aestronglyMeasurable ?_
  filter_upwards with t
  have h1 := hbd t
  calc ‖Ptw q U V W X Y χ σ ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Cb * (2 + |t|) * ‖Complex.Gamma ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖
        * ((X ^ c₁ + Y ^ c₁) * ((V * W) ^ (1 / (k : ℝ)) * (1 + Real.log (V * W)) ^ 3)) := h1
    _ = K * (‖Complex.Gamma ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|)) := by
        rw [hKdef]; ring

/-- Integrability of the regularised kernel on the line `Re s = 1` (off the origin `Ptw` agrees
with the difference of the two naive kernels, each of which is integrable). -/
lemma integrable_Ptw_line_one (q : ℕ) [NeZero q] (hq : 2 ≤ q) {U V W X Y : ℝ} (hU : 0 < U)
    (hUV : U ≤ V) (hW : 1 ≤ W) (hV : 1 ≤ V) (hX : 0 < X) (hY : 0 < Y)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (σ : ℂ) (hσ : 0 < σ.re) :
    Integrable (fun t : ℝ => Ptw q U V W X Y χ σ ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
  have hfun : (fun t : ℝ => Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)
        * (X : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)
        * DirichletCharacter.LFunction χ (σ + ((1 : ℂ) + (t : ℂ) * Complex.I))
        * lcmF q U V W χ (σ + ((1 : ℂ) + (t : ℂ) * Complex.I))
      - Complex.Gamma ((1 : ℂ) + (t : ℂ) * Complex.I)
        * (Y : ℂ) ^ ((1 : ℂ) + (t : ℂ) * Complex.I)
        * DirichletCharacter.LFunction χ (σ + ((1 : ℂ) + (t : ℂ) * Complex.I))
        * lcmF q U V W χ (σ + ((1 : ℂ) + (t : ℂ) * Complex.I)))
      = (fun t : ℝ => Ptw q U V W X Y χ σ ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
    funext t
    have hs : ((1 : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have h1 := congrArg Complex.re h0
      simp at h1
    rw [Ptw_eq_naive q U V W X Y χ σ ((1 : ℂ) + (t : ℂ) * Complex.I) hs]
    ring
  rw [← hfun]
  exact (integrable_naive_line_one q hq hU hUV hV hW hX χ hχ σ hσ).sub
    (integrable_naive_line_one q hq hU hUV hV hW hY χ hχ σ hσ)

/-! ## The horizontal edges of the shift rectangle -/

/-- Uniform character-`L` bound on the segment `1 - 1/k ≤ Re ≤ 2`  (AREA 1 below `Re = 1`,
`norm_LFunction_le_re_ge_one` at and above it). -/
lemma LFunction_segment_bound (h1 : Work.LinnikContract2.Area1) (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {k : ℕ} (hk : 3 ≤ k) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ CL : ℝ, 0 < CL ∧ ∀ r t : ℝ, 1 - (k : ℝ)⁻¹ ≤ r → r ≤ 2 →
      ‖DirichletCharacter.LFunction χ ((r : ℂ) + (t : ℂ) * Complex.I)‖ ≤ CL * (2 + |t|) := by
  obtain ⟨Cb0, hCb0pos, hCb0⟩ := h1.1 k hk (1 : ℝ) (by norm_num)
  have hq3R : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) < (q : ℝ) := by linarith
  have hlogq : 0 < Real.log q := Real.log_pos hq1
  have hlog3 : (1 : ℝ) ≤ Real.log q := by
    have h3 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]; exact Real.exp_one_lt_three
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hq3R
    linarith
  set CL : ℝ := Cb0 * (q : ℝ) ^ ((1 / 3 : ℝ) * (1 / (k : ℝ)) * (1 + 1 / (k : ℝ)) + 1)
    + (Real.log q + 8) with hCLdef
  have hCL0 : 0 < CL := by rw [hCLdef]; positivity
  have hCLbig : Real.log q + 8 ≤ CL := by
    rw [hCLdef]
    have h0 : 0 ≤ Cb0 * (q : ℝ) ^ ((1 / 3 : ℝ) * (1 / (k : ℝ)) * (1 + 1 / (k : ℝ)) + 1) :=
      mul_nonneg hCb0pos.le (Real.rpow_nonneg (Nat.cast_nonneg q) _)
    linarith
  have hCLbig2 : Cb0 * (q : ℝ) ^ ((1 / 3 : ℝ) * (1 / (k : ℝ)) * (1 + 1 / (k : ℝ)) + 1) ≤ CL := by
    rw [hCLdef]; linarith
  refine ⟨CL, hCL0, ?_⟩
  intro r t hr1 hr2
  rcases lt_or_ge r 1 with hrlt | hrge
  · have hr1' : 1 - 1 / (k : ℝ) ≤ r := by rw [one_div]; exact hr1
    have hb := hCb0 (χ := χ) hχ r t hr1' (by
      have hll : 0 ≤ Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) :=
        div_nonneg (Real.log_nonneg hlog3) hlogq.le
      linarith)
    refine le_trans hb ?_
    have hrle : (0 : ℝ) ≤ 1 - r := by linarith
    have hk0 : (0 : ℝ) ≤ (k : ℝ)⁻¹ := by positivity
    have hkk : (0 : ℝ) ≤ 1 + 1 / (k : ℝ) := by linarith
    have hexp : (1 / 3 : ℝ) * (1 - r) * (1 + 1 / (k : ℝ)) + 1
        ≤ (1 / 3 : ℝ) * (1 / (k : ℝ)) * (1 + 1 / (k : ℝ)) + 1 := by
      have hle : 1 - r ≤ 1 / (k : ℝ) := by linarith
      nlinarith [hkk, hrle, hk0, hle]
    have hpow : (q : ℝ) ^ ((1 / 3 : ℝ) * (1 - r) * (1 + 1 / (k : ℝ)) + 1)
        ≤ (q : ℝ) ^ ((1 / 3 : ℝ) * (1 / (k : ℝ)) * (1 + 1 / (k : ℝ)) + 1) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ (q : ℝ)) hexp
    have h1' : Cb0 * (q : ℝ) ^ ((1 / 3 : ℝ) * (1 - r) * (1 + 1 / (k : ℝ)) + 1)
        ≤ Cb0 * (q : ℝ) ^ ((1 / 3 : ℝ) * (1 / (k : ℝ)) * (1 + 1 / (k : ℝ)) + 1) :=
      mul_le_mul_of_nonneg_left hpow hCb0pos.le
    have h3 : Cb0 * (q : ℝ) ^ ((1 / 3 : ℝ) * (1 - r) * (1 + 1 / (k : ℝ)) + 1) * (1 + |t|)
        ≤ Cb0 * (q : ℝ) ^ ((1 / 3 : ℝ) * (1 / (k : ℝ)) * (1 + 1 / (k : ℝ)) + 1) * (2 + |t|) :=
      mul_le_mul h1' (by linarith [abs_nonneg t]) (by positivity)
        (mul_nonneg hCb0pos.le (Real.rpow_nonneg (by linarith) _))
    have h4 : Cb0 * (q : ℝ) ^ ((1 / 3 : ℝ) * (1 / (k : ℝ)) * (1 + 1 / (k : ℝ)) + 1) * (2 + |t|)
        ≤ CL * (2 + |t|) :=
      mul_le_mul_of_nonneg_right hCLbig2 (by linarith [abs_nonneg t])
    linarith
  · have hb := Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one χ hχ
      ((r : ℂ) + (t : ℂ) * Complex.I) (by simp; linarith)
    have him : (((r : ℂ) + (t : ℂ) * Complex.I)).im = t := by simp
    rw [him] at hb
    refine le_trans hb ?_
    have habs : (0 : ℝ) ≤ |t| := abs_nonneg t
    have hloglt : Real.log (2 + |t|) ≤ 1 + |t| := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 + |t| by positivity)
      linarith
    have h7 : Real.log (q : ℝ) + 7 + |t| ≤ (Real.log (q : ℝ) + 8) * (2 + |t|) := by
      nlinarith [hlog3, habs]
    have h8 : (Real.log (q : ℝ) + 8) * (2 + |t|) ≤ CL * (2 + |t|) :=
      mul_le_mul_of_nonneg_right hCLbig (by linarith)
    linarith

/-- **HB (11.16), edge bound.**  On the horizontal edges `Im s = ±T` (`T ≥ 1`) of the rectangle
`[c₁,1] × [-T,T]` the regularised kernel decays like `e^{-πT/2}T⁴`. -/
lemma norm_Ptw_edge (h1 : Work.LinnikContract2.Area1) (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {U V W X Y : ℝ} (hU : 0 < U) (hUV : U ≤ V) (hV : 1 ≤ V) (hW : 1 ≤ W) (hX : 0 < X)
    (hY : 0 < Y) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (σ : ℂ) (hσ0 : 0 < σ.re)
    (hσ1 : σ.re ≤ 1) {k : ℕ} (hk : 3 ≤ k) {c₁ : ℝ} (hc₁ : c₁ = 1 - σ.re - (k : ℝ)⁻¹) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Set.Icc c₁ 1, ∀ T : ℝ, 1 ≤ T →
      (‖Ptw q U V W X Y χ σ ((x : ℂ) + (T : ℂ) * Complex.I)‖
          ≤ C * Real.exp (-(Real.pi / 2 * T)) * T ^ 4) ∧
      (‖Ptw q U V W X Y χ σ ((x : ℂ) - (T : ℂ) * Complex.I)‖
          ≤ C * Real.exp (-(Real.pi / 2 * T)) * T ^ 4) := by
  obtain ⟨Cg, hCgpos, hCg⟩ := Gamma_vertical_uniform
  obtain ⟨CL, hCL0, hLunif⟩ := LFunction_segment_bound h1 q hq hk χ hχ
  have hq3R : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 < Real.log q := Real.log_pos (by linarith : (1 : ℝ) < (q : ℝ))
  set DF : ℝ := (V * W) ^ (1 / (k : ℝ)) * (1 + Real.log (V * W)) ^ 3 with hDFdef
  have hDF0 : 0 ≤ DF := by
    rw [hDFdef]
    refine mul_nonneg (Real.rpow_nonneg (by nlinarith) _) (pow_nonneg ?_ 3)
    have : (1 : ℝ) ≤ V * W := by nlinarith
    linarith [Real.log_nonneg this]
  have hX0 : (0 : ℝ) ≤ X := hX.le
  have hY0 : (0 : ℝ) ≤ Y := hY.le
  refine ⟨Cg * 4 * (max 1 X + max 1 X⁻¹ + (max 1 Y + max 1 Y⁻¹)) * CL * (3 + |σ.im|) * DF + 1,
    by positivity, ?_⟩
  intro x hx T hT
  obtain ⟨hx1, hx2⟩ := hx
  have hT0 : (0 : ℝ) < T := by linarith
  have hkinv3 : (k : ℝ)⁻¹ ≤ 1 / 3 := by
    have h : (1 : ℝ) / (k : ℝ) ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hk)
    simpa [one_div] using h
  have hxlow : -(1 / 3 : ℝ) ≤ x := by
    rw [hc₁] at hx1
    linarith
  have hxl : 1 - (k : ℝ)⁻¹ ≤ σ.re + x := by
    rw [hc₁] at hx1
    linarith
  have hcx : c₁ ≤ x := hx1
  have hc₁ge : (-1 : ℝ) ≤ c₁ := by
    have h : (k : ℝ)⁻¹ ≤ 1 / 3 := by
      have h' : (1 : ℝ) / (k : ℝ) ≤ 1 / 3 :=
        one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hk)
      simpa [one_div] using h'
    rw [hc₁]; linarith
  have key : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
      ‖Ptw q U V W X Y χ σ ((x : ℂ) + (ε : ℂ) * (T : ℂ) * Complex.I)‖
        ≤ (Cg * 4 * (max 1 X + max 1 X⁻¹ + (max 1 Y + max 1 Y⁻¹)) * CL * (3 + |σ.im|) * DF + 1)
            * Real.exp (-(Real.pi / 2 * T)) * T ^ 4 := by
    intro ε hε
    have hεabs : |ε| = 1 := by rcases hε with h | h <;> rw [h] <;> norm_num
    have hεT : |ε * T| = T := by rw [abs_mul, hεabs, one_mul, abs_of_pos hT0]
    set s : ℂ := (x : ℂ) + (ε : ℂ) * (T : ℂ) * Complex.I with hsdef
    have hs_re : s.re = x := by simp [hsdef]
    have hs_im : s.im = ε * T := by simp [hsdef]
    have hs_norm : T ≤ ‖s‖ := by
      calc T = |s.im| := by rw [hs_im, hεT]
        _ ≤ ‖s‖ := Complex.abs_im_le_norm s
    have hs_ne : s ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hs_norm
      linarith
    have hΓb : ‖Complex.Gamma s‖
        ≤ Cg * (1 + T) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi / 2 * T)) * T⁻¹ := by
      have harg : s + 1 = (((x + 1 : ℝ)) : ℂ) + ((ε * T : ℝ) : ℂ) * Complex.I := by
        rw [hsdef]; push_cast; ring
      have hb := hCg (x + 1) (by linarith) (by linarith) (ε * T)
      have hΓ1 : ‖Complex.Gamma (s + 1)‖
          ≤ Cg * (1 + T) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi / 2 * T)) := by
        rw [harg]
        simpa only [hεT] using hb
      have hsplit : Complex.Gamma s = Complex.Gamma (s + 1) / s := by
        rw [Complex.Gamma_add_one s hs_ne]; field_simp
      have hinv : ‖s‖⁻¹ ≤ T⁻¹ := by
        rw [inv_le_inv₀ (by positivity) hT0]
        exact hs_norm
      calc ‖Complex.Gamma s‖ = ‖Complex.Gamma (s + 1)‖ * ‖s‖⁻¹ := by
            rw [hsplit, norm_div, div_eq_mul_inv]
        _ ≤ (Cg * (1 + T) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi / 2 * T))) * T⁻¹ :=
            mul_le_mul hΓ1 hinv (by positivity) (by positivity)
        _ = Cg * (1 + T) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi / 2 * T)) * T⁻¹ := by ring
    have hXb : ‖(X : ℂ) ^ s‖ ≤ max 1 X + max 1 X⁻¹ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, hs_re]
      by_cases h1 : 1 ≤ X
      · have h2 : X ^ x ≤ X := by
          calc X ^ x ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hx2
            _ = X := Real.rpow_one X
        have h3 : X ≤ max 1 X + max 1 X⁻¹ := by
          have h4 : X ≤ max 1 X := le_max_right _ _
          have h5 : 0 ≤ max 1 X⁻¹ := le_trans zero_le_one (le_max_left _ _)
          linarith
        exact le_trans h2 h3
      · have hXle : X ≤ 1 := le_of_lt (not_le.mp h1)
        have h2 : X ^ x ≤ X⁻¹ := by
          have ha : X ^ x ≤ X ^ c₁ := Real.rpow_le_rpow_of_exponent_ge hX hXle hcx
          have hb : X ^ c₁ ≤ X ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hX hXle hc₁ge
          calc X ^ x ≤ X ^ c₁ := ha
            _ ≤ X ^ (-1 : ℝ) := hb
            _ = X⁻¹ := Real.rpow_neg_one X
        have h5 : X⁻¹ ≤ max 1 X + max 1 X⁻¹ := by
          have h6 : X⁻¹ ≤ max 1 X⁻¹ := le_max_right _ _
          have h7 : 0 ≤ max 1 X := le_trans zero_le_one (le_max_left _ _)
          linarith
        exact le_trans h2 h5
    have hYb : ‖(Y : ℂ) ^ s‖ ≤ max 1 Y + max 1 Y⁻¹ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hY, hs_re]
      by_cases h1 : 1 ≤ Y
      · have h2 : Y ^ x ≤ Y := by
          calc Y ^ x ≤ Y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 hx2
            _ = Y := Real.rpow_one Y
        have h3 : Y ≤ max 1 Y + max 1 Y⁻¹ := by
          have h4 : Y ≤ max 1 Y := le_max_right _ _
          have h5 : 0 ≤ max 1 Y⁻¹ := le_trans zero_le_one (le_max_left _ _)
          linarith
        exact le_trans h2 h3
      · have hYle : Y ≤ 1 := le_of_lt (not_le.mp h1)
        have h2 : Y ^ x ≤ Y⁻¹ := by
          have ha : Y ^ x ≤ Y ^ c₁ := Real.rpow_le_rpow_of_exponent_ge hY hYle hcx
          have hb : Y ^ c₁ ≤ Y ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hY hYle hc₁ge
          calc Y ^ x ≤ Y ^ c₁ := ha
            _ ≤ Y ^ (-1 : ℝ) := hb
            _ = Y⁻¹ := Real.rpow_neg_one Y
        have h5 : Y⁻¹ ≤ max 1 Y + max 1 Y⁻¹ := by
          have h6 : Y⁻¹ ≤ max 1 Y⁻¹ := le_max_right _ _
          have h7 : 0 ≤ max 1 Y := le_trans zero_le_one (le_max_left _ _)
          linarith
        exact le_trans h2 h5
    have hsub : ‖(X : ℂ) ^ s - (Y : ℂ) ^ s‖
        ≤ (max 1 X + max 1 X⁻¹) + (max 1 Y + max 1 Y⁻¹) :=
      le_trans (norm_sub_le _ _) (add_le_add hXb hYb)
    have hLedge : ‖DirichletCharacter.LFunction χ (σ + s)‖ ≤ CL * (3 + |σ.im|) * T := by
      have hre : (σ + s).re = σ.re + x := by rw [Complex.add_re, hs_re]
      have him : (σ + s).im = σ.im + ε * T := by rw [Complex.add_im, hs_im]
      have hsplit : σ + s = ((σ.re + x : ℝ) : ℂ) + ((σ.im + ε * T : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [hre, him]
      rw [hsplit]
      have hb := hLunif (σ.re + x) (σ.im + ε * T) hxl (by linarith)
      refine le_trans hb ?_
      have h2 : (2 : ℝ) + |σ.im + ε * T| ≤ (3 + |σ.im|) * T := by
        have hab := abs_add_le σ.im (ε * T)
        rw [hεT] at hab
        nlinarith [abs_nonneg σ.im, hT]
      calc CL * (2 + |σ.im + ε * T|) ≤ CL * ((3 + |σ.im|) * T) :=
            mul_le_mul_of_nonneg_left h2 hCL0.le
        _ = CL * (3 + |σ.im|) * T := by ring
    have hFb : ‖lcmF q U V W χ (σ + s)‖ ≤ DF := by
      have hre : 1 - (k : ℝ)⁻¹ ≤ (σ + s).re := by
        have hh : (σ + s).re = σ.re + x := by rw [Complex.add_re, hs_re]
        rw [hh]; exact hxl
      have := norm_lcmF_le_gen q hU hUV hV hW χ (k := k) (by omega) hre
      simpa [hDFdef] using this
    rw [Ptw_eq_naive q U V W X Y χ σ s hs_ne]
    have hnorm : ‖Complex.Gamma s * ((X : ℂ) ^ s - (Y : ℂ) ^ s)
          * DirichletCharacter.LFunction χ (σ + s) * lcmF q U V W χ (σ + s)‖
        = ‖Complex.Gamma s‖ * ‖(X : ℂ) ^ s - (Y : ℂ) ^ s‖
          * ‖DirichletCharacter.LFunction χ (σ + s)‖ * ‖lcmF q U V W χ (σ + s)‖ := by
      simp only [norm_mul]
    rw [hnorm]
    have hpk0 : 0 ≤ Cg * (1 + T) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi / 2 * T)) * T⁻¹ := by
      positivity
    have hbnorm := mul_le_mul (mul_le_mul hΓb hsub (norm_nonneg _) hpk0) hLedge (norm_nonneg _)
      (by positivity : 0 ≤ Cg * (1 + T) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi / 2 * T)) * T⁻¹
        * (max 1 X + max 1 X⁻¹ + (max 1 Y + max 1 Y⁻¹)))
    have hstep : ‖Complex.Gamma s‖ * ‖(X : ℂ) ^ s - (Y : ℂ) ^ s‖
          * ‖DirichletCharacter.LFunction χ (σ + s)‖ * ‖lcmF q U V W χ (σ + s)‖
        ≤ (Cg * (1 + T) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi / 2 * T)) * T⁻¹
            * (max 1 X + max 1 X⁻¹ + (max 1 Y + max 1 Y⁻¹)))
          * (CL * (3 + |σ.im|) * T) * DF := by
      calc ‖Complex.Gamma s‖ * ‖(X : ℂ) ^ s - (Y : ℂ) ^ s‖
            * ‖DirichletCharacter.LFunction χ (σ + s)‖ * ‖lcmF q U V W χ (σ + s)‖
          = (‖Complex.Gamma s‖ * ‖(X : ℂ) ^ s - (Y : ℂ) ^ s‖
              * ‖DirichletCharacter.LFunction χ (σ + s)‖) * ‖lcmF q U V W χ (σ + s)‖ := by ring
        _ ≤ ((Cg * (1 + T) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi / 2 * T)) * T⁻¹
              * (max 1 X + max 1 X⁻¹ + (max 1 Y + max 1 Y⁻¹)))
              * (CL * (3 + |σ.im|) * T)) * DF :=
            mul_le_mul hbnorm hFb (norm_nonneg _) (by positivity)
        _ = (Cg * (1 + T) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi / 2 * T)) * T⁻¹
              * (max 1 X + max 1 X⁻¹ + (max 1 Y + max 1 Y⁻¹)))
              * (CL * (3 + |σ.im|) * T) * DF := by ring
    have hfin : (Cg * (1 + T) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi / 2 * T)) * T⁻¹
            * (max 1 X + max 1 X⁻¹ + (max 1 Y + max 1 Y⁻¹)))
          * (CL * (3 + |σ.im|) * T) * DF
        ≤ (Cg * 4 * (max 1 X + max 1 X⁻¹ + (max 1 Y + max 1 Y⁻¹)) * CL * (3 + |σ.im|) * DF + 1)
            * Real.exp (-(Real.pi / 2 * T)) * T ^ 4 := by
      have hexp0 : 0 ≤ Real.exp (-(Real.pi / 2 * T)) := (Real.exp_pos _).le
      have hT2 : (1 + T) ^ (3 / 2 : ℝ) ≤ 4 * T ^ (4 : ℕ) := by
        have h1 : (1 + T) ^ (3 / 2 : ℝ) ≤ (1 + T) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
        have h2 : (1 + T) ^ (2 : ℝ) = (1 + T) ^ (2 : ℕ) := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        have h3 : (1 + T) ^ (2 : ℕ) ≤ (2 * T) ^ (2 : ℕ) := by nlinarith
        have h4 : (2 * T) ^ (2 : ℕ) = 4 * T ^ 2 := by ring
        have h5 : T ^ 2 ≤ T ^ (4 : ℕ) := pow_le_pow_right₀ hT (by norm_num)
        calc (1 + T) ^ (3 / 2 : ℝ) ≤ (1 + T) ^ (2 : ℝ) := h1
          _ = (1 + T) ^ (2 : ℕ) := h2
          _ ≤ (2 * T) ^ (2 : ℕ) := h3
          _ = 4 * T ^ 2 := h4
          _ ≤ 4 * T ^ (4 : ℕ) := by linarith
      have hkey : Cg * (1 + T) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi / 2 * T)) * T⁻¹
              * (max 1 X + max 1 X⁻¹ + (max 1 Y + max 1 Y⁻¹))
            * (CL * (3 + |σ.im|) * T) * DF
          = Cg * (max 1 X + max 1 X⁻¹ + (max 1 Y + max 1 Y⁻¹)) * CL * (3 + |σ.im|) * DF
            * Real.exp (-(Real.pi / 2 * T))
            * ((1 + T) ^ (3 / 2 : ℝ) * (T⁻¹ * T)) := by ring
      rw [hkey, inv_mul_cancel₀ (ne_of_gt hT0), mul_one]
      have hA0 : 0 ≤ Cg * (max 1 X + max 1 X⁻¹ + (max 1 Y + max 1 Y⁻¹)) * CL * (3 + |σ.im|) * DF := by
        positivity
      have hAe : 0 ≤ Cg * (max 1 X + max 1 X⁻¹ + (max 1 Y + max 1 Y⁻¹)) * CL * (3 + |σ.im|) * DF
          * Real.exp (-(Real.pi / 2 * T)) := mul_nonneg hA0 hexp0
      calc Cg * (max 1 X + max 1 X⁻¹ + (max 1 Y + max 1 Y⁻¹)) * CL * (3 + |σ.im|) * DF
            * Real.exp (-(Real.pi / 2 * T)) * (1 + T) ^ (3 / 2 : ℝ)
          ≤ Cg * (max 1 X + max 1 X⁻¹ + (max 1 Y + max 1 Y⁻¹)) * CL * (3 + |σ.im|) * DF
            * Real.exp (-(Real.pi / 2 * T)) * (4 * T ^ (4 : ℕ)) :=
            mul_le_mul_of_nonneg_left hT2 hAe
        _ = 4 * (Cg * (max 1 X + max 1 X⁻¹ + (max 1 Y + max 1 Y⁻¹)) * CL * (3 + |σ.im|) * DF)
            * Real.exp (-(Real.pi / 2 * T)) * T ^ 4 := by ring
        _ ≤ (Cg * 4 * (max 1 X + max 1 X⁻¹ + (max 1 Y + max 1 Y⁻¹)) * CL * (3 + |σ.im|) * DF + 1)
            * Real.exp (-(Real.pi / 2 * T)) * T ^ 4 := by
            have hT4 : 0 ≤ T ^ (4 : ℕ) := by positivity
            nlinarith [hA0, hexp0, hT4]
    calc ‖Complex.Gamma s‖ * ‖(X : ℂ) ^ s - (Y : ℂ) ^ s‖
          * ‖DirichletCharacter.LFunction χ (σ + s)‖ * ‖lcmF q U V W χ (σ + s)‖
        ≤ (Cg * (1 + T) ^ (3 / 2 : ℝ) * Real.exp (-(Real.pi / 2 * T)) * T⁻¹
            * (max 1 X + max 1 X⁻¹ + (max 1 Y + max 1 Y⁻¹)))
          * (CL * (3 + |σ.im|) * T) * DF := hstep
      _ ≤ (Cg * 4 * (max 1 X + max 1 X⁻¹ + (max 1 Y + max 1 Y⁻¹)) * CL * (3 + |σ.im|) * DF + 1)
            * Real.exp (-(Real.pi / 2 * T)) * T ^ 4 := hfin
  constructor
  · have h := key 1 (Or.inl rfl)
    have h' : (↑x : ℂ) + ((1 : ℝ) : ℂ) * (T : ℂ) * Complex.I
        = (↑x : ℂ) + (T : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h'] at h
    exact h
  · have h := key (-1) (Or.inr rfl)
    have h' : (↑x : ℂ) + ((-1 : ℝ) : ℂ) * (T : ℂ) * Complex.I
        = (↑x : ℂ) - (T : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h'] at h
    exact h

/-- The two horizontal-edge integrals of the contour shift tend to `0`. -/
lemma Ptw_edge_tendsto (h1 : Work.LinnikContract2.Area1) (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    {U V W X Y : ℝ} (hU : 0 < U) (hUV : U ≤ V) (hV : 1 ≤ V) (hW : 1 ≤ W) (hX : 0 < X)
    (hY : 0 < Y) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (σ : ℂ) (hσ0 : 0 < σ.re)
    (hσ1 : σ.re ≤ 1) {k : ℕ} (hk : 3 ≤ k) {c₁ : ℝ} (hc₁ : c₁ = 1 - σ.re - (k : ℝ)⁻¹)
    (hc₁le : c₁ ≤ 1) :
    (Tendsto (fun R : ℝ => ∫ x in c₁..1, Ptw q U V W X Y χ σ ((x : ℂ) + (R : ℂ) * Complex.I))
        atTop (𝓝 0)) ∧
    (Tendsto (fun R : ℝ => ∫ x in c₁..1, Ptw q U V W X Y χ σ ((x : ℂ) - (R : ℂ) * Complex.I))
        atTop (𝓝 0)) := by
  obtain ⟨C, hCpos, hbd⟩ := norm_Ptw_edge h1 q hq hU hUV hV hW hX hY χ hχ σ hσ0 hσ1 hk hc₁
  have hlim : Tendsto (fun R : ℝ =>
      C * (1 - c₁) * (Real.exp (-(Real.pi / 2 * R)) * R ^ 4)) atTop (𝓝 0) := by
    have h0 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 : ℝ) (Real.pi / 2) (by positivity)
    have h2 : Tendsto (fun R : ℝ => Real.exp (-(Real.pi / 2 * R)) * R ^ 4) atTop (𝓝 0) := by
      simpa [mul_comm, Real.rpow_natCast] using h0
    simpa using h2.const_mul (C * (1 - c₁))
  have habs : |1 - c₁| = 1 - c₁ := abs_of_nonneg (by linarith)
  constructor
  · refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hb : ∀ x ∈ Set.Icc c₁ 1,
        ‖Ptw q U V W X Y χ σ ((x : ℂ) + (R : ℂ) * Complex.I)‖
          ≤ C * Real.exp (-(Real.pi / 2 * R)) * R ^ 4 :=
      fun x hx => (hbd x hx R hR).1
    calc ‖∫ x in c₁..1, Ptw q U V W X Y χ σ ((x : ℂ) + (R : ℂ) * Complex.I)‖
        ≤ (C * Real.exp (-(Real.pi / 2 * R)) * R ^ 4) * |1 - c₁| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => by
            rw [Set.uIoc_of_le hc₁le] at hx
            exact hb x ⟨hx.1.le, hx.2⟩)
      _ = C * (1 - c₁) * (Real.exp (-(Real.pi / 2 * R)) * R ^ 4) := by
          rw [habs]; ring
  · refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hb : ∀ x ∈ Set.Icc c₁ 1,
        ‖Ptw q U V W X Y χ σ ((x : ℂ) - (R : ℂ) * Complex.I)‖
          ≤ C * Real.exp (-(Real.pi / 2 * R)) * R ^ 4 :=
      fun x hx => (hbd x hx R hR).2
    calc ‖∫ x in c₁..1, Ptw q U V W X Y χ σ ((x : ℂ) - (R : ℂ) * Complex.I)‖
        ≤ (C * Real.exp (-(Real.pi / 2 * R)) * R ^ 4) * |1 - c₁| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => by
            rw [Set.uIoc_of_le hc₁le] at hx
            exact hb x ⟨hx.1.le, hx.2⟩)
      _ = C * (1 - c₁) * (Real.exp (-(Real.pi / 2 * R)) * R ^ 4) := by
          rw [habs]; ring

/-! ## The contour shift -/

/-- **HB (11.16), contour shift.**  The `Re s = 1` integral of the (difference) kernel equals its
`Re s = c₁ = 1 - σ.re - 1/k` integral, because the kernel is holomorphic on the strip
`-1 < Re s ≤ 1` (the two `Γ`-poles at the origin cancel) and the horizontal edges vanish. -/
theorem Ssm_sub_eq_Ptw_shifted (h1 : Work.LinnikContract2.Area1) (q : ℕ) [NeZero q] (hq : 3 ≤ q)
    (U V W X Y : ℝ) (χ : DirichletCharacter ℂ q) (σ : ℂ) (hU : 0 < U) (hUV : U ≤ V) (hW : 1 ≤ W)
    (hV : 1 ≤ V) (hX : 0 < X) (hY : 0 < Y) (hχ : χ ≠ 1) (hσ : 0 < σ.re) (hσ1 : σ.re ≤ 1)
    {k : ℕ} (hk : 3 ≤ k) {Cb c₁ : ℝ} (hCb : 0 < Cb)
    (hc₁ : c₁ = 1 - σ.re - (k : ℝ)⁻¹) (hc₁neg : c₁ < 0)
    (hLbd : ∀ t : ℝ, ‖DirichletCharacter.LFunction χ (σ + ((c₁ : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ Cb * (2 + |t|)) :
    Ssm q U V W X χ σ - Ssm q U V W Y χ σ
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, Ptw q U V W X Y χ σ ((c₁ : ℂ) + (t : ℂ) * Complex.I) := by
  have hk1 : 1 ≤ k := by omega
  have hkinv : (k : ℝ)⁻¹ ≤ 1 / 3 := by
    have h : (1 : ℝ) / (k : ℝ) ≤ 1 / 3 :=
      one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast (show 3 ≤ k by omega))
    simpa [one_div] using h
  have hc₁gt : -1 < c₁ := by rw [hc₁]; linarith
  have hc₁le : c₁ ≤ 1 := by rw [hc₁]; linarith
  rw [Ssm_sub_eq_Ptw_line q (by omega) U V W X Y χ σ hU hUV hW hV hX hY hχ hσ]
  congr 1
  have hFd : ∀ R : ℝ, DifferentiableOn ℂ (Ptw q U V W X Y χ σ)
      (Set.uIcc c₁ 1 ×ℂ Set.uIcc (-R) R) := by
    intro R
    refine (differentiableOn_Ptw q U V W X Y χ hχ (by linarith) (by linarith) σ).mono ?_
    rintro s ⟨hs1, _⟩
    simp only [Set.mem_setOf_eq]
    rw [Set.uIcc_of_le hc₁le] at hs1
    linarith [hs1.1]
  have hIp := integrable_Ptw_line_shifted (X := X) (Y := Y) q hU hUV hV hW (by linarith) (by linarith)
    χ hχ σ hk1 hCb hc₁ hc₁gt hc₁neg hLbd
  have hIq := integrable_Ptw_line_one (X := X) (Y := Y) q (by omega) hU hUV hW hV (by linarith)
    (by linarith) χ hχ σ hσ
  obtain ⟨htop, hbot⟩ := Ptw_edge_tendsto h1 q hq hU hUV hV hW hX hY χ hχ σ hσ hσ1 hk hc₁ hc₁le
  exact Commons.Analysis.Complex.vertical_contour_shift (Ptw q U V W X Y χ σ) c₁ 1 hc₁le hFd
    hIp hIq htop hbot

/-! ## The integral of `Gamma` on a shifted line -/

/-- `∫ ‖Γ(c+it)‖(2+|t|)` on a line `-1/2 < c < 0` with `|c| ≥ 1/(2k)` is at most `2k` times the
corresponding integral on `Re = c + 1 > 0`. -/
lemma gamma_integral_neg_le (k : ℕ) (hk : 1 ≤ k) {c CΓ : ℝ} (hc1 : -(1 / 2 : ℝ) < c)
    (hc2 : c < 0) (hc3 : (2 * (k : ℝ))⁻¹ ≤ |c|)
    (hΓ : ∀ a : ℝ, 1 / 2 ≤ a → a ≤ 2 →
      ∫ t : ℝ, ‖Complex.Gamma ((a : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) ≤ CΓ) :
    ∫ t : ℝ, ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) ≤ 2 * (k : ℝ) * CΓ := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hcne : c ≠ 0 := ne_of_lt hc2
  have hcabs : 0 < |c| := abs_pos.mpr hcne
  have h2k : (0 : ℝ) < 2 * (k : ℝ) := by positivity
  have hpt : ∀ t : ℝ, ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|)
      ≤ 2 * (k : ℝ) * (‖Complex.Gamma ((((c + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖
          * (2 + |t|)) := by
    intro t
    set s : ℂ := (c : ℂ) + (t : ℂ) * Complex.I with hsdef
    have hsne : s ≠ 0 := by
      intro h0
      have h1 := congrArg Complex.re h0
      simp at h1
      have h2 : s.re = c := by simp [hsdef]
      rw [h2] at h1
      exact hcne h1
    have hnorm : |c| ≤ ‖s‖ := by
      have h := Complex.abs_re_le_norm s
      simpa [hsdef] using h
    have hinvs : (‖s‖)⁻¹ ≤ 2 * (k : ℝ) := by
      have h1 : (‖s‖)⁻¹ ≤ (|c|)⁻¹ := by
        rw [inv_le_inv₀ (by positivity) hcabs]
        exact hnorm
      have h2 : (|c|)⁻¹ ≤ 2 * (k : ℝ) := (inv_le_comm₀ h2k hcabs).mp hc3
      linarith
    have hsplit : Complex.Gamma s = Complex.Gamma (s + 1) / s := by
      rw [Complex.Gamma_add_one s hsne]; field_simp
    have harg : s + 1 = (((c + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by
      rw [hsdef]; push_cast; ring
    have hΓ1 : ‖Complex.Gamma s‖ ≤ 2 * (k : ℝ)
        * ‖Complex.Gamma ((((c + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ := by
      calc ‖Complex.Gamma s‖ = ‖Complex.Gamma (s + 1)‖ * (‖s‖)⁻¹ := by
            rw [hsplit, norm_div, div_eq_mul_inv]
        _ ≤ ‖Complex.Gamma (s + 1)‖ * (2 * (k : ℝ)) :=
            mul_le_mul_of_nonneg_left hinvs (norm_nonneg _)
        _ = 2 * (k : ℝ) * ‖Complex.Gamma ((((c + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ := by
            rw [harg]; ring
    have h2t : 0 ≤ 2 + |t| := by positivity
    calc ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|)
        = ‖Complex.Gamma s‖ * (2 + |t|) := by rw [hsdef]
      _ ≤ (2 * (k : ℝ) * ‖Complex.Gamma ((((c + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖)
            * (2 + |t|) := mul_le_mul_of_nonneg_right hΓ1 h2t
      _ = 2 * (k : ℝ) * (‖Complex.Gamma ((((c + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖
            * (2 + |t|)) := by ring
  have hmaj : Integrable (fun t : ℝ => 2 * (k : ℝ)
      * (‖Complex.Gamma ((((c + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|))) :=
    (integrable_gamma_line_mul (c + 1) (by linarith)).const_mul _
  have hlhs : Integrable (fun t : ℝ =>
      ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|)) :=
    integrable_gamma_line_neg (by linarith) hc2
  calc ∫ t : ℝ, ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|)
      ≤ ∫ t : ℝ, 2 * (k : ℝ)
          * (‖Complex.Gamma ((((c + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|)) :=
        integral_mono_ae hlhs hmaj (Eventually.of_forall hpt)
    _ = 2 * (k : ℝ) * ∫ t : ℝ,
          ‖Complex.Gamma ((((c + 1 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) :=
        integral_const_mul _ _
    _ ≤ 2 * (k : ℝ) * CΓ :=
        mul_le_mul_of_nonneg_left (hΓ (c + 1) (by linarith) (by linarith)) (by positivity)
/-! ## The main (large `q`) case -/

/-- **HB (11.16), main case.**  For every fixed tuple `0 < w`, `w < u < x` with `2w + 1/3 < u`
there is `C > 0` and a threshold `Q` beyond which the difference of the two cut-off smoothed sums
of the mollified coefficient is `≤ C/log q`. -/
theorem Ssm_diff_bound (h1 : Work.LinnikContract2.Area1) (u w x : ℝ) (hw : 0 < w) (hwu : w < u)
    (hux : u < x) (h2w : 2 * w + 1 / 3 < u) :
    ∃ C : ℝ, 0 < C ∧ ∃ Q : ℕ, ∀ (q : ℕ) [NeZero q], Q ≤ q → ∀ (ψ : DirichletCharacter ℂ q),
      ψ ≠ 1 → ∀ (σ : ℂ), σ.re ≤ 1 → |σ.im| ≤ 2 →
      (1 - σ.re) * Real.log q ≤ 2 * Work.LinnikContract2.lamMax q →
      ‖Ssm q 1 ((q : ℝ) ^ w) ((q : ℝ) ^ w) ((q : ℝ) ^ x) ψ σ
        - Ssm q 1 ((q : ℝ) ^ w) ((q : ℝ) ^ w) (((q : ℝ) ^ u) / (Real.log q) ^ 2) ψ σ‖
        ≤ C / Real.log q := by
  -- ### the parameters
  set δ : ℝ := u - 2 * w - 1 / 3 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hkexists : ∃ k : ℕ, 3 ≤ k ∧ 2 < δ * (k : ℝ) := by
    refine ⟨max 3 (Nat.floor (2 / δ) + 1), le_max_left _ _, ?_⟩
    have h1' : 2 / δ < (Nat.floor (2 / δ) : ℝ) + 1 := Nat.lt_floor_add_one (2 / δ)
    have h2' : ((Nat.floor (2 / δ) : ℕ) : ℝ) + 1
        ≤ ((max 3 (Nat.floor (2 / δ) + 1) : ℕ) : ℝ) := by
      have hh : Nat.floor (2 / δ) + 1 ≤ max 3 (Nat.floor (2 / δ) + 1) := le_max_right _ _
      exact_mod_cast hh
    have h3' : 2 / δ < ((max 3 (Nat.floor (2 / δ) + 1) : ℕ) : ℝ) := lt_of_lt_of_le h1' h2'
    rw [div_lt_iff₀ hδpos] at h3'
    linarith
  obtain ⟨k, hk3, hkδ⟩ := hkexists
  have hk1 : 1 ≤ k := by omega
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk3R : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
  have he : 0 < δ / (2 * (k : ℝ)) := by positivity
  have hek : δ / (2 * (k : ℝ)) + 1 / (3 * ((k : ℝ)) ^ 2) < δ / (k : ℝ) := by
    have h2 : δ / (2 * (k : ℝ)) + 1 / (3 * ((k : ℝ)) ^ 2)
        = (3 * δ * (k : ℝ) + 2) / (6 * ((k : ℝ)) ^ 2) := by
      field_simp; ring
    have h3 : δ / (k : ℝ) = (6 * δ * (k : ℝ)) / (6 * ((k : ℝ)) ^ 2) := by field_simp
    rw [h2, h3, div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 6 * ((k : ℝ)) ^ 2)]
    nlinarith [hkδ, hδpos]
  obtain ⟨Cb0, hCb0pos, hCb0⟩ := LFunction_line_bound h1 k hk3 he
  obtain ⟨CΓ, hCΓpos, hCΓ⟩ := Gamma_line_integral_bound
  have hx0 : 0 ≤ x := by linarith
  have hu0 : 0 ≤ u := by linarith
  obtain ⟨Cll, hCllpos, Qll, hCll⟩ :=
    exists_rpow_loglog_le_log_mul (2 * (max x u) / 3) (by positivity)
  obtain ⟨Ql, hQl⟩ := lamMax_div_log_small (1 / (4 * (k : ℝ)))
    (div_pos one_pos (by positivity))
  set E : ℝ := (1 / 3 : ℝ) * (1 / (k : ℝ)) * (1 + 1 / (k : ℝ)) + δ / (2 * (k : ℝ)) with hEdef
  set s0 : ℝ := 1 / (3 * ((k : ℝ)) ^ 2) + δ / (2 * (k : ℝ)) - δ / (k : ℝ) with hs0def
  have hs0neg : s0 < 0 := by rw [hs0def]; linarith [hek]
  obtain ⟨K, hKpos, Qa, hKa⟩ :=
    hb11_logpow_rpow_neg_threshold (C := 5) (by norm_num) (s := s0 / 2) (by linarith)
  refine ⟨4 * ((1 / (2 * Real.pi)) * Cb0 * (2 * (k : ℝ)) * CΓ * Cll * (1 + 2 * w) ^ 3) * K + 1,
    by positivity, max (max Qll Ql) (max Qa 16), ?_⟩
  intro q _ hqQ ψ hψ σ hσ1 hσim hσlam
  -- ### basic facts about `q`
  have hq16 : 16 ≤ q := le_trans (le_trans (le_max_right Qa 16) (le_max_right (max Qll Ql) (max Qa 16))) hqQ
  have hq3 : 3 ≤ q := by omega
  have hq2 : 2 ≤ q := by omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hL : 0 < Real.log q := Real.log_pos hq1
  have hL0 : (0 : ℝ) ≤ Real.log q := hL.le
  have hL1 : 1 ≤ Real.log q := by
    have h16 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
    have h3 : (1 : ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]; exact Real.exp_one_lt_three
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 3) h16
    linarith
  have hll1 : 1 ≤ Real.log (Real.log (q : ℝ)) := by
    have h16 : (16 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq16
    have hexp : Real.exp 1 ≤ Real.log (q : ℝ) := by
      have h1 : Real.exp 1 ≤ Real.log 16 := by
        have h16' : Real.log 16 = 4 * Real.log 2 := by
          rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
        rw [h16']
        nlinarith [Real.log_two_gt_d9, Real.exp_one_lt_d9]
      exact le_trans h1 (Real.log_le_log (by norm_num) h16)
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hllpos : 0 < Real.log (Real.log (q : ℝ)) := by linarith
  have hll0 : 0 ≤ Real.log (Real.log (q : ℝ)) := le_of_lt hllpos
  -- ### the threshold on `λ_max / L`
  have hQl' : (Real.log (Real.log (Real.log (q : ℝ))) / 3 + 1) / Real.log (q : ℝ)
      < 1 / (4 * (k : ℝ)) :=
    hQl q (le_trans (le_trans (le_max_right Qll Ql) (le_max_left (max Qll Ql) (max Qa 16))) hqQ)
  have hlamL : Work.LinnikContract2.lamMax q < (Real.log q) / (4 * (k : ℝ)) := by
    have h1 : Real.log (Real.log (Real.log (q : ℝ))) / 3 / Real.log (q : ℝ) < 1 / (4 * (k : ℝ)) := by
      have hle : Real.log (Real.log (Real.log (q : ℝ))) / 3 / Real.log (q : ℝ)
          ≤ (Real.log (Real.log (Real.log (q : ℝ))) / 3 + 1) / Real.log (q : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) hL0
      linarith [hle, hQl']
    have h2 : Work.LinnikContract2.lamMax q / Real.log q
        = Real.log (Real.log (Real.log (q : ℝ))) / 3 / Real.log (q : ℝ) := by
      rw [Work.LinnikContract2.lamMax]
    have h3 : Work.LinnikContract2.lamMax q / Real.log q < 1 / (4 * (k : ℝ)) := by
      rw [h2]; exact h1
    have h4 := (div_lt_iff₀ hL).mp h3
    calc Work.LinnikContract2.lamMax q < (1 / (4 * (k : ℝ))) * Real.log q := h4
      _ = (Real.log q) / (4 * (k : ℝ)) := by ring
  have h1mσ : 1 - σ.re ≤ 1 / (2 * (k : ℝ)) := by
    have h4 : (1 - σ.re) * Real.log q ≤ 2 * ((Real.log q) / (4 * (k : ℝ))) := by
      have := hσlam
      linarith [hlamL]
    have h5 : 2 * ((Real.log q) / (4 * (k : ℝ))) = Real.log q / (2 * (k : ℝ)) := by ring
    rw [h5] at h4
    have h6 := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ 1 / Real.log q)
    rw [show ((1 - σ.re) * Real.log q) * (1 / Real.log q) = 1 - σ.re by field_simp,
      show (Real.log q / (2 * (k : ℝ))) * (1 / Real.log q) = 1 / (2 * (k : ℝ)) by
        field_simp] at h6
    exact h6
  have hσ0 : 0 < σ.re := by
    have h6 : (1 : ℝ) / (2 * (k : ℝ)) ≤ 1 / 6 := by
      have hk3R : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk3
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith [h1mσ, h6]
  have h1mσ0 : 0 ≤ 1 - σ.re := by linarith
  -- ### the point `c₁`
  set c₁ : ℝ := 1 - σ.re - (k : ℝ)⁻¹ with hc₁def
  have hc₁ : c₁ = 1 - σ.re - (k : ℝ)⁻¹ := hc₁def
  have hkinv3 : 1 / (k : ℝ) ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hk3)
  have hkinv2s : 1 / (2 * (k : ℝ)) < 1 / (k : ℝ) := by
    rw [one_div, one_div]
    exact (inv_lt_inv₀ (by positivity) hkR).mpr (by linarith)
  have hkinv2 : 1 / (2 * (k : ℝ)) ≤ 1 / (k : ℝ) := hkinv2s.le
  have hck : (k : ℝ)⁻¹ = 1 / (k : ℝ) := (one_div _).symm
  have hc2k : (2 * (k : ℝ))⁻¹ = 1 / (2 * (k : ℝ)) := (one_div _).symm
  have hsum : 1 / (k : ℝ) = 1 / (2 * (k : ℝ)) + 1 / (2 * (k : ℝ)) := by
    field_simp; ring
  have hc₁neg : c₁ < 0 := by
    rw [hc₁, hck]
    linarith only [h1mσ, hsum, hkinv2s]
  have hc₁gt : -(1 / 2 : ℝ) < c₁ := by
    rw [hc₁, hck]
    linarith only [h1mσ0, hkinv3]
  have hc₁abs : (2 * (k : ℝ))⁻¹ ≤ |c₁| := by
    rw [abs_of_neg hc₁neg, hc₁, hck, hc2k]
    linarith only [h1mσ, hsum]
  -- ### the cut-offs
  have hW1 : 1 ≤ (q : ℝ) ^ w := Real.one_le_rpow (by linarith) hw.le
  have hX1 : 1 ≤ (q : ℝ) ^ x := Real.one_le_rpow (by linarith) (by linarith : 0 ≤ x)
  have hX0 : 0 < (q : ℝ) ^ x := Real.rpow_pos_of_pos hqpos x
  have hY0 : 0 < ((q : ℝ) ^ u) / (Real.log q) ^ 2 := div_pos (Real.rpow_pos_of_pos hqpos u)
    (by positivity)
  -- ### the shifted `L`-bound (Burgess at `Re = 1 - 1/k`)
  set Cb : ℝ := 2 * (Cb0 * (q : ℝ) ^ E) with hCbdef
  have hCbpos : 0 < Cb := by rw [hCbdef]; positivity
  have hLbd : ∀ t : ℝ, ‖DirichletCharacter.LFunction ψ
      (σ + ((c₁ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ Cb * (2 + |t|) := by
    intro t
    have hb := hCb0 q ψ hq3 hψ (1 - 1 / (k : ℝ)) (σ.im + t) le_rfl (by
      have hll : 0 ≤ Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) := div_nonneg hll0 hL0
      linarith)
    have hEeq : (1 / 3 : ℝ) * (1 - (1 - 1 / (k : ℝ))) * (1 + 1 / (k : ℝ)) + δ / (2 * (k : ℝ)) = E := by
      rw [hEdef]; ring
    rw [hEeq] at hb
    have harg : σ + ((c₁ : ℂ) + (t : ℂ) * Complex.I)
        = (((1 - 1 / (k : ℝ)) : ℝ) : ℂ) + (((σ.im + t) : ℝ) : ℂ) * Complex.I := by
      rw [hc₁]
      apply Complex.ext <;> simp <;> ring
    rw [harg]
    refine le_trans hb ?_
    have h2 : (1 : ℝ) + |σ.im + t| ≤ 2 * (2 + |t|) := by
      have h3 : |σ.im + t| ≤ |σ.im| + |t| := abs_add_le _ _
      linarith [hσim, abs_nonneg t]
    rw [hCbdef]
    have h4 : 0 ≤ Cb0 * (q : ℝ) ^ E := by positivity
    nlinarith [h2, h4]
  -- ### the shift and the integral bound
  have hshift := Ssm_sub_eq_Ptw_shifted h1 q hq3 1 ((q : ℝ) ^ w) ((q : ℝ) ^ w) ((q : ℝ) ^ x)
    (((q : ℝ) ^ u) / (Real.log q) ^ 2) ψ σ (by norm_num) hW1 hW1 hW1 hX0 hY0 hψ hσ0 hσ1 hk3
    hCbpos hc₁ hc₁neg hLbd
  set DF : ℝ := (((q : ℝ) ^ w) * ((q : ℝ) ^ w)) ^ (1 / (k : ℝ))
    * (1 + Real.log (((q : ℝ) ^ w) * ((q : ℝ) ^ w))) ^ 3 with hDFdef
  have hDF0 : 0 ≤ DF := by
    rw [hDFdef]
    refine mul_nonneg (Real.rpow_nonneg (by positivity) _) (pow_nonneg ?_ 3)
    have : (1 : ℝ) ≤ ((q : ℝ) ^ w) * ((q : ℝ) ^ w) := by nlinarith
    linarith [Real.log_nonneg this]
  have hDFb2 : DF ≤ (q : ℝ) ^ (2 * w / (k : ℝ)) * ((1 + 2 * w) ^ 3 * (Real.log q) ^ 3) := by
    have hWsq : ((q : ℝ) ^ w) * ((q : ℝ) ^ w) = (q : ℝ) ^ (2 * w) := by
      rw [← Real.rpow_add hqpos]; congr 1; ring
    have hlogW : Real.log (((q : ℝ) ^ w) * ((q : ℝ) ^ w)) = 2 * w * Real.log q := by
      rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hqpos w))
        (ne_of_gt (Real.rpow_pos_of_pos hqpos w)), Real.log_rpow hqpos]
      ring
    rw [hDFdef, hlogW, hWsq]
    have h1 : ((q : ℝ) ^ (2 * w)) ^ (1 / (k : ℝ)) = (q : ℝ) ^ (2 * w * (1 / (k : ℝ))) := by
      rw [← Real.rpow_mul hqpos.le]
    rw [h1]
    have h2 : 2 * w * (1 / (k : ℝ)) = 2 * w / (k : ℝ) := by ring
    rw [h2]
    have h3 : (1 + 2 * w * Real.log q) ^ 3 ≤ (1 + 2 * w) ^ 3 * (Real.log q) ^ 3 := by
      have h4 : 1 + 2 * w * Real.log q ≤ (1 + 2 * w) * Real.log q := by nlinarith [hw, hL1]
      have h5 : 0 ≤ 1 + 2 * w * Real.log q := by positivity
      calc (1 + 2 * w * Real.log q) ^ 3 ≤ ((1 + 2 * w) * Real.log q) ^ 3 :=
            pow_le_pow_left₀ h5 h4 3
        _ = (1 + 2 * w) ^ 3 * (Real.log q) ^ 3 := by rw [mul_pow]
    exact mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hqpos.le _)
  have hint : ‖(1 / (2 * Real.pi)) * ∫ t : ℝ, Ptw q 1 ((q : ℝ) ^ w) ((q : ℝ) ^ w)
        ((q : ℝ) ^ x) (((q : ℝ) ^ u) / (Real.log q) ^ 2) ψ σ ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ (1 / (2 * Real.pi)) * (Cb
          * ((((q : ℝ) ^ x) ^ c₁ + (((q : ℝ) ^ u) / (Real.log q) ^ 2) ^ c₁) * DF)
          * (2 * (k : ℝ) * CΓ)) := by
    have hpt := norm_Ptw_shifted_pointwise q (by norm_num : (0:ℝ) < 1) hW1 hW1 hW1 hX0 hY0 ψ hψ
      σ hk1 hCbpos hc₁ hc₁neg hLbd
    set KK : ℝ := Cb * ((((q : ℝ) ^ x) ^ c₁ + (((q : ℝ) ^ u) / (Real.log q) ^ 2) ^ c₁) * DF)
      with hKKdef
    have hKK0 : 0 ≤ KK := by rw [hKKdef]; positivity
    have hmaj : Integrable (fun t : ℝ => KK * (‖Complex.Gamma ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖
        * (2 + |t|))) := (integrable_gamma_line_neg (by linarith) hc₁neg).const_mul KK
    have hint1 : ‖∫ t : ℝ, Ptw q 1 ((q : ℝ) ^ w) ((q : ℝ) ^ w) ((q : ℝ) ^ x)
        (((q : ℝ) ^ u) / (Real.log q) ^ 2) ψ σ ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ KK * ∫ t : ℝ, ‖Complex.Gamma ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) := by
      have hmono : (fun t : ℝ => ‖Ptw q 1 ((q : ℝ) ^ w) ((q : ℝ) ^ w) ((q : ℝ) ^ x)
          (((q : ℝ) ^ u) / (Real.log q) ^ 2) ψ σ ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖)
          ≤ (fun t : ℝ => KK * (‖Complex.Gamma ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|))) := by
        intro t
        have h1 := hpt t
        rw [hKKdef]
        calc ‖Ptw q 1 ((q : ℝ) ^ w) ((q : ℝ) ^ w) ((q : ℝ) ^ x)
              (((q : ℝ) ^ u) / (Real.log q) ^ 2) ψ σ ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖
            ≤ Cb * (2 + |t|) * ‖Complex.Gamma ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖
              * ((((q : ℝ) ^ x) ^ c₁ + (((q : ℝ) ^ u) / (Real.log q) ^ 2) ^ c₁)
                * ((((q : ℝ) ^ w) * ((q : ℝ) ^ w)) ^ (1 / (k : ℝ))
                  * (1 + Real.log (((q : ℝ) ^ w) * ((q : ℝ) ^ w))) ^ 3)) := h1
          _ = Cb * ((((q : ℝ) ^ x) ^ c₁ + (((q : ℝ) ^ u) / (Real.log q) ^ 2) ^ c₁)
                * ((((q : ℝ) ^ w) * ((q : ℝ) ^ w)) ^ (1 / (k : ℝ))
                  * (1 + Real.log (((q : ℝ) ^ w) * ((q : ℝ) ^ w))) ^ 3))
              * (‖Complex.Gamma ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|)) := by ring
      have hPtwin : Integrable (fun t : ℝ => Ptw q 1 ((q : ℝ) ^ w) ((q : ℝ) ^ w) ((q : ℝ) ^ x)
          (((q : ℝ) ^ u) / (Real.log q) ^ 2) ψ σ ((c₁ : ℂ) + (t : ℂ) * Complex.I)) :=
        integrable_Ptw_line_shifted (X := ((q:ℝ)^x)) (Y := ((q:ℝ)^u / (Real.log q)^2)) q
          (by norm_num) hW1 hW1 hW1 hX0 hY0 ψ hψ σ hk1 hCbpos hc₁ (by linarith : -1 < c₁) hc₁neg hLbd
      calc ‖∫ t : ℝ, Ptw q 1 ((q : ℝ) ^ w) ((q : ℝ) ^ w) ((q : ℝ) ^ x)
            (((q : ℝ) ^ u) / (Real.log q) ^ 2) ψ σ ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ ∫ t : ℝ, ‖Ptw q 1 ((q : ℝ) ^ w) ((q : ℝ) ^ w) ((q : ℝ) ^ x)
              (((q : ℝ) ^ u) / (Real.log q) ^ 2) ψ σ ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖ :=
            MeasureTheory.norm_integral_le_integral_norm _
        _ ≤ ∫ t : ℝ, KK * (‖Complex.Gamma ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|)) :=
            integral_mono (hPtwin.norm) hmaj hmono
        _ = KK * ∫ t : ℝ, ‖Complex.Gamma ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) :=
            integral_const_mul _ _
    have hΓi : ∫ t : ℝ, ‖Complex.Gamma ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|)
        ≤ 2 * (k : ℝ) * CΓ :=
      gamma_integral_neg_le k hk1 hc₁gt hc₁neg hc₁abs (fun a ha1 ha2 => hCΓ a ha1 ha2)
    have hnorm : ‖(1 / (2 * Real.pi)) * ∫ t : ℝ, Ptw q 1 ((q : ℝ) ^ w) ((q : ℝ) ^ w)
        ((q : ℝ) ^ x) (((q : ℝ) ^ u) / (Real.log q) ^ 2) ψ σ ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖
        = (1 / (2 * Real.pi)) * ‖∫ t : ℝ, Ptw q 1 ((q : ℝ) ^ w) ((q : ℝ) ^ w)
            ((q : ℝ) ^ x) (((q : ℝ) ^ u) / (Real.log q) ^ 2) ψ σ
            ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖ := by
      rw [norm_mul]
      congr 1
      have hgoal : ((1 / (2 * Real.pi) : ℝ) : ℂ) = 1 / (2 * (Real.pi : ℂ)) := by
        rw [Complex.ofReal_div (1:ℝ) (2*Real.pi), Complex.ofReal_mul (2:ℝ) Real.pi]
        norm_num
      have h1 : ‖(((1 / (2 * Real.pi) : ℝ)) : ℂ)‖ = |(1 / (2 * Real.pi) : ℝ)| :=
        RCLike.norm_ofReal (1 / (2 * Real.pi))
      rw [← hgoal, h1, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
    rw [hnorm]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
    calc ‖∫ t : ℝ, Ptw q 1 ((q : ℝ) ^ w) ((q : ℝ) ^ w) ((q : ℝ) ^ x)
          (((q : ℝ) ^ u) / (Real.log q) ^ 2) ψ σ ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ KK * ∫ t : ℝ, ‖Complex.Gamma ((c₁ : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) := hint1
      _ ≤ KK * (2 * (k : ℝ) * CΓ) := mul_le_mul_of_nonneg_left hΓi hKK0
      _ = Cb * ((((q : ℝ) ^ x) ^ c₁ + (((q : ℝ) ^ u) / (Real.log q) ^ 2) ^ c₁) * DF)
            * (2 * (k : ℝ) * CΓ) := by rw [hKKdef, hDFdef]

  -- ### the two cut-off contributions
  have hLLx : (q : ℝ) ^ (x * (1 - σ.re)) ≤ (Real.log (Real.log (q : ℝ))) ^ (2 * x / 3) := by
    rw [Real.rpow_def_of_pos hqpos, Real.rpow_def_of_pos hllpos]
    apply Real.exp_le_exp.mpr
    have hlam : (1 - σ.re) * Real.log q ≤ 2 * Work.LinnikContract2.lamMax q := hσlam
    calc Real.log (q : ℝ) * (x * (1 - σ.re)) = x * ((1 - σ.re) * Real.log (q : ℝ)) := by ring
      _ ≤ x * (2 * Work.LinnikContract2.lamMax q) := mul_le_mul_of_nonneg_left hlam (by linarith)
      _ = Real.log (Real.log (Real.log (q : ℝ))) * (2 * x / 3) := by
          rw [Work.LinnikContract2.lamMax]; ring
  have hLLu : (q : ℝ) ^ (u * (1 - σ.re)) ≤ (Real.log (Real.log (q : ℝ))) ^ (2 * u / 3) := by
    rw [Real.rpow_def_of_pos hqpos, Real.rpow_def_of_pos hllpos]
    apply Real.exp_le_exp.mpr
    have hlam : (1 - σ.re) * Real.log q ≤ 2 * Work.LinnikContract2.lamMax q := hσlam
    calc Real.log (q : ℝ) * (u * (1 - σ.re)) = u * ((1 - σ.re) * Real.log (q : ℝ)) := by ring
      _ ≤ u * (2 * Work.LinnikContract2.lamMax q) := mul_le_mul_of_nonneg_left hlam (by linarith)
      _ = Real.log (Real.log (Real.log (q : ℝ))) * (2 * u / 3) := by
          rw [Work.LinnikContract2.lamMax]; ring
  have hAX : ((q : ℝ) ^ x) ^ c₁
      ≤ (Real.log (Real.log (q : ℝ))) ^ (2 * x / 3) * (q : ℝ) ^ (-(x / (k : ℝ))) := by
    have hexp : x * c₁ = x * (1 - σ.re) + (-(x / (k : ℝ))) := by rw [hc₁]; ring_nf
    have heq : ((q : ℝ) ^ x) ^ c₁
        = (q : ℝ) ^ (x * (1 - σ.re)) * (q : ℝ) ^ (-(x / (k : ℝ))) := by
      rw [← Real.rpow_mul hqpos.le, hexp, Real.rpow_add hqpos]
    rw [heq]
    exact mul_le_mul_of_nonneg_right hLLx (Real.rpow_nonneg hqpos.le _)
  have hAY : (((q : ℝ) ^ u) / (Real.log q) ^ 2) ^ c₁
      ≤ (Real.log (Real.log (q : ℝ))) ^ (2 * u / 3) * (Real.log q) ^ (2 * (1 / (k : ℝ)))
        * (q : ℝ) ^ (-(u / (k : ℝ))) := by
    have hinvL : 0 < Real.log q := hL
    have e1 : (((q : ℝ) ^ u) / (Real.log q) ^ 2) ^ c₁
        = ((q : ℝ) ^ u) ^ c₁ / ((Real.log q) ^ 2) ^ c₁ :=
      Real.div_rpow (Real.rpow_pos_of_pos hqpos u).le (by positivity) c₁
    have e2 : ((q : ℝ) ^ u) ^ c₁ = (q : ℝ) ^ (u * c₁) := (Real.rpow_mul hqpos.le u c₁).symm
    have e3 : ((Real.log q) ^ 2) ^ c₁ = (Real.log q) ^ (2 * c₁) := by
      have hnat : ((Real.log q) ^ 2 : ℝ) = (Real.log q) ^ (2 : ℝ) :=
        (Real.rpow_natCast (Real.log q) 2).symm
      rw [hnat]
      exact (Real.rpow_mul hL0 2 c₁).symm
    have hexp : u * c₁ = u * (1 - σ.re) + (-(u / (k : ℝ))) := by rw [hc₁]; ring_nf
    have hexp2 : 2 * c₁ = -(2 * (1 / (k : ℝ))) + 2 * (1 - σ.re) := by rw [hc₁]; ring_nf
    have hden : ((Real.log q) ^ (-(2 * (1 / (k : ℝ))) + 2 * (1 - σ.re)))⁻¹
        ≤ (Real.log q) ^ (2 * (1 / (k : ℝ))) := by
      have h1 : ((Real.log q) ^ (-(2 * (1 / (k : ℝ))) + 2 * (1 - σ.re)))⁻¹
          = (Real.log q) ^ (2 * (1 / (k : ℝ)) - 2 * (1 - σ.re)) := by
        rw [← Real.rpow_neg hL0]; congr 1; ring
      rw [h1]
      refine Real.rpow_le_rpow_of_exponent_le hL1 ?_
      linarith [h1mσ0]
    rw [e1, e2, e3, hexp, hexp2, Real.rpow_add hqpos]
    rw [div_eq_mul_inv]
    calc (q : ℝ) ^ (u * (1 - σ.re)) * (q : ℝ) ^ (-(u / (k : ℝ)))
          * ((Real.log q) ^ (-(2 * (1 / (k : ℝ))) + 2 * (1 - σ.re)))⁻¹
        ≤ ((Real.log (Real.log (q : ℝ))) ^ (2 * u / 3) * (q : ℝ) ^ (-(u / (k : ℝ))))
          * ((Real.log q) ^ (2 * (1 / (k : ℝ)))) := by
          refine mul_le_mul ?_ hden (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hLLu (Real.rpow_nonneg hqpos.le _)
      _ = (Real.log (Real.log (q : ℝ))) ^ (2 * u / 3) * (Real.log q) ^ (2 * (1 / (k : ℝ)))
          * (q : ℝ) ^ (-(u / (k : ℝ))) := by ring

  -- ### the arithmetic closing
  have hexpu : E + 2 * w / (k : ℝ) - u / (k : ℝ) = s0 := by
    rw [hEdef, hs0def, hδdef]; field_simp; ring
  have hexpx : E + 2 * w / (k : ℝ) - x / (k : ℝ) ≤ s0 := by
    rw [← hexpu]
    have h2 : u / (k : ℝ) ≤ x / (k : ℝ) := by
      rw [div_le_div_iff_of_pos_right hkR]; exact hux.le
    linarith
  have hXx : (q : ℝ) ^ E * (q : ℝ) ^ (-(x / (k : ℝ))) * (q : ℝ) ^ (2 * w / (k : ℝ))
      ≤ (q : ℝ) ^ s0 := by
    rw [← Real.rpow_add hqpos, ← Real.rpow_add hqpos]
    refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
    linarith [hexpx]
  have hXu : (q : ℝ) ^ E * (q : ℝ) ^ (-(u / (k : ℝ))) * (q : ℝ) ^ (2 * w / (k : ℝ))
      ≤ (q : ℝ) ^ s0 := by
    rw [← Real.rpow_add hqpos, ← Real.rpow_add hqpos]
    refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
    linarith [hexpu]
  have hLk : (Real.log q) ^ (2 * (1 / (k : ℝ))) ≤ Real.log q := by
    have h1 : 2 * (1 / (k : ℝ)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]
      linarith [hk3R]
    have h2 := Real.rpow_le_rpow_of_exponent_le hL1 h1
    rwa [Real.rpow_one] at h2
  have hCllx : (Real.log (Real.log (q : ℝ))) ^ (2 * x / 3) ≤ Cll * Real.log q := by
    refine le_trans ?_ (hCll q (le_trans (le_trans (le_max_left Qll Ql)
      (le_max_left (max Qll Ql) (max Qa 16))) hqQ))
    refine Real.rpow_le_rpow_of_exponent_le hll1 ?_
    rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 3)]
    linarith [le_max_left x u]
  have hCllu : (Real.log (Real.log (q : ℝ))) ^ (2 * u / 3) ≤ Cll * Real.log q := by
    refine le_trans ?_ (hCll q (le_trans (le_trans (le_max_left Qll Ql)
      (le_max_left (max Qll Ql) (max Qa 16))) hqQ))
    refine Real.rpow_le_rpow_of_exponent_le hll1 ?_
    rw [div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 3)]
    linarith [le_max_right x u]
  have hS : ((q : ℝ) ^ x) ^ c₁ + (((q : ℝ) ^ u) / (Real.log q) ^ 2) ^ c₁
      ≤ Cll * Real.log q * (q : ℝ) ^ (-(x / (k : ℝ)))
        + Cll * Real.log q * Real.log q * (q : ℝ) ^ (-(u / (k : ℝ))) := by
    have hAx : ((q : ℝ) ^ x) ^ c₁ ≤ Cll * Real.log q * (q : ℝ) ^ (-(x / (k : ℝ))) := by
      refine le_trans hAX ?_
      exact mul_le_mul_of_nonneg_right hCllx (Real.rpow_nonneg hqpos.le _)
    have hAy : (((q : ℝ) ^ u) / (Real.log q) ^ 2) ^ c₁
        ≤ Cll * Real.log q * Real.log q * (q : ℝ) ^ (-(u / (k : ℝ))) := by
      refine le_trans hAY ?_
      calc (Real.log (Real.log (q : ℝ))) ^ (2 * u / 3) * (Real.log q) ^ (2 * (1 / (k : ℝ)))
            * (q : ℝ) ^ (-(u / (k : ℝ)))
          ≤ (Cll * Real.log q) * Real.log q * (q : ℝ) ^ (-(u / (k : ℝ))) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hqpos.le _)
            calc (Real.log (Real.log (q : ℝ))) ^ (2 * u / 3)
                  * (Real.log q) ^ (2 * (1 / (k : ℝ)))
                ≤ (Cll * Real.log q) * Real.log q :=
                  mul_le_mul hCllu hLk (by positivity) (by positivity)
              _ = Cll * Real.log q * Real.log q := by ring
        _ = Cll * Real.log q * Real.log q * (q : ℝ) ^ (-(u / (k : ℝ))) := by ring
    linarith
  have hmain : ‖Ssm q 1 ((q : ℝ) ^ w) ((q : ℝ) ^ w) ((q : ℝ) ^ x) ψ σ
        - Ssm q 1 ((q : ℝ) ^ w) ((q : ℝ) ^ w) (((q : ℝ) ^ u) / (Real.log q) ^ 2) ψ σ‖
      ≤ 4 * ((1 / (2 * Real.pi)) * Cb0 * (2 * (k : ℝ)) * CΓ * Cll * (1 + 2 * w) ^ 3)
          * (Real.log q) ^ 5 * (q : ℝ) ^ s0 := by
    rw [hshift]
    refine le_trans hint ?_
    rw [hCbdef]
    have hgoal : (1 / (2 * Real.pi)) * (2 * (Cb0 * (q : ℝ) ^ E)
          * ((((q : ℝ) ^ x) ^ c₁ + (((q : ℝ) ^ u) / (Real.log q) ^ 2) ^ c₁) * DF)
          * (2 * (k : ℝ) * CΓ))
        = (2 * ((1 / (2 * Real.pi)) * Cb0 * (2 * (k : ℝ) * CΓ)))
          * ((q : ℝ) ^ E
            * ((((q : ℝ) ^ x) ^ c₁ + (((q : ℝ) ^ u) / (Real.log q) ^ 2) ^ c₁) * DF)) := by
      ring
    rw [hgoal]
    have hX : (q : ℝ) ^ E
          * ((((q : ℝ) ^ x) ^ c₁ + (((q : ℝ) ^ u) / (Real.log q) ^ 2) ^ c₁) * DF)
        ≤ 2 * Cll * (1 + 2 * w) ^ 3 * (Real.log q) ^ 5 * (q : ℝ) ^ s0 := by
      set A : ℝ := (q : ℝ) ^ E with hA
      set Bx : ℝ := (q : ℝ) ^ (-(x / (k : ℝ))) with hBx
      set Bu : ℝ := (q : ℝ) ^ (-(u / (k : ℝ))) with hBu
      set Qw : ℝ := (q : ℝ) ^ (2 * w / (k : ℝ)) with hQw
      have hA0 : 0 ≤ A := by rw [hA]; positivity
      have hS1 : ((q : ℝ) ^ x) ^ c₁ + (((q : ℝ) ^ u) / (Real.log q) ^ 2) ^ c₁
          ≤ Cll * Real.log q * Bx + Cll * Real.log q * Real.log q * Bu := by
        rw [hBx, hBu]; exact hS
      have hDF1 : DF ≤ Qw * ((1 + 2 * w) ^ 3 * (Real.log q) ^ 3) := by rw [hQw]; exact hDFb2
      have hXx1 : A * Bx * Qw ≤ (q : ℝ) ^ s0 := by rw [hA, hBx, hQw]; exact hXx
      have hXu1 : A * Bu * Qw ≤ (q : ℝ) ^ s0 := by rw [hA, hBu, hQw]; exact hXu
      have hQw0 : 0 ≤ Qw := by rw [hQw]; positivity
      have step1 : A * ((((q : ℝ) ^ x) ^ c₁ + (((q : ℝ) ^ u) / (Real.log q) ^ 2) ^ c₁) * DF)
          ≤ A * ((Cll * Real.log q * Bx + Cll * Real.log q * Real.log q * Bu) * DF) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hS1 (by positivity)) hA0
      have step2 : A * ((Cll * Real.log q * Bx + Cll * Real.log q * Real.log q * Bu) * DF)
          ≤ A * ((Cll * Real.log q * Bx + Cll * Real.log q * Real.log q * Bu)
              * (Qw * ((1 + 2 * w) ^ 3 * (Real.log q) ^ 3))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hDF1 (by positivity)) hA0
      have step3 : A * ((Cll * Real.log q * Bx + Cll * Real.log q * Real.log q * Bu)
              * (Qw * ((1 + 2 * w) ^ 3 * (Real.log q) ^ 3)))
          = Cll * (1 + 2 * w) ^ 3 * (Real.log q) ^ 4
            * (A * Bx * Qw + Real.log q * (A * Bu * Qw)) := by
        ring
      rw [step3] at step2
      have step4 : Cll * (1 + 2 * w) ^ 3 * (Real.log q) ^ 4
            * (A * Bx * Qw + Real.log q * (A * Bu * Qw))
          ≤ Cll * (1 + 2 * w) ^ 3 * (Real.log q) ^ 4
            * ((q : ℝ) ^ s0 + Real.log q * (q : ℝ) ^ s0) := by
        have h0 : 0 ≤ Cll * (1 + 2 * w) ^ 3 * (Real.log q) ^ 4 := by positivity
        refine mul_le_mul_of_nonneg_left ?_ h0
        exact add_le_add hXx1 (mul_le_mul_of_nonneg_left hXu1 hL0)
      have step5 : Cll * (1 + 2 * w) ^ 3 * (Real.log q) ^ 4
            * ((q : ℝ) ^ s0 + Real.log q * (q : ℝ) ^ s0)
          ≤ 2 * Cll * (1 + 2 * w) ^ 3 * (Real.log q) ^ 5 * (q : ℝ) ^ s0 := by
        have h1 : (1 : ℝ) + Real.log q ≤ 2 * Real.log q := by linarith
        have h2 : 0 ≤ Cll * (1 + 2 * w) ^ 3 * (Real.log q) ^ 4 * (q : ℝ) ^ s0 := by positivity
        have h3 : 0 ≤ Real.log q := hL0
        nlinarith [h1, h2, h3, hCllpos.le, Real.rpow_nonneg hqpos.le s0,
          Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + 2 * w) 3]
      linarith [step1, step2, step4, step5]
    have hb1 : 0 ≤ (1 / (2 * Real.pi)) * Cb0 * (2 * (k : ℝ) * CΓ) := by positivity
    calc 2 * ((1 / (2 * Real.pi)) * Cb0 * (2 * (k : ℝ) * CΓ))
          * ((q : ℝ) ^ E
            * ((((q : ℝ) ^ x) ^ c₁ + (((q : ℝ) ^ u) / (Real.log q) ^ 2) ^ c₁) * DF))
        ≤ 2 * ((1 / (2 * Real.pi)) * Cb0 * (2 * (k : ℝ) * CΓ))
          * (2 * Cll * (1 + 2 * w) ^ 3 * (Real.log q) ^ 5 * (q : ℝ) ^ s0) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = 4 * ((1 / (2 * Real.pi)) * Cb0 * (2 * (k : ℝ)) * CΓ * Cll * (1 + 2 * w) ^ 3)
          * (Real.log q) ^ 5 * (q : ℝ) ^ s0 := by ring
  have hfinal : 4 * ((1 / (2 * Real.pi)) * Cb0 * (2 * (k : ℝ)) * CΓ * Cll * (1 + 2 * w) ^ 3)
      * (Real.log q) ^ 5 * (q : ℝ) ^ s0
      ≤ (4 * ((1 / (2 * Real.pi)) * Cb0 * (2 * (k : ℝ)) * CΓ * Cll * (1 + 2 * w) ^ 3) * K + 1)
        / Real.log q := by
    have hKa' := hKa q (le_trans (le_trans (le_max_left Qa 16) (le_max_right (max Qll Ql) (max Qa 16)))
      hqQ)
    have hKa'' : (Real.log q) ^ 5 * (q : ℝ) ^ (s0 / 2) ≤ K / Real.log q := by
      rw [← Real.rpow_natCast]
      exact hKa'
    have hqs : (q : ℝ) ^ s0 ≤ (q : ℝ) ^ (s0 / 2) := by
      refine Real.rpow_le_rpow_of_exponent_le (by linarith) ?_
      linarith [hs0neg]
    have hL5 : 0 ≤ (Real.log q) ^ 5 := by positivity
    have h1 : (Real.log q) ^ 5 * (q : ℝ) ^ s0 ≤ (Real.log q) ^ 5 * (q : ℝ) ^ (s0 / 2) :=
      mul_le_mul_of_nonneg_left hqs hL5
    have h2 : 4 * ((1 / (2 * Real.pi)) * Cb0 * (2 * (k : ℝ)) * CΓ * Cll * (1 + 2 * w) ^ 3)
        * ((Real.log q) ^ 5 * (q : ℝ) ^ s0)
        ≤ 4 * ((1 / (2 * Real.pi)) * Cb0 * (2 * (k : ℝ)) * CΓ * Cll * (1 + 2 * w) ^ 3)
          * (K / Real.log q) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact le_trans h1 hKa''
    have h3 : 4 * ((1 / (2 * Real.pi)) * Cb0 * (2 * (k : ℝ)) * CΓ * Cll * (1 + 2 * w) ^ 3)
        * (K / Real.log q)
        = 4 * ((1 / (2 * Real.pi)) * Cb0 * (2 * (k : ℝ)) * CΓ * Cll * (1 + 2 * w) ^ 3) * K
          / Real.log q := by ring
    have h4 : 4 * ((1 / (2 * Real.pi)) * Cb0 * (2 * (k : ℝ)) * CΓ * Cll * (1 + 2 * w) ^ 3) * K
        / Real.log q
        ≤ (4 * ((1 / (2 * Real.pi)) * Cb0 * (2 * (k : ℝ)) * CΓ * Cll * (1 + 2 * w) ^ 3) * K + 1)
          / Real.log q := by
      rw [div_le_div_iff_of_pos_right hL]
      linarith
    linarith [h2, h3, h4]
  exact le_trans hmain hfinal


theorem hb11_offdiag_pair_bound (h1 : Work.LinnikContract2.Area1) :
    ∀ (u w x : ℝ), 0 < w → w < u → u < x → 2 * w + 1 / 3 < u →
      ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q], 2 ≤ q →
        ∀ (χ χ' : DirichletCharacter ℂ q), χ * χ'⁻¹ ≠ 1 →
        ∀ (ρ ρ' : ℂ), Work.LinnikContract2.IsZ χ ρ →
          Work.LinnikContract2.lamOf q ρ ≤ Work.LinnikContract2.lamMax q →
          Work.LinnikContract2.IsZ χ' ρ' →
          Work.LinnikContract2.lamOf q ρ' ≤ Work.LinnikContract2.lamMax q →
          ‖∑' n : ℕ,
              (((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)) : ℂ)^2 *
              (χ (n : ZMod q) * (starRingEnd ℂ (χ' (n : ZMod q)))) *
              ((n : ℂ) ^ ((1 : ℂ) - ρ - (starRingEnd ℂ ρ'))) *
              (((Real.exp (-(n : ℝ) / (q:ℝ)^x)
                  - Real.exp (-(n : ℝ) * (Real.log q)^2 / (q:ℝ)^u)) : ℝ) : ℂ)‖
            ≤ C / Real.log q := by
  intro u w x hw hwu hux h2w
  obtain ⟨C₁, hC₁pos, Q, hC₁⟩ := Ssm_diff_bound h1 u w x hw hwu hux h2w
  obtain ⟨C₂, hC₂pos, hC₂⟩ := hb11_crude_bound u w x hw hwu hux Q
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁pos, ?_⟩
  intro q _ hq2 χ χ' hχχ' ρ ρ' hZ1 hlam1 hZ2 hlam2
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hL : 0 < Real.log q := Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hL0 : (0 : ℝ) ≤ Real.log q := hL.le
  have hW1 : 1 ≤ (q : ℝ) ^ w := Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ q)) hw.le
  have hWlt : 1 < (q : ℝ) ^ w := by
    have h2 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
    have h := Real.rpow_lt_rpow (show (0 : ℝ) ≤ 1 by norm_num) h2 hw
    rwa [Real.one_rpow] at h
  have hsumid : (∑' n : ℕ,
        (((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM ((q:ℝ)^w) d : ℝ)) : ℂ)^2 *
        (χ (n : ZMod q) * (starRingEnd ℂ (χ' (n : ZMod q)))) *
        ((n : ℂ) ^ ((1 : ℂ) - ρ - (starRingEnd ℂ ρ'))) *
        (((Real.exp (-(n : ℝ) / (q:ℝ)^x)
            - Real.exp (-(n : ℝ) * (Real.log q)^2 / (q:ℝ)^u)) : ℝ) : ℂ))
      = Ssm q 1 ((q:ℝ)^w) ((q:ℝ)^w) ((q:ℝ)^x) (χ * χ'⁻¹) (ρ + (starRingEnd ℂ ρ') - 1)
        - Ssm q 1 ((q:ℝ)^w) ((q:ℝ)^w) (((q:ℝ)^u) / (Real.log q)^2) (χ * χ'⁻¹)
            (ρ + (starRingEnd ℂ ρ') - 1) := by
    set W := (q : ℝ) ^ w with hWdef
    set X := (q : ℝ) ^ x with hXdef
    set Y := ((q : ℝ) ^ u) / (Real.log q) ^ 2 with hYdef
    set ψ := χ * χ'⁻¹ with hψdef
    set σ : ℂ := ρ + (starRingEnd ℂ ρ') - 1 with hσdef
    have hW1' : 1 < W := hWlt
    have hXpos : 0 < X := by rw [hXdef]; positivity
    have hYpos : 0 < Y := by rw [hYdef]; positivity
    have hsX : Summable (fun n : ℕ => detCoeff q 1 W W ψ σ n * ((Real.exp (-(n:ℝ)/X) : ℝ) : ℂ)) := by
      have := summable_detCoeff_mul_exp (q := q) 1 W W ψ σ (t := 1 / X) (by norm_num) (by positivity)
      simpa [div_eq_mul_inv] using this
    have hsY : Summable (fun n : ℕ => detCoeff q 1 W W ψ σ n * ((Real.exp (-(n:ℝ)/Y) : ℝ) : ℂ)) := by
      have := summable_detCoeff_mul_exp (q := q) 1 W W ψ σ (t := 1 / Y) (by norm_num) (by positivity)
      simpa [div_eq_mul_inv] using this
    change (∑' n : ℕ,
        (((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM W d : ℝ)) : ℂ)^2 *
        (χ (n : ZMod q) * (starRingEnd ℂ (χ' (n : ZMod q)))) *
        ((n : ℂ) ^ ((1 : ℂ) - ρ - (starRingEnd ℂ ρ'))) *
        (((Real.exp (-(n : ℝ) / X)
            - Real.exp (-(n : ℝ) * (Real.log q)^2 / (q:ℝ)^u)) : ℝ) : ℂ))
      = (∑' n : ℕ, detCoeff q 1 W W ψ σ n * ((Real.exp (-(n:ℝ)/X) : ℝ) : ℂ))
        - (∑' n : ℕ, detCoeff q 1 W W ψ σ n * ((Real.exp (-(n:ℝ)/Y) : ℝ) : ℂ))
    rw [← Summable.tsum_sub hsX hsY]
    refine tsum_congr fun n => ?_
    have hdet : detCoeff q 1 W W ψ σ n
        = ((Work.LinnikAreas.Density4.thetaS W n : ℝ) : ℂ)^2 * (ψ (n : ZMod q))
          * ((n : ℂ) ^ (-σ)) := by
      rw [detCoeff]
      rw [psiS_one_eq_thetaS (W := W) hW1']
      ring
    rw [hdet]
    have hexpYU : Real.exp (-(n : ℝ) * (Real.log q)^2 / (q:ℝ)^u) = Real.exp (-(n:ℝ)/Y) := by
      rw [hYdef]; congr 1; field_simp
    rw [hexpYU, conj_char_mul χ χ' (n : ZMod q)]
    rw [show (1 : ℂ) - ρ - (starRingEnd ℂ ρ') = -σ by rw [hσdef]; ring]
    simp only [Work.LinnikAreas.Density4.thetaS, Complex.ofReal_sub]
    ring
  rw [hsumid]
  by_cases hqQ : Q ≤ q
  · have hstrip1 := Work.LinnikAreas.Density4.re_strip_of_isZ
      (Work.LinnikContract2.IsZ_iff_round1.mp hZ1)
    have hstrip2 := Work.LinnikAreas.Density4.re_strip_of_isZ
      (Work.LinnikContract2.IsZ_iff_round1.mp hZ2)
    have hσ1 : (ρ + (starRingEnd ℂ ρ') - 1).re ≤ 1 := by
      simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.conj_re]
      linarith [hstrip1.2, hstrip2.2]
    have hσim : |(ρ + (starRingEnd ℂ ρ') - 1).im| ≤ 2 := by
      have him : (ρ + (starRingEnd ℂ ρ') - 1).im = ρ.im - ρ'.im := by
        simp only [Complex.sub_im, Complex.add_im, Complex.one_im, sub_zero, Complex.conj_im]
        ring
      rw [him]
      have h1 : |ρ.im| ≤ 1 := hZ1.2.2
      have h2 : |ρ'.im| ≤ 1 := hZ2.2.2
      calc |ρ.im - ρ'.im| ≤ |ρ.im| + |ρ'.im| := abs_sub _ _
        _ ≤ 2 := by linarith
    have hσlam : (1 - (ρ + (starRingEnd ℂ ρ') - 1).re) * Real.log q
        ≤ 2 * Work.LinnikContract2.lamMax q := by
      have hre : (ρ + (starRingEnd ℂ ρ') - 1).re = ρ.re + ρ'.re - 1 := by
        simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.conj_re]
      have h1 : (1 - ρ.re) * Real.log q = Work.LinnikContract2.lamOf q ρ := rfl
      have h2 : (1 - ρ'.re) * Real.log q = Work.LinnikContract2.lamOf q ρ' := rfl
      rw [hre]
      nlinarith [hlam1, hlam2]
    have hb := hC₁ q hqQ (χ * χ'⁻¹) hχχ' (ρ + (starRingEnd ℂ ρ') - 1) hσ1 hσim hσlam
    refine le_trans hb ?_
    rw [div_le_div_iff_of_pos_right hL]
    exact le_max_left _ _
  · have hlt : q < Q := lt_of_not_ge hqQ
    rw [← hsumid]
    have hb := hC₂ q hq2 hlt χ χ' hχχ' ρ ρ' hZ1 hlam1 hZ2 hlam2
    refine le_trans hb ?_
    rw [div_le_div_iff_of_pos_right hL]
    exact le_max_right _ _

end Work.LinnikAreas2

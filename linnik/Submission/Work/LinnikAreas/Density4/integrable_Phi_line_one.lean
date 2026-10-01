import Mathlib
import Submission.Work.LinnikAreas.Density4.SsmPhiAux
import Submission.Work.LinnikAreas.Density4.norm_lcmF_le_gen
import Submission.Work.LinnikAreas.Density4.SsmCommonsDeps
import Submission.Work.LinnikAreas.Density4.integrable_one_add_abs_rpow_exp
import Submission.Work.LinnikAreas.Density4.gamma_vertical_integrable_of_bound

namespace Work.LinnikAreas.Density4

open Complex MeasureTheory

/-- `t ↦ Phi (1 + i t)` is integrable on `ℝ`.

On the line `Re s = 1` all four factors of `Phi (1 + i t)` are controlled by an
integrable majorant: `Γ (1 + i t)` decays like `e^{-π|t|/2}`, `X^{1+it}` has modulus `X`,
`L (ρ + 1 + i t)` is dominated by `log q + log (2 + |t|) + 6` (the character-`L` bound on
`Re s ≥ 1`), and `lcmF (ρ + 1 + i t)` is bounded by a constant depending only on `V`, `W`
(the finite-lcm weight on `Re s ≥ 0`).  Since `ρ.re > 0` the point `ρ + 1 + i t` stays in
`Re s > 1`, where the naive expression for `Phi` applies (`Phi_eq_naive`). -/
theorem integrable_Phi_line_one (q : ℕ) [NeZero q] {U V W X : ℝ} (hU : 0 < U) (hUV : U ≤ V)
    (hV : 1 ≤ V) (hW : 1 ≤ W) (hX : 0 < X) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (ρ : ℂ)
    (hβ : 0 < ρ.re) (hL0 : DirichletCharacter.LFunction χ ρ = 0) :
    MeasureTheory.Integrable
      (fun t : ℝ => Work.LinnikAreas.Density4.Phi q U V W X χ ρ ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
  -- exponential decay of `Γ` on the vertical line `Re s = 1`
  obtain ⟨Cg, _hCgpos, hCg⟩ :=
    Commons.Analysis.SpecialFunctions.Gamma.gamma_vertical_exp_decay 1 one_pos
  set KL : ℝ := Real.log (q : ℝ) + 6 + 2 + |ρ.im| with hKLdef
  set Cl : ℝ := (V * W) ^ (1 / (1 : ℝ)) * (1 + Real.log (V * W)) ^ 3 with hCldef
  set K : ℝ := Cg * X * KL * Cl with hKdef
  -- the integrand is continuous, hence a.e. strongly measurable
  have hcont : Continuous (fun t : ℝ =>
      Work.LinnikAreas.Density4.Phi q U V W X χ ρ ((1 : ℂ) + (t : ℂ) * Complex.I)) := by
    have hline : Continuous (fun t : ℝ => (1 : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
    exact (Work.LinnikAreas.Density4.continuousOn_Phi q U V W X χ ρ hX hχ).comp_continuous
      hline (fun t => by simp [Complex.add_re])
  -- the integrable majorant
  have hbase : Integrable (fun t : ℝ => (1 + |t|) ^ (2 : ℝ) * Real.exp (-(Real.pi / 2 * |t|))) :=
    Work.LinnikAreas.Density4.integrable_one_add_abs_rpow_exp 2 (Real.pi / 2) (by positivity)
  have hmaj : Integrable (fun t : ℝ =>
      K * ((1 + |t|) ^ (2 : ℝ) * Real.exp (-(Real.pi / 2 * |t|)))) :=
    hbase.const_mul K
  refine hmaj.mono' hcont.aestronglyMeasurable ?_
  filter_upwards with t
  set s : ℂ := (1 : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsne : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hsdef] at this
  have hsre : s.re = 1 := by simp [hsdef]
  have hsim : s.im = t := by simp [hsdef]
  have hXnorm : ‖(X : ℂ) ^ s‖ = X := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, hsre, Real.rpow_one]
  have hGamma : ‖Complex.Gamma s‖ ≤ Cg * (1 + |t|) * Real.exp (-(Real.pi / 2 * |t|)) := by
    have h := hCg t
    rw [Real.rpow_one] at h
    rw [show -(Real.pi / 2) * |t| = -(Real.pi / 2 * |t|) by ring] at h
    have hs_eq : s = (1 : ℂ) + Complex.I * (t : ℂ) := by rw [hsdef]; ring
    rw [hs_eq]
    exact h
  have hLbound : ‖DirichletCharacter.LFunction χ (ρ + s)‖ ≤ KL * (1 + |t|) := by
    rw [hKLdef]
    have h := Commons.NumberTheory.DirichletCharacter.norm_LFunction_le_re_ge_one χ hχ (ρ + s)
      (by rw [Complex.add_re, hsre]; linarith)
    have him : (ρ + s).im = ρ.im + t := by rw [Complex.add_im, hsim]
    rw [him] at h
    refine le_trans h ?_
    have hlog : Real.log (2 + |ρ.im + t|) ≤ 2 + |ρ.im| + |t| := by
      have hy : 0 < 2 + |ρ.im + t| := by positivity
      rw [Real.log_le_iff_le_exp hy]
      have hle : (2 : ℝ) + |ρ.im + t| ≤ 2 + |ρ.im| + |t| := by linarith [abs_add_le ρ.im t]
      have hexp : 2 + |ρ.im| + |t| ≤ Real.exp (2 + |ρ.im| + |t|) := by
        linarith [Real.add_one_le_exp (2 + |ρ.im| + |t|)]
      linarith
    have hkey : 2 + |ρ.im| + |t| ≤ (2 + |ρ.im|) * (1 + |t|) := by
      have h2 : (1 : ℝ) ≤ 2 + |ρ.im| := by linarith [abs_nonneg ρ.im]
      calc 2 + |ρ.im| + |t| ≤ (2 + |ρ.im|) + (2 + |ρ.im|) * |t| := by
            have := mul_le_mul_of_nonneg_right h2 (abs_nonneg t); linarith
        _ = (2 + |ρ.im|) * (1 + |t|) := by ring
    have hq0 : 0 ≤ Real.log (q : ℝ) + 6 := by linarith [Real.log_natCast_nonneg q]
    have hqt : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hq : Real.log (q : ℝ) + 6 ≤ (Real.log (q : ℝ) + 6) * (1 + |t|) := by
      calc Real.log (q : ℝ) + 6 = (Real.log (q : ℝ) + 6) * 1 := by ring
        _ ≤ (Real.log (q : ℝ) + 6) * (1 + |t|) := mul_le_mul_of_nonneg_left hqt hq0
    calc Real.log (q : ℝ) + Real.log (2 + |ρ.im + t|) + 6
        ≤ Real.log (q : ℝ) + (2 + |ρ.im| + |t|) + 6 := by linarith
      _ = (Real.log (q : ℝ) + 6) + (2 + |ρ.im| + |t|) := by ring
      _ ≤ (Real.log (q : ℝ) + 6) * (1 + |t|) + (2 + |ρ.im|) * (1 + |t|) := add_le_add hq hkey
      _ = (Real.log (q : ℝ) + 6 + 2 + |ρ.im|) * (1 + |t|) := by ring
  have hlcm : ‖Work.LinnikAreas.Density4.lcmF q U V W χ (ρ + s)‖ ≤ Cl := by
    rw [hCldef]
    have hs1 : (1 : ℝ) - (↑(1 : ℕ) : ℝ)⁻¹ ≤ (ρ + s).re := by
      have h : (1 : ℝ) - (↑(1 : ℕ) : ℝ)⁻¹ = 0 := by norm_num
      rw [h, Complex.add_re, hsre]; linarith
    have h := Work.LinnikAreas.Density4.norm_lcmF_le_gen q hU hUV hV hW χ (k := 1) le_rfl
      (s := ρ + s) hs1
    simpa using h
  rw [show Work.LinnikAreas.Density4.Phi q U V W X χ ρ ((1 : ℂ) + (t : ℂ) * Complex.I)
        = Work.LinnikAreas.Density4.Phi q U V W X χ ρ s from by rw [hsdef]]
  rw [Work.LinnikAreas.Density4.Phi_eq_naive q U V W X χ ρ s hL0 hsne]
  rw [norm_mul, norm_mul, norm_mul, hXnorm]
  calc ‖Complex.Gamma s‖ * X * ‖DirichletCharacter.LFunction χ (ρ + s)‖
        * ‖Work.LinnikAreas.Density4.lcmF q U V W χ (ρ + s)‖
      ≤ (Cg * (1 + |t|) * Real.exp (-(Real.pi / 2 * |t|))) * X * (KL * (1 + |t|)) * Cl := by
        gcongr
    _ = K * ((1 + |t|) ^ (2 : ℝ) * Real.exp (-(Real.pi / 2 * |t|))) := by
        rw [hKdef, show (1 + |t|) ^ (2 : ℝ) = (1 + |t|) * (1 + |t|) by
          rw [Real.rpow_two, pow_two]]
        ring

end Work.LinnikAreas.Density4

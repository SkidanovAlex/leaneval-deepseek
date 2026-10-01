import Mathlib
import Submission.Work.ZeroDensity.LogFree.CrossDefs
import Submission.Work.LinnikAreas.JutilaPieces.LFunctionCritLineBound
import Submission.Work.LinnikAreas.Density4.integrable_one_add_abs_rpow_exp
import Submission.Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp
import Submission.Work.LinnikAreas2.dslope_diff_cpow_norm_le

/-!
# `Work.ZeroDensity.LogFree.CrossLine` — the shifted-line inputs of the cross Gram bound

The cross-character Gram entry is `Ssm q 1 W W X ψ σ - Ssm q 1 W W U' ψ σ` (`CrossDefs.crossGram`),
and it is bounded by shifting the Mellin contour of that difference from the line `Re s = 1` down
to the line `Re (σ + s) = 0`, i.e. `Re s = -Re σ`.  This file supplies the analytic inputs on that
line:

* `cross_Lbd`: the convexity bound `‖L(iy,ψ)‖ ≤ C·𝓓^{1/2+η}(2+|t|)^{1/2+η}` at the scale
  `𝓓 = scale q T = q(T+2)`, at the point `σ + (-σ.re + it) = i(σ.im + t)`;
* `norm_Gamma_shifted`: the pointwise `Γ`-bound `‖Γ(c+it)‖ ≤ C (1+|t|)^{3/2}e^{-π|t|/2}/(δ(1+c))`
  for `-1 < c ≤ -δ`, the factor `1/(1+c)` being the inverse of the distance from the line to the
  pole of `Γ` at `-1`;
* `integrable_gamma_shifted` and `gamma_integral_shifted_cross`: the corresponding `L¹`-statement
  and the bound `∫‖Γ(c+it)‖(2+|t|)^r ≤ C/(1+c)`;
* `norm_Ptw_cross_line`: the pointwise bound for the regularised cross kernel
  `Ptw q 1 W W X U' ψ σ` on that line, with the `L`-bound supplied as a hypothesis.
-/

open DirichletCharacter Complex MeasureTheory
open Work.LinnikAreas.Density4
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroDensity.LogFree

/-- The convexity bound on the imaginary axis, at the scale `𝓓 = q(T+2)`, at the point
`σ + (-σ.re + it) = i(σ.im + t)`: `‖L(iy,ψ)‖ ≤ C 𝓓^{1/2+η}(2+|t|)^{1/2+η}` with `y = σ.im + t`. -/
theorem cross_Lbd (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (T : ℝ), 2 ≤ q → 1 ≤ T →
      ∀ (ψ : DirichletCharacter ℂ q), ψ ≠ 1 → ∀ (σ : ℂ), |σ.im| ≤ 2 * T → ∀ t : ℝ,
        ‖DirichletCharacter.LFunction ψ (σ + (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
          ≤ C * (scale q T) ^ ((1 : ℝ) / 2 + η) * (2 + |t|) ^ ((1 : ℝ) / 2 + η) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    Work.LinnikAreas.JutilaPieces.LFunctionCritLineBound (η / 2) (by linarith)
  refine ⟨C₁ * 2 ^ ((1 : ℝ) / 2 + η / 2), by positivity, ?_⟩
  intro q _inst T hq hT ψ hψ σ hσ t
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hT1 : (1 : ℝ) ≤ T := hT
  have hscale1 : (1 : ℝ) ≤ scale q T := by
    rw [scale]
    nlinarith [abs_nonneg t]
  have hspos : (0 : ℝ) < scale q T := lt_of_lt_of_le one_pos hscale1
  have hb1 : (1 : ℝ) ≤ 2 + |t| := by linarith [abs_nonneg t]
  have hbpos : (0 : ℝ) < 2 + |t| := by linarith [abs_nonneg t]
  have harg : σ + (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)
      = ((σ.im + t : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [harg]
  refine (hC₁ q ψ hψ (σ.im + t)).trans ?_
  have hy_le : 1 + |σ.im + t| ≤ (2 * T + 2) * (2 + |t|) := by
    have h1 : |σ.im + t| ≤ |σ.im| + |t| := abs_add_le _ _
    have h2 : |σ.im| ≤ 2 * T := hσ
    have h3 : (0 : ℝ) ≤ 2 + |t| := by linarith [abs_nonneg t]
    nlinarith [h1, h2, h3, hT1, abs_nonneg t]
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hqy_le : (q : ℝ) * (1 + |σ.im + t|) ≤ 2 * scale q T * (2 + |t|) := by
    rw [scale]
    have h2T : 2 * T + 2 ≤ 2 * (T + 2) := by linarith
    have hb : (0 : ℝ) ≤ 2 + |t| := by linarith [abs_nonneg t]
    calc (q : ℝ) * (1 + |σ.im + t|) ≤ (q : ℝ) * ((2 * T + 2) * (2 + |t|)) :=
          mul_le_mul_of_nonneg_left hy_le hqnn
      _ ≤ (q : ℝ) * ((2 * (T + 2)) * (2 + |t|)) := by
          have h := mul_le_mul_of_nonneg_right h2T hb
          exact mul_le_mul_of_nonneg_left h hqnn
      _ = 2 * ((q : ℝ) * (T + 2)) * (2 + |t|) := by ring
  have hstep1 : ((q : ℝ) * (1 + |σ.im + t|)) ^ ((1 : ℝ) / 2 + η / 2)
      ≤ (2 * scale q T * (2 + |t|)) ^ ((1 : ℝ) / 2 + η / 2) :=
    Real.rpow_le_rpow (by positivity) hqy_le (by positivity)
  have hstep2 : (2 * scale q T * (2 + |t|)) ^ ((1 : ℝ) / 2 + η / 2)
      = 2 ^ ((1 : ℝ) / 2 + η / 2) * (scale q T) ^ ((1 : ℝ) / 2 + η / 2)
          * (2 + |t|) ^ ((1 : ℝ) / 2 + η / 2) := by
    rw [Real.mul_rpow (by positivity) hbpos.le, Real.mul_rpow (by norm_num) hspos.le]
  have hstep3 : (scale q T) ^ ((1 : ℝ) / 2 + η / 2) * (2 + |t|) ^ ((1 : ℝ) / 2 + η / 2)
      ≤ (scale q T) ^ ((1 : ℝ) / 2 + η) * (2 + |t|) ^ ((1 : ℝ) / 2 + η) := by
    have h1 : (scale q T) ^ ((1 : ℝ) / 2 + η / 2) ≤ (scale q T) ^ ((1 : ℝ) / 2 + η) :=
      Real.rpow_le_rpow_of_exponent_le hscale1 (by linarith)
    have h2 : (2 + |t|) ^ ((1 : ℝ) / 2 + η / 2) ≤ (2 + |t|) ^ ((1 : ℝ) / 2 + η) :=
      Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  have hstep4 : 2 ^ ((1 : ℝ) / 2 + η / 2) * ((scale q T) ^ ((1 : ℝ) / 2 + η)
        * (2 + |t|) ^ ((1 : ℝ) / 2 + η))
      = 2 ^ ((1 : ℝ) / 2 + η / 2) * (scale q T) ^ ((1 : ℝ) / 2 + η)
        * (2 + |t|) ^ ((1 : ℝ) / 2 + η) := by ring
  calc C₁ * ((q : ℝ) * (1 + |σ.im + t|)) ^ ((1 : ℝ) / 2 + η / 2)
      ≤ C₁ * (2 * scale q T * (2 + |t|)) ^ ((1 : ℝ) / 2 + η / 2) :=
        mul_le_mul_of_nonneg_left hstep1 hC₁pos.le
    _ = C₁ * (2 ^ ((1 : ℝ) / 2 + η / 2) * (scale q T) ^ ((1 : ℝ) / 2 + η / 2)
          * (2 + |t|) ^ ((1 : ℝ) / 2 + η / 2)) := by rw [hstep2]
    _ = C₁ * (2 ^ ((1 : ℝ) / 2 + η / 2) * ((scale q T) ^ ((1 : ℝ) / 2 + η / 2)
          * (2 + |t|) ^ ((1 : ℝ) / 2 + η / 2))) := by ring
    _ ≤ C₁ * (2 ^ ((1 : ℝ) / 2 + η / 2) * ((scale q T) ^ ((1 : ℝ) / 2 + η)
          * (2 + |t|) ^ ((1 : ℝ) / 2 + η))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep3 (by positivity)) hC₁pos.le
    _ = C₁ * 2 ^ ((1 : ℝ) / 2 + η / 2) * (scale q T) ^ ((1 : ℝ) / 2 + η)
          * (2 + |t|) ^ ((1 : ℝ) / 2 + η) := by ring

/-- `Γ s = Γ (s+2) / (s (s+1))` for `s ∉ {0,-1}`. -/
lemma Gamma_eq_Gamma_add_two (s : ℂ) (hs : s ≠ 0) (hs1 : s + 1 ≠ 0) :
    Complex.Gamma s = Complex.Gamma (s + 2) / (s * (s + 1)) := by
  have h2 : Complex.Gamma (s + 2) = (s + 1) * Complex.Gamma (s + 1) := by
    have h := Complex.Gamma_add_one (s + 1) hs1
    rwa [show (s + 1) + 1 = s + 2 by ring] at h
  have h1 : Complex.Gamma (s + 1) = s * Complex.Gamma s := Complex.Gamma_add_one s hs
  have hmul : (s * (s + 1)) * Complex.Gamma s = Complex.Gamma (s + 2) := by
    rw [h2, h1]; ring
  rw [← hmul, mul_div_cancel_left₀ _ (mul_ne_zero hs hs1)]

/-- `Γ` is continuous on the vertical line `Re s = c` for `-1 < c < 0` (no pole is met: the
only non-positive integer in `(-1,0)` would be `0`). -/
lemma continuous_gamma_line_of_neg_one_lt {c : ℝ} (hc1 : -1 < c) (hc0 : c < 0) :
    Continuous (fun t : ℝ => Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hinner : ContinuousAt (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) t := by fun_prop
  refine ContinuousAt.comp (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I)
    (g := Complex.Gamma) (x := t) ?_ hinner
  refine Complex.continuousAt_Gamma _ fun m hm => ?_
  have h := congrArg Complex.re hm
  have hre : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by simp
  rw [hre] at h
  have h2 : (-(m : ℂ)).re = -(m : ℝ) := by simp
  rw [h2] at h
  have hm1 : m = 0 := by
    have h1 : (m : ℝ) < 1 := by linarith
    have h2' : m < 1 := by exact_mod_cast h1
    omega
  subst hm1
  simp at h
  linarith

/-- `integrable_one_add_abs_rpow_exp` in the form `exp (-a * |t|)`. -/
lemma integrable_one_add_abs_rpow_exp' (c a : ℝ) (ha : 0 < a) :
    Integrable (fun t : ℝ => (1 + |t|) ^ c * Real.exp (-(a) * |t|)) := by
  refine (Work.LinnikAreas.Density4.integrable_one_add_abs_rpow_exp c a ha).congr ?_
  filter_upwards with t
  rw [show -(a * |t|) = -(a) * |t| by ring]

/-- Pointwise `Γ`-bound on a vertical line `Re s = c` with `-1 < c ≤ -δ`: the pole of `Γ` at `-1`
is at distance `1 + c`, whence the factor `1/(δ(1+c))` (and the pole at `0` is at distance `δ`). -/
lemma norm_Gamma_shifted {Csh : ℝ} (hCshpos : 0 < Csh)
    (hCsh : ∀ u v : ℝ, 1 / 2 ≤ u → u ≤ 2 →
      ‖Complex.Gamma ((u : ℂ) + (v : ℂ) * Complex.I)‖
        ≤ Csh * (1 + |v|) ^ (u - 1 / 2) * Real.exp (-(Real.pi / 2) * |v|))
    {δ : ℝ} (hδ : 0 < δ) {c : ℝ} (hc1 : -1 < c) (hc2 : c ≤ -δ) (t : ℝ) :
    ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Csh * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2) * |t|) / (δ * (1 + c)) := by
  have hcm : c < 0 := by linarith
  have h1c : 0 < 1 + c := by linarith
  set s : ℂ := (c : ℂ) + (t : ℂ) * Complex.I with hs
  have hsne : s ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    rw [hs] at hh
    simp at hh
    linarith
  have hs1ne : s + 1 ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    rw [hs] at hh
    simp at hh
    linarith
  have hsplit := Gamma_eq_Gamma_add_two s hsne hs1ne
  have harg2 : s + 2 = (((c + 2 : ℝ)) : ℂ) + (t : ℂ) * Complex.I := by
    rw [hs]; push_cast; ring
  have hΓ2 : ‖Complex.Gamma ((((c + 2 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Csh * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2) * |t|) := by
    have h := hCsh (c + 2) t (by linarith) (by linarith)
    have hpow : (1 + |t|) ^ (c + 2 - 1 / 2) ≤ (1 + |t|) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (by linarith)
    have hstep : Csh * (1 + |t|) ^ ((c + 2 - 1 / 2)) ≤ Csh * (1 + |t|) ^ ((3 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_left hpow hCshpos.le
    calc ‖Complex.Gamma ((((c + 2 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ Csh * (1 + |t|) ^ (c + 2 - 1 / 2) * Real.exp (-(Real.pi / 2) * |t|) := h
      _ = (Csh * (1 + |t|) ^ (c + 2 - 1 / 2)) * Real.exp (-(Real.pi / 2) * |t|) := by ring
      _ ≤ (Csh * (1 + |t|) ^ ((3 : ℝ) / 2)) * Real.exp (-(Real.pi / 2) * |t|) :=
          mul_le_mul_of_nonneg_right hstep (Real.exp_nonneg _)
      _ = Csh * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2) * |t|) := by ring
  have h1 : -c ≤ ‖s‖ := by
    have h := Complex.abs_re_le_norm s
    have hre : s.re = c := by rw [hs]; simp
    rw [hre] at h
    rwa [abs_of_neg hcm] at h
  have h2 : 1 + c ≤ ‖s + 1‖ := by
    have h := Complex.abs_re_le_norm (s + 1)
    have hre : (s + 1).re = 1 + c := by rw [hs]; simp; ring
    rw [hre] at h
    rwa [abs_of_nonneg h1c.le] at h
  have hδc : δ ≤ -c := by linarith
  have hnorm1 : δ * (1 + c) ≤ ‖s‖ * ‖s + 1‖ := by
    have hmm : (-c) * (1 + c) ≤ ‖s‖ * ‖s + 1‖ :=
      mul_le_mul h1 h2 (by linarith) (norm_nonneg s)
    have h2' : δ * (1 + c) ≤ (-c) * (1 + c) := mul_le_mul_of_nonneg_right hδc h1c.le
    linarith
  have hden : (0 : ℝ) < δ * (1 + c) := by positivity
  rw [hsplit, norm_div, norm_mul, div_eq_mul_inv]
  have hinv : (‖s‖ * ‖s + 1‖)⁻¹ ≤ (δ * (1 + c))⁻¹ := by
    rw [inv_le_inv₀ (by positivity) hden]
    exact hnorm1
  have harg : Complex.Gamma (s + 2) = Complex.Gamma ((((c + 2 : ℝ)) : ℂ) + (t : ℂ) * Complex.I) := by
    rw [harg2]
  rw [harg]
  calc ‖Complex.Gamma ((((c + 2 : ℝ)) : ℂ) + (t : ℂ) * Complex.I)‖ * (‖s‖ * ‖s + 1‖)⁻¹
      ≤ (Csh * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2) * |t|))
          * (δ * (1 + c))⁻¹ :=
        mul_le_mul hΓ2 hinv (by positivity) (by positivity)
    _ = Csh * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2) * |t|) / (δ * (1 + c)) := by
        ring

/-- For `-1 < c < 0` the function `t ↦ ‖Γ(c+it)‖(2+|t|)^r` is integrable. -/
theorem integrable_gamma_shifted (r : ℝ) (hr : 0 ≤ r) {δ : ℝ} (hδ : 0 < δ) :
    ∀ c : ℝ, -1 < c → c ≤ -δ →
      Integrable (fun t : ℝ => ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) ^ r) := by
  intro c hc1 hc2
  obtain ⟨Csh, hCshpos, hCsh⟩ :=
    Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp
  have hcm : c < 0 := by linarith
  have h1c : 0 < 1 + c := by linarith
  set M : ℝ := Csh * 3 ^ r * (1 / (δ * (1 + c))) with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact mul_nonneg (mul_nonneg hCshpos.le (Real.rpow_nonneg (by norm_num) r)) (by positivity)
  have hmaj : Integrable (fun t : ℝ => M * ((1 + |t|) ^ ((3 : ℝ) / 2 + r)
      * Real.exp (-(Real.pi / 2) * |t|))) :=
    (integrable_one_add_abs_rpow_exp' ((3 : ℝ) / 2 + r) (Real.pi / 2) (by positivity)).const_mul M
  have h2tp : ∀ t : ℝ, (2 + |t|) ^ r ≤ 3 ^ r * (1 + |t|) ^ r := by
    intro t
    have hb : (2 + |t|) ≤ 3 * (1 + |t|) := by linarith [abs_nonneg t]
    calc (2 + |t|) ^ r ≤ (3 * (1 + |t|)) ^ r := Real.rpow_le_rpow (by positivity) hb hr
      _ = 3 ^ r * (1 + |t|) ^ r := Real.mul_rpow (by norm_num) (by positivity)
  have hbound : ∀ t : ℝ, ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) ^ r
      ≤ M * ((1 + |t|) ^ ((3 : ℝ) / 2 + r) * Real.exp (-(Real.pi / 2) * |t|)) := by
    intro t
    have hΓ := norm_Gamma_shifted hCshpos hCsh hδ hc1 hc2 t
    have hmul := mul_le_mul hΓ (h2tp t) (Real.rpow_nonneg (by positivity) r) (by positivity)
    have hkey : Csh * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2) * |t|) / (δ * (1 + c))
          * (3 ^ r * (1 + |t|) ^ r)
        = M * ((1 + |t|) ^ ((3 : ℝ) / 2 + r) * Real.exp (-(Real.pi / 2) * |t|)) := by
      rw [hMdef, Real.rpow_add (by linarith [abs_nonneg t])]
      field_simp
      try ring
    exact hmul.trans (le_of_eq hkey)
  have hcont : AEStronglyMeasurable
      (fun t : ℝ => ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) ^ r) volume := by
    have h2 : Continuous (fun t : ℝ => (2 + |t|) ^ r) :=
      (continuous_const.add continuous_abs).rpow_const
        (fun t => Or.inl (ne_of_gt (by linarith [abs_nonneg t] : (0 : ℝ) < 2 + |t|)))
    exact ((continuous_gamma_line_of_neg_one_lt hc1 hcm).norm.mul h2).aestronglyMeasurable
  refine hmaj.mono' hcont ?_
  filter_upwards with t
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (by linarith [abs_nonneg t] : (0 : ℝ) ≤ 2 + |t|) r))]
  exact hbound t

/-- The `Γ`-integral on the shifted line `Re s = c ∈ (-1,0)`, weighted by `(2+|t|)^r`, is at most
`C/(1+c)`; the factor `1/(1+c)` is the inverse of the distance from the line to the pole `-1`. -/
theorem gamma_integral_shifted_cross (r δ : ℝ) (hr : 0 ≤ r) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℝ), -1 < c → c ≤ -δ →
      ∫ t : ℝ, ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) ^ r
        ≤ C / (1 + c) := by
  obtain ⟨Csh, hCshpos, hCsh⟩ :=
    Commons.Analysis.SpecialFunctions.Gamma.Gamma_vertical_upper_uniform_sharp
  have hbase : Integrable (fun t : ℝ => (1 + |t|) ^ ((3 : ℝ) / 2 + r)
      * Real.exp (-(Real.pi / 2) * |t|)) :=
    integrable_one_add_abs_rpow_exp' ((3 : ℝ) / 2 + r) (Real.pi / 2) (by positivity)
  set K : ℝ := ∫ t : ℝ, (1 + |t|) ^ ((3 : ℝ) / 2 + r) * Real.exp (-(Real.pi / 2) * |t|) with hK
  have hK0 : 0 ≤ K := integral_nonneg fun t => by positivity
  refine ⟨Csh * 3 ^ r * (K + 1) / δ, by positivity, ?_⟩
  intro c hc1 hc2
  have hcm : c < 0 := by linarith
  have h1c : 0 < 1 + c := by linarith
  have hstep : ∀ t : ℝ, ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) ^ r
      ≤ (Csh * 3 ^ r / δ) * (1 / (1 + c))
        * ((1 + |t|) ^ ((3 : ℝ) / 2 + r) * Real.exp (-(Real.pi / 2) * |t|)) := by
    intro t
    have hΓ := norm_Gamma_shifted hCshpos hCsh hδ hc1 hc2 t
    have h2tp : (2 + |t|) ^ r ≤ 3 ^ r * (1 + |t|) ^ r := by
      have hb : (2 + |t|) ≤ 3 * (1 + |t|) := by linarith [abs_nonneg t]
      calc (2 + |t|) ^ r ≤ (3 * (1 + |t|)) ^ r := Real.rpow_le_rpow (by positivity) hb hr
        _ = 3 ^ r * (1 + |t|) ^ r := Real.mul_rpow (by norm_num) (by positivity)
    have hmul := mul_le_mul hΓ h2tp (Real.rpow_nonneg (by positivity) r) (by positivity)
    have hkey : Csh * (1 + |t|) ^ ((3 : ℝ) / 2) * Real.exp (-(Real.pi / 2) * |t|) / (δ * (1 + c))
          * (3 ^ r * (1 + |t|) ^ r)
        = (Csh * 3 ^ r / δ) * (1 / (1 + c))
          * ((1 + |t|) ^ ((3 : ℝ) / 2 + r) * Real.exp (-(Real.pi / 2) * |t|)) := by
      rw [Real.rpow_add (by linarith [abs_nonneg t])]
      field_simp
      try ring
    exact hmul.trans (le_of_eq hkey)
  have hmajint : Integrable (fun t : ℝ => (Csh * 3 ^ r / δ) * (1 / (1 + c))
      * ((1 + |t|) ^ ((3 : ℝ) / 2 + r) * Real.exp (-(Real.pi / 2) * |t|))) :=
    (integrable_one_add_abs_rpow_exp' ((3 : ℝ) / 2 + r) (Real.pi / 2) (by positivity)).const_mul _
  have hmono : ∫ t : ℝ, ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ * (2 + |t|) ^ r
      ≤ ∫ t : ℝ, (Csh * 3 ^ r / δ) * (1 / (1 + c))
          * ((1 + |t|) ^ ((3 : ℝ) / 2 + r) * Real.exp (-(Real.pi / 2) * |t|)) :=
    integral_mono (integrable_gamma_shifted r hr hδ c hc1 hc2) hmajint hstep
  have hval : ∫ t : ℝ, (Csh * 3 ^ r / δ) * (1 / (1 + c))
      * ((1 + |t|) ^ ((3 : ℝ) / 2 + r) * Real.exp (-(Real.pi / 2) * |t|))
      = (Csh * 3 ^ r / δ) * (1 / (1 + c)) * K := by
    rw [hK, integral_const_mul]
  refine hmono.trans ?_
  rw [hval]
  have hKle : K ≤ K + 1 := by linarith
  have hfac : 0 ≤ (Csh * 3 ^ r / δ) * (1 / (1 + c)) := by positivity
  have hfin : (Csh * 3 ^ r / δ) * (1 / (1 + c)) * K ≤ Csh * 3 ^ r * (K + 1) / δ / (1 + c) := by
    have h1 : (Csh * 3 ^ r / δ) * (1 / (1 + c)) * K
        ≤ (Csh * 3 ^ r / δ) * (1 / (1 + c)) * (K + 1) :=
      mul_le_mul_of_nonneg_left hKle hfac
    have h2 : (Csh * 3 ^ r / δ) * (1 / (1 + c)) * (K + 1)
        = Csh * 3 ^ r * (K + 1) / δ / (1 + c) := by
      field_simp
      try ring
    linarith [h1, h2]
  exact hfin

/-- The pointwise bound on the shifted line `Re s = -σ.re` for the regularised cross kernel
`Ptw`; the `L`-bound on that line is supplied as a hypothesis. -/
theorem norm_Ptw_cross_line (q : ℕ) [NeZero q] {W X U' Cb r : ℝ}
    {ψ : DirichletCharacter ℂ q} {σ : ℂ}
    (hW : 1 < W) (hX : 0 < X) (hU' : 0 < U') (hCb : 0 < Cb) (hr : 0 ≤ r)
    (hσpos : 0 < σ.re)
    (hLbd : ∀ t : ℝ, ‖DirichletCharacter.LFunction ψ (σ + (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ Cb * (2 + |t|) ^ r) :
    ∀ t : ℝ, ‖Work.LinnikAreas2.Ptw q 1 W W X U' ψ σ (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ Cb * (2 + |t|) ^ r * ‖Complex.Gamma (((-σ.re : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
          * (X ^ (-σ.re) + U' ^ (-σ.re)) * (2 * W) ^ 2 := by
  intro t
  set s : ℂ := (((-σ.re : ℝ)) : ℂ) + (t : ℂ) * Complex.I with hs
  have hsre : s.re = -σ.re := by simp [hs]
  have hsne : s ≠ 0 := by
    intro h
    have h1 := congrArg Complex.re h
    rw [hsre] at h1
    simp at h1
    linarith [hσpos]
  have hnaive := Work.LinnikAreas2.Ptw_eq_naive q 1 W W X U' ψ σ s hsne
  have hres : (σ + s).re = 0 := by
    rw [Complex.add_re, hsre]
    ring
  have hlcm : ‖lcmF q 1 W W ψ (σ + s)‖ ≤ (2 * W) ^ 2 := by
    rw [lcmF_one_eq_crossQ q hW ψ (σ + s)]
    exact norm_crossQ_le q hW ψ (le_of_eq hres.symm)
  have hX : ‖(X : ℂ) ^ s‖ = X ^ (-σ.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX, hsre]
  have hU'' : ‖(U' : ℂ) ^ s‖ = U' ^ (-σ.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hU', hsre]
  have hdiff : ‖(X : ℂ) ^ s - (U' : ℂ) ^ s‖ ≤ X ^ (-σ.re) + U' ^ (-σ.re) := by
    calc ‖(X : ℂ) ^ s - (U' : ℂ) ^ s‖ ≤ ‖(X : ℂ) ^ s‖ + ‖(U' : ℂ) ^ s‖ := norm_sub_le _ _
      _ = X ^ (-σ.re) + U' ^ (-σ.re) := by rw [hX, hU'']
  have hslbd : ‖DirichletCharacter.LFunction ψ (σ + s)‖ ≤ Cb * (2 + |t|) ^ r := by
    rw [hs]; exact hLbd t
  rw [hnaive, norm_mul, norm_mul, norm_mul]
  have hCb0 : 0 ≤ Cb * (2 + |t|) ^ r := by positivity
  have hΓ0 : 0 ≤ ‖Complex.Gamma s‖ := norm_nonneg _
  have hX0 : 0 ≤ X ^ (-σ.re) + U' ^ (-σ.re) := by positivity
  have h1 : ‖Complex.Gamma s‖ * ‖(X : ℂ) ^ s - (U' : ℂ) ^ s‖
      ≤ ‖Complex.Gamma s‖ * (X ^ (-σ.re) + U' ^ (-σ.re)) :=
    mul_le_mul_of_nonneg_left hdiff hΓ0
  have h2 : ‖Complex.Gamma s‖ * ‖(X : ℂ) ^ s - (U' : ℂ) ^ s‖
        * ‖DirichletCharacter.LFunction ψ (σ + s)‖
      ≤ ‖Complex.Gamma s‖ * (X ^ (-σ.re) + U' ^ (-σ.re)) * (Cb * (2 + |t|) ^ r) :=
    mul_le_mul h1 hslbd (norm_nonneg _) (mul_nonneg hΓ0 hX0)
  have h3 : ‖Complex.Gamma s‖ * ‖(X : ℂ) ^ s - (U' : ℂ) ^ s‖
        * ‖DirichletCharacter.LFunction ψ (σ + s)‖ * ‖lcmF q 1 W W ψ (σ + s)‖
      ≤ (‖Complex.Gamma s‖ * (X ^ (-σ.re) + U' ^ (-σ.re)) * (Cb * (2 + |t|) ^ r))
          * (2 * W) ^ 2 :=
    mul_le_mul h2 hlcm (norm_nonneg _) (mul_nonneg (mul_nonneg hΓ0 hX0) hCb0)
  calc ‖Complex.Gamma s‖ * ‖(X : ℂ) ^ s - (U' : ℂ) ^ s‖
        * ‖DirichletCharacter.LFunction ψ (σ + s)‖ * ‖lcmF q 1 W W ψ (σ + s)‖
      ≤ (‖Complex.Gamma s‖ * (X ^ (-σ.re) + U' ^ (-σ.re)) * (Cb * (2 + |t|) ^ r))
          * (2 * W) ^ 2 := h3
    _ = Cb * (2 + |t|) ^ r * ‖Complex.Gamma s‖ * (X ^ (-σ.re) + U' ^ (-σ.re))
          * (2 * W) ^ 2 := by ring

end Work.ZeroDensity.LogFree

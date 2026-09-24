import Mathlib
import Submission.Commons.Analysis.Oscillatory.norm_integral_mul_exp_le_of_hasDerivAt_deriv_ge_mono

/-!
# A first-derivative (van der Corput) bound for the oscillation integral of GM §6

Guth–Maynard, *New large value estimates for Dirichlet polynomials*, proof of Lemma 6.2,
needs the estimate (for `|σ| ≥ 2`)

`∫_V^{2V} v^{-1+iσ} e(-v) dv ≪ 1/|σ|`  when `V ≤ |σ|/20`,  `≪ 1/|σ|^{1/2}` when `V ≍ |σ|`,

and in particular the uniform bound `|∫_V^{2V} v^{-1+iσ} e(-v) dv| ≤ C V/√(1+|σ|)` for `V ≥ 1`,
which is what we prove here.

The proof: if `|σ| ≤ 8πV` the trivial bound `≤ 1` suffices (the right-hand side is `≥ C` there);
if `|σ| ≥ 8πV` we substitute `v = e^s`, so that the integral becomes
`∫_{log V}^{log 2V} exp(i(σs - 2π e^s)) ds` whose phase has `|d/ds(σs - 2π e^s)| = |σ - 2π e^s| ≥ |σ|/2`
on the range, and the first-derivative van der Corput bound (`Commons.Analysis.Oscillatory.vdc_first_deriv`)
gives `≤ 8/|σ|`.
-/

open MeasureTheory Set
open scoped Real Interval

set_option autoImplicit false

namespace Work.GM.S2

noncomputable section

/-- The oscillatory integrand `v^{iσ-1} e(-v)` of the target integral. -/
def oscF (σ v : ℝ) : ℂ :=
  (v : ℂ) ^ (Complex.I * (σ : ℂ) - 1) * Complex.exp (-(2 * Real.pi * Complex.I * (v : ℂ)))

/-- The phase after substituting `v = e^s`: `σ s - 2π e^s`. -/
def phase (σ : ℝ) : ℝ → ℝ := fun s => σ * s - 2 * Real.pi * Real.exp s

lemma norm_oscF (σ : ℝ) {v : ℝ} (hv : 0 < v) : ‖oscF σ v‖ = v⁻¹ := by
  rw [oscF, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hv, Complex.norm_exp]
  have h1 : (Complex.I * (σ : ℂ) - 1).re = -1 := by simp
  rw [h1]
  have h2 : (-(2 * ↑Real.pi * Complex.I * (v : ℂ))).re = 0 := by simp
  rw [h2, Real.exp_zero, mul_one, Real.rpow_neg_one]

/-- Substituting `v = e^s` in the integrand: `e^s · oscF σ (e^s) = exp(i·(σs - 2π e^s))`. -/
lemma oscF_smul_exp (σ s : ℝ) :
    (Real.exp s) • (oscF σ (Real.exp s)) =
      Complex.exp (Complex.I * ((phase σ s : ℝ) : ℂ)) := by
  have hr : (0:ℝ) < Real.exp s := Real.exp_pos s
  have hne : ((Real.exp s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  unfold phase
  rw [oscF, Complex.real_smul, Complex.cpow_def_of_ne_zero hne,
    ← Complex.ofReal_log (le_of_lt hr), Real.log_exp, Complex.ofReal_exp]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Trivial bound: `|∫_V^{2V} v^{-1+iσ} e(-v) dv| ≤ 1` for `V ≥ 1`. -/
lemma norm_integral_oscF_le_one (σ V : ℝ) (hV : 1 ≤ V) :
    ‖∫ v in V..(2*V), oscF σ v‖ ≤ 1 := by
  have hVpos : (0:ℝ) < V := lt_of_lt_of_le one_pos hV
  have hab : V ≤ 2*V := by linarith
  have hle := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hab
      (f := oscF σ) (g := fun _ : ℝ => V⁻¹)
      (Filter.Eventually.of_forall (fun t (ht : t ∈ Set.Ioc V (2*V)) => by
        have htV : V ≤ t := le_of_lt ht.1
        have htpos : (0:ℝ) < t := lt_of_lt_of_le hVpos htV
        rw [norm_oscF σ htpos]
        exact inv_anti₀ hVpos htV))
      (intervalIntegrable_const)
  rw [intervalIntegral.integral_const] at hle
  have h2 : (2*V - V) = V := by ring
  rw [h2, smul_eq_mul] at hle
  rw [mul_inv_cancel₀ (ne_of_gt hVpos)] at hle
  exact hle

/-- First-derivative (van der Corput) bound in the regime `|σ| ≥ 8πV`. -/
lemma norm_integral_oscF_le_large (V σ : ℝ) (hV : 1 ≤ V) (hσ : 8 * Real.pi * V ≤ |σ|) :
    ‖∫ v in V..(2*V), oscF σ v‖ ≤ 8 / |σ| := by
  have hVpos : (0:ℝ) < V := lt_of_lt_of_le one_pos hV
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hσpos : 0 < |σ| := by
    have : (0:ℝ) < 8 * Real.pi * V := by positivity
    linarith
  have hlam : (0:ℝ) < |σ| / 2 := by linarith
  have hab : Real.log V ≤ Real.log (2*V) := Real.log_le_log hVpos (by linarith)
  -- phase and its derivative
  have hφ : ContDiff ℝ 2 (phase σ) := by
    unfold phase; fun_prop
  have hderiv : deriv (phase σ) = fun s => σ - 2 * Real.pi * Real.exp s := by
    unfold phase
    funext s
    have h1 : HasDerivAt (fun s : ℝ => σ * s) σ s := by simpa using (hasDerivAt_id s).const_mul σ
    have h2 : HasDerivAt (fun s : ℝ => 2 * Real.pi * Real.exp s) (2 * Real.pi * Real.exp s) s :=
      (Real.hasDerivAt_exp s).const_mul (2 * Real.pi)
    exact (h1.sub h2).deriv
  -- `deriv (phase σ)` is antitone
  have hmono : MonotoneOn (deriv (phase σ)) (Set.Icc (Real.log V) (Real.log (2*V))) ∨
      AntitoneOn (deriv (phase σ)) (Set.Icc (Real.log V) (Real.log (2*V))) := by
    right
    rw [hderiv]
    intro x _ y _ hxy
    have hexp : Real.exp x ≤ Real.exp y := Real.exp_le_exp.mpr hxy
    have := mul_le_mul_of_nonneg_left hexp (by positivity : (0:ℝ) ≤ 2 * Real.pi)
    linarith
  -- `|deriv (phase σ)| ≥ |σ|/2` on the range
  have hbound : ∀ s ∈ Set.Icc (Real.log V) (Real.log (2*V)), |σ| / 2 ≤ |deriv (phase σ) s| := by
    intro s hs
    have hs1 : V ≤ Real.exp s := by
      have := Real.exp_le_exp.mpr hs.1
      rwa [Real.exp_log hVpos] at this
    have hs2 : Real.exp s ≤ 2*V := by
      have := Real.exp_le_exp.mpr hs.2
      rwa [Real.exp_log (by positivity : (0:ℝ) < 2*V)] at this
    have hX : 2 * Real.pi * Real.exp s ≤ |σ| / 2 := by
      have h1 : 2 * Real.pi * Real.exp s ≤ 2 * Real.pi * (2*V) :=
        mul_le_mul_of_nonneg_left hs2 (by positivity)
      nlinarith [hσ, hpi]
    rw [hderiv]
    have hXnn : (0:ℝ) ≤ 2 * Real.pi * Real.exp s := by positivity
    have hkey : |σ| - 2 * Real.pi * Real.exp s ≤ |σ - 2 * Real.pi * Real.exp s| := by
      have h := abs_sub_abs_le_abs_sub σ (2 * Real.pi * Real.exp s)
      rwa [abs_of_nonneg hXnn] at h
    linarith
  have hvdc := Commons.Analysis.Oscillatory.vdc_first_deriv (a := Real.log V)
      (b := Real.log (2*V)) (φ := phase σ) (lam := |σ|/2) hab hlam hφ hmono hbound
  -- the substitution `v = e^s`
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (E := ℂ)
      (f := Real.exp) (f' := Real.exp) (g := oscF σ)
      (a := Real.log V) (b := Real.log (2 * V))
      Real.continuous_exp.continuousOn
      (fun x _ => Real.hasDerivAt_exp x)
      (fun x _ => Real.exp_nonneg x)
  rw [Real.exp_log hVpos, Real.exp_log (by positivity : (0:ℝ) < 2*V)] at hsub
  have hcongr : ∫ x in Real.log V..Real.log (2*V), Real.exp x • (oscF σ ∘ Real.exp) x
      = ∫ x in Real.log V..Real.log (2*V), Complex.exp (Complex.I * ((phase σ x : ℝ) : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [Function.comp_apply]
    exact oscF_smul_exp σ x
  have hmain : ‖∫ v in V..(2*V), oscF σ v‖
      = ‖∫ x in Real.log V..Real.log (2*V), Complex.exp (Complex.I * ((phase σ x : ℝ) : ℂ))‖ := by
    rw [← hsub, hcongr]
  rw [hmain]
  calc ‖∫ x in Real.log V..Real.log (2*V), Complex.exp (Complex.I * ((phase σ x : ℝ) : ℂ))‖
      ≤ 4 / (|σ|/2) := hvdc
    _ = 8 / |σ| := by rw [div_div_eq_mul_div]; norm_num

theorem osc_integral_bound : ∃ C : ℝ, 0 < C ∧ ∀ (V : ℝ), 1 ≤ V → ∀ σ : ℝ,
    ‖∫ v in V..(2 * V), ((v : ℂ) ^ (Complex.I * (σ : ℂ) - 1)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (v : ℂ)))‖
      ≤ C * V / Real.sqrt (1 + |σ|) := by
  refine ⟨100, by norm_num, ?_⟩
  intro V hV σ
  have hVpos : (0:ℝ) < V := lt_of_lt_of_le one_pos hV
  have hsig : (0:ℝ) ≤ |σ| := abs_nonneg σ
  by_cases hcase : 8 * Real.pi * V ≤ |σ|
  · have hbig := norm_integral_oscF_le_large V σ hV hcase
    have hsig1 : (1:ℝ) ≤ |σ| := by
      have : (1:ℝ) ≤ 8 * Real.pi * V := by nlinarith [Real.pi_gt_three, hV]
      linarith
    have hsigeq : 0 < |σ| := lt_of_lt_of_le one_pos hsig1
    have hsqrt : Real.sqrt (1 + |σ|) ≤ 2 * |σ| := by
      have hs : 1 + |σ| ≤ (2 * |σ|)^2 := by
        have h : (0:ℝ) ≤ (|σ| - 1) * (4 * |σ| + 3) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith [h]
      calc Real.sqrt (1 + |σ|) ≤ Real.sqrt ((2 * |σ|)^2) := Real.sqrt_le_sqrt hs
        _ = 2 * |σ| := Real.sqrt_sq (by positivity)
    have hspos : 0 < Real.sqrt (1 + |σ|) := Real.sqrt_pos.mpr (by positivity)
    calc ‖∫ v in V..(2*V), oscF σ v‖ ≤ 8 / |σ| := hbig
      _ ≤ 100 * V / Real.sqrt (1 + |σ|) := by
          rw [div_le_div_iff₀ hsigeq hspos]
          have h16 : (16:ℝ) ≤ 100 * V := by nlinarith [hV]
          have h3 : 16 * |σ| ≤ 100 * V * |σ| := by
            have := mul_le_mul_of_nonneg_right h16 hsig
            linarith
          have h2 : 8 * Real.sqrt (1 + |σ|) ≤ 8 * (2 * |σ|) :=
            mul_le_mul_of_nonneg_left hsqrt (by norm_num)
          linarith
  · push Not at hcase
    have hone := norm_integral_oscF_le_one σ V hV
    have hsqrt2 : Real.sqrt (1 + |σ|) ≤ 100 * V := by
      have h1 : 1 + |σ| ≤ (100*V)^2 := by
        have hp : 8 * Real.pi * V < 32 * V := by nlinarith [Real.pi_lt_four, hV]
        nlinarith [hcase, hp, hV]
      calc Real.sqrt (1 + |σ|) ≤ Real.sqrt ((100*V)^2) := Real.sqrt_le_sqrt h1
        _ = 100 * V := Real.sqrt_sq (by positivity)
    have hspos : 0 < Real.sqrt (1 + |σ|) := Real.sqrt_pos.mpr (by positivity)
    calc ‖∫ v in V..(2*V), oscF σ v‖ ≤ 1 := hone
      _ ≤ 100 * V / Real.sqrt (1 + |σ|) := by
          rw [le_div_iff₀ hspos]
          linarith

end

end Work.GM.S2

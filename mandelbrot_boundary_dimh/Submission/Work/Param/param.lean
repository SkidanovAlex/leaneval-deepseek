import Mathlib
import ChallengeDeps
import Submission.Work.Interfaces.Basic
import Submission.Work.Param.Basic
import Submission.Work.Param.Interior
import Submission.Work.Param.critical_orbit

/-! Guidance from the project lead (the requester): for real `α ∈ (0,1)`,
`cOfAlpha α = λ/2 - λ²/4` with `λ = exp (2πiα)` lies on the boundary of the Mandelbrot set.
The proof uses the conjugacy `Tc (cOfLam λ) (x + λ/2) = Q λ x + λ/2`, Lemma A
(`Work.Param.critical_orbit`: for `‖λ‖ < 1` the critical orbit of `Q λ` converges to `0`), and
Lemma B (`Work.Param.not_mem_interior_of_unit`: for `‖λ‖ = 1` the parameter `cOfLam λ` is not
interior to `M`, via Montel + the identity theorem + Baire + a degree count). -/

namespace Work.Param
open MandelDim Filter Topology
open LeanEval.Dynamics.MandelbrotBoundary
noncomputable section

theorem mem_mandelbrot_of_critical_orbit (l : ℂ)
    (h : Tendsto (fun n : ℕ => (Q l)^[n] (-(l / 2))) atTop (𝓝 0)) :
    cOfLam l ∈ Mandelbrot := by
  obtain ⟨R, hR⟩ := (h.add_const (l / 2)).norm.bddAbove_range
  exact ⟨R, fun n => by rw [Tc_cOfLam_iterate_zero]; exact hR ⟨n, rfl⟩⟩

theorem exp_two_pi_I_ne_one {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ)) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    intro hz
    have him := congrArg Complex.im hz
    simp [Complex.mul_im, Complex.mul_re] at him
  have h2 : (α : ℂ) = (n : ℂ) :=
    mul_left_cancel₀ hne (by rw [hn]; ring)
  have h5 : ((n : ℤ) : ℂ) = ((α : ℝ) : ℂ) := by rw [← h2]
  have h4 : (n : ℝ) = α := Complex.ofReal_inj.mp (by simpa using h5)
  have hn0 : (0 : ℝ) < (n : ℝ) := by rw [h4]; exact hα0
  have hnlt : (n : ℝ) < 1 := by rw [h4]; exact hα1
  have hlt : n < 1 := by exact_mod_cast hnlt
  have hgt : (0 : ℤ) < n := by exact_mod_cast hn0
  omega

theorem norm_exp_two_pi_I (α : ℝ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

/-- The critical-point orbit `(Q l)^[n] (-l/2)` converges to `0` for every `‖l‖ < 1`
(Koenigs linearisation + analytic continuation up to the critical value, `Work.Param.critical_orbit`). -/
theorem critical_orbit_tendsto (l : ℂ) (hl : ‖l‖ < 1) :
    Tendsto (fun n : ℕ => (Q l)^[n] (-(l / 2))) atTop (𝓝 0) :=
  critical_orbit l hl

/-- **PARAM**: the main-cardioid boundary lies in the boundary of the Mandelbrot set.

For real `α ∈ (0,1)` put `lam = exp (2πiα)`, `‖lam‖ = 1`, `lam ≠ 1`, and `c₀ = cOfAlpha α =
cOfLam lam`.  For `0 < t < 1` the parameter `cOfLam (t * lam)` is in `M` (the multiplier `t * lam`
has modulus `t < 1`, so the critical orbit converges — `Work.Param.critical_orbit`), hence by
closedness of `M` (`MsetStatement`) its limit `c₀` is in `M`.  On the other hand
`Work.Param.not_mem_interior_of_unit` shows `c₀ ∉ interior M`.  -/
theorem param (hM : MsetStatement) : ParamStatement := by
  intro α hα0 hα1
  have hcrit : ∀ l : ℂ, ‖l‖ < 1 →
      Tendsto (fun n : ℕ => (Q l)^[n] (-(l / 2))) atTop (𝓝 0) := critical_orbit_tendsto
  set lam : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (α : ℂ)) with hlam
  have hnorm : ‖lam‖ = 1 := by rw [hlam]; exact norm_exp_two_pi_I α
  have hne1 : lam ≠ 1 := by rw [hlam]; exact exp_two_pi_I_ne_one hα0 hα1
  have hc0 : cOfAlpha α = cOfLam lam := by
    rw [hlam]; exact cOfAlpha_eq (α : ℂ)
  have hmemM : cOfLam lam ∈ Mandelbrot := by
    have hbase : Tendsto (fun k : ℕ => (1 - 1 / ((k : ℝ) + 1) : ℝ)) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hlim : Tendsto (fun k : ℕ => (((1 - 1 / ((k : ℝ) + 1) : ℝ)) : ℂ) * lam) atTop
        (𝓝 lam) := by
      simpa using hbase.ofReal.mul (tendsto_const_nhds (x := lam))
    have hmain : Tendsto (fun k : ℕ => cOfLam ((((1 - 1 / ((k : ℝ) + 1) : ℝ)) : ℂ) * lam))
        atTop (𝓝 (cOfLam lam)) :=
      differentiable_cOfLam.continuous.continuousAt.tendsto.comp hlim
    refine hM.1.mem_of_tendsto hmain (Eventually.of_forall fun k => ?_)
    have hk_pos : 0 ≤ 1 - 1 / ((k : ℝ) + 1) := by
      have : 1 / ((k : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [show (0 : ℝ) ≤ (k : ℝ) from Nat.cast_nonneg k]
      linarith
    have hk_lt : (1 - 1 / ((k : ℝ) + 1) : ℝ) < 1 := by
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      linarith
    have hk_norm : ‖(((1 - 1 / ((k : ℝ) + 1) : ℝ)) : ℂ) * lam‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk_pos, hnorm, mul_one]
      exact hk_lt
    exact mem_mandelbrot_of_critical_orbit (((1 - 1 / ((k : ℝ) + 1) : ℝ) : ℂ) * lam)
      (hcrit (((1 - 1 / ((k : ℝ) + 1) : ℝ) : ℂ) * lam) hk_norm)
  have hnotint : cOfLam lam ∉ interior Mandelbrot := not_mem_interior_of_unit hM hcrit hnorm
  rw [hc0, show frontier Mandelbrot = closure Mandelbrot \ interior Mandelbrot from rfl,
    Set.mem_sdiff]
  exact ⟨by rw [hM.1.closure_eq]; exact hmemM, hnotint⟩

end

end Work.Param

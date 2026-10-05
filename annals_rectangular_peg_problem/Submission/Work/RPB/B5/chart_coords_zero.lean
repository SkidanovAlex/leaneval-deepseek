import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.Defs
import Submission.Work.RPB.B5.exp_chordPhase_zero_sub
import Submission.Work.RPV.chordPS_circle_stdZ

/-!
# B5: the chord chart at `τ = 0`, `x ≤ 0`

For `x ∈ (-√2, 0]` the middle reparametrisation gives a chord parameter
`ρ = D.rho 0 x t ∈ (0, π²/4]`, so `r = √ρ ∈ (0, π/2]` and the chart is the chord surface of the
unit circle:
`D.W 0 t ρ = Work.RPB.chordSurf CI.c a 0 t r`.

At `τ = 0` the curve is the unit circle (`CI.start`), and the phase `a 0 t r` is a lift of
`t + π/2` (`Work.RPB.B5.exp_chordPhase_zero_sub`, here extended to the endpoint `r = π/2`).
The chord `e^{i(t+r)} - e^{i(t-r)} = 2 sin r · i · e^{it}` then has reduced coordinate
`-√2 cos r · i`, so

* `(D.W 0 t ρ).1.1 = -√2 cos r`, `(D.W 0 t ρ).1.2 = a 0 t r`, `(D.W 0 t ρ).2 = 0`.

These are the three coordinates of `stdZ (-(√2 cos r)) (a 0 t r)`; this is the `τ = 0`, `x ≤ 0`
chart branch used in `lagData_start` and `lagData_std`.
-/

open Complex Real

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- The chord phase at `τ = 0` for the range `r ∈ (0, π/2]` (the range of the middle
reparametrisation, whose value at `x = 0` is `r = π/2`).  This is
`Work.RPB.B5.exp_chordPhase_zero_sub` with the endpoint `r = π/2` included. -/
private theorem exp_chordPhase_zero_sub' (CI : Work.RPV.CurveIsotopy)
    (a : ℝ → ℝ → ℝ → ℝ) (ha : Work.RPB.IsChordPhase CI.c a) (t : ℝ) {r : ℝ}
    (hr : r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2)) :
    Complex.exp (((a 0 t r - (t + Real.pi / 2)) : ℝ) * Complex.I) = 1 := by
  have hr0 : 0 < r := hr.1
  have hrπ : r < Real.pi := by linarith [hr.2, Real.pi_pos]
  have hmem : r ∈ Set.Ioo (0 : ℝ) Real.pi := ⟨hr0, hrπ⟩
  have hsin : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr0 hrπ
  -- the chord of the unit circle, as an explicit multiple of `exp ((t + π/2) * I)`
  have hval : ((2 * Real.sin r : ℝ) : ℂ) * Complex.exp (((t + Real.pi / 2) : ℝ) * Complex.I)
      = Work.RPB.chordVec CI.c 0 t r := by
    rw [Work.RPB.B2.chordVec_circle CI.c CI.start t r]
    push_cast
    ring
  -- whose norm is `2 sin r`
  have hnorm : ‖Work.RPB.chordVec CI.c 0 t r‖ = 2 * Real.sin r := by
    rw [← hval, norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < 2 * Real.sin r)]
  have hne : ((2 * Real.sin r : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; linarith
  -- `IsChordPhase` says the chord is `‖chord‖ * exp (a * I)`; cancelling the positive factor
  -- identifies the two exponential directions
  have hdir := ha.2.1 0 (by norm_num) t r hmem
  rw [hnorm, ← hval] at hdir
  have hexp : Complex.exp (((t + Real.pi / 2) : ℝ) * Complex.I)
      = Complex.exp (a 0 t r * Complex.I) := mul_left_cancel₀ hne hdir
  have hsub : (((a 0 t r - (t + Real.pi / 2)) : ℝ) : ℂ) * Complex.I
      = a 0 t r * Complex.I - ((t + Real.pi / 2) : ℝ) * Complex.I := by
    push_cast; ring
  rw [hsub, Complex.exp_sub, hexp, div_self (Complex.exp_ne_zero _)]

/-- If `exp ((φ - (t + π/2)) I) = 1` then `exp (-φ I) = exp (-(t + π/2) I)`: the phase `φ` differs
from `t + π/2` by an integer multiple of `2π`. -/
private lemma exp_neg_eq_of_exp_sub_eq_one {t φ : ℝ}
    (h : Complex.exp (((φ - (t + Real.pi / 2)) : ℝ) * Complex.I) = 1) :
    Complex.exp (-(φ : ℂ) * Complex.I) =
      Complex.exp (-(((t + Real.pi / 2) : ℝ) : ℂ) * Complex.I) := by
  have h1 : Complex.exp (-(φ : ℂ) * Complex.I)
      * Complex.exp (((φ - (t + Real.pi / 2) : ℝ) : ℂ) * Complex.I)
      = Complex.exp (-(((t + Real.pi / 2) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [h, mul_one] at h1
  exact h1

/-- The reduced chord `(e^{i(t+r)}, e^{i(t-r)})` with phase `φ`, when `φ ≡ t + π/2 (mod 2π)`,
has `chordPS`-coordinates `(-√2 cos r, φ, 0)`. -/
private lemma chordPS_circle_coords (t r φ : ℝ)
    (hφ : Complex.exp (((φ - (t + Real.pi / 2)) : ℝ) * Complex.I) = 1) :
    (Work.RPV.chordPS (Complex.exp (((t + r) : ℝ) * Complex.I))
        (Complex.exp (((t - r) : ℝ) * Complex.I)) φ).1.1 = -Real.sqrt 2 * Real.cos r ∧
    (Work.RPV.chordPS (Complex.exp (((t + r) : ℝ) * Complex.I))
        (Complex.exp (((t - r) : ℝ) * Complex.I)) φ).1.2 = φ ∧
    (Work.RPV.chordPS (Complex.exp (((t + r) : ℝ) * Complex.I))
        (Complex.exp (((t - r) : ℝ) * Complex.I)) φ).2 = 0 := by
  have he := exp_neg_eq_of_exp_sub_eq_one hφ
  have hkey := Work.RPV.chordPS_circle_stdZ t r
  refine ⟨?_, ?_, ?_⟩
  · -- the first coordinate only depends on `exp (-φ I)`, which equals `exp (-(t + π/2) I)`
    have hstd := congrArg (fun x : Work.RPV.PS => x.1.1) hkey
    simp only [Work.RPV.chordPS, Work.RPV.stdZ] at hstd
    simp only [Work.RPV.chordPS]
    rw [he, hstd]
    ring
  · simp only [Work.RPV.chordPS]
  · -- the last coordinate pair `(u.re, K₀)`: the real part vanishes because `exp (-φ I)`
    -- equals `exp (-(t + π/2) I)`, the modulus part since both points lie on the unit circle
    have hstd := congrArg (fun x : Work.RPV.PS => x.2) hkey
    simp only [Work.RPV.chordPS, Work.RPV.stdZ] at hstd
    simp only [Work.RPV.chordPS]
    rw [he]
    exact hstd

/-- At `τ = 0` the chord chart over the parameter `r ∈ (0, π/2]` is the zero-section point
`stdZ (-(√2 cos r)) (a 0 t r)`. -/
private lemma chordSurf_zero_coords (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) {t r : ℝ} (hr : r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2)) :
    (Work.RPB.chordSurf CI.c a 0 t r).1.1 = -Real.sqrt 2 * Real.cos r ∧
    (Work.RPB.chordSurf CI.c a 0 t r).1.2 = a 0 t r ∧
    (Work.RPB.chordSurf CI.c a 0 t r).2 = 0 := by
  have hφ := exp_chordPhase_zero_sub' CI a ha t hr
  have h := chordPS_circle_coords t r (a 0 t r) hφ
  rw [Work.RPB.chordSurf, CI.start (t + r), CI.start (t - r)]
  exact h

theorem chart_coords_zero (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a) :
    ∀ x : ℝ, -Real.sqrt 2 < x → x ≤ 0 → ∀ t : ℝ,
      (D.W 0 t (D.rho 0 x t)).1.1 = -Real.sqrt 2 * Real.cos (Real.sqrt (D.rho 0 x t)) ∧
      (D.W 0 t (D.rho 0 x t)).1.2 = a 0 t (Real.sqrt (D.rho 0 x t)) ∧
      (D.W 0 t (D.rho 0 x t)).2 = 0 := by
  intro x hx1 hx0 t
  obtain ⟨hrho0, hrhole⟩ := D.hrhoval 0 (by norm_num) x ⟨hx1, hx0⟩ t
  set r := Real.sqrt (D.rho 0 x t) with hrdef
  have hrpos : 0 < r := Real.sqrt_pos.mpr hrho0
  have hrle : r ≤ Real.pi / 2 := by
    calc r ≤ Real.sqrt (Real.pi ^ 2 / 4) := Real.sqrt_le_sqrt hrhole
      _ = Real.pi / 2 := by
          rw [show Real.pi ^ 2 / 4 = (Real.pi / 2) ^ 2 by ring]
          exact Real.sqrt_sq (by positivity)
  have hrsq : r ^ 2 = D.rho 0 x t := Real.sq_sqrt hrho0.le
  have hW : D.W 0 t (D.rho 0 x t) = Work.RPB.chordSurf CI.c a 0 t r := by
    rw [← hrsq]
    exact D.hWchord 0 (by norm_num) t r ⟨hrpos, hrle⟩
  rw [hW]
  exact chordSurf_zero_coords CI a ha ⟨hrpos, hrle⟩

end Work.RPB.B5

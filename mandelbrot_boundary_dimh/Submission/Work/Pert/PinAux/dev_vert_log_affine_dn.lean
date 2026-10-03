import Mathlib
import Submission.Work.Pert.PinAux.Basic
import Submission.Work.Pert.Pin3.dev_vert_log

namespace Work.Pert.PinAux

open MeasureTheory

set_option linter.unusedVariables false

/-!
# `Work.Pert.PinAux.dev_vert_log_affine_dn`

Logarithmic bound for the displacement of `Dev := Φ - id` along a vertical segment
`s ↦ x + i s`, `s ∈ [T, M]` in the **downward / negative** regime `T ≤ M < 0`, `M < t₀`,
when the deviation of the derivative is bounded by the three-term majorant
`A / (t₀ - s) + B / (-s) + cc`.

This is the mirror of `Work.Pert.PinAux.dev_vert_log_affine` (which lives in the regime
`0 < T ≤ M`, `t₀ < T` and uses the majorant `A / (s - t₀) + B / s + cc`).  The arguments of
the logarithms acquire a sign: the antiderivative is now
`s ↦ -A log(t₀ - s) - B log(-s) + cc s`, so

  `‖Dev z_M - Dev z_T‖ ≤ ∫_T^M (A / (t₀ - s) + B / (-s) + cc) ds
    = A log((t₀ - T)/(t₀ - M)) + B log(T/M) + cc (M - T)`

(the second log is `log((-T)/(-M)) = log(T/M)`, using that `T, M < 0`).

The fundamental estimate along the segment is `Work.Pert.Pin3.dev_vert_le_of_diffAt` (in the
`+I` parametrisation, which is the one used here), and the integral of the majorant is evaluated
in closed form with the antiderivative above.
-/

theorem dev_vert_log_affine_dn {Φ : ℂ → ℂ} {x t₀ T M A B cc : ℝ}
    (hTM : T ≤ M) (hMt : M < t₀) (hM0 : M < 0)
    (hdiff : ∀ s ∈ Set.Icc T M, DifferentiableAt ℂ Φ ((x : ℂ) + (s : ℂ) * Complex.I))
    (hbound : ∀ s ∈ Set.Icc T M,
      ‖deriv Φ ((x : ℂ) + (s : ℂ) * Complex.I) - 1‖ ≤ A / (t₀ - s) + B / (-s) + cc)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ cc) :
    ‖Work.Pert.PinAux.Dev Φ ((x : ℂ) + (M : ℂ) * Complex.I)
        - Work.Pert.PinAux.Dev Φ ((x : ℂ) + (T : ℂ) * Complex.I)‖
      ≤ A * Real.log ((t₀ - T) / (t₀ - M)) + B * Real.log (T / M) + cc * (M - T) := by
  -- positivity of the quantities occurring in the logarithms / denominators
  have hdenM : 0 < t₀ - M := by linarith
  have hdenT : 0 < t₀ - T := by linarith
  have hnegM : 0 < -M := by linarith
  have hnegT : 0 < -T := by linarith
  -- the majorant is continuous on the segment (all denominators are positive there)
  have hcont : ContinuousOn (fun s : ℝ => A / (t₀ - s) + B / (-s) + cc) (Set.Icc T M) := by
    refine ContinuousOn.add (ContinuousOn.add ?_ ?_) continuousOn_const
    · refine ContinuousOn.div₀ continuousOn_const
        (continuousOn_const.sub continuousOn_id) ?_
      intro s hs
      have h : s < t₀ := lt_of_le_of_lt hs.2 hMt
      exact ne_of_gt (by linarith)
    · refine ContinuousOn.div₀ continuousOn_const continuousOn_id.neg ?_
      intro s hs
      have h : 0 < -s := by have := hs.2; linarith
      exact ne_of_gt h
  -- the fundamental estimate "displacement ≤ integral of the speed"
  have hmain := Work.Pert.Pin3.dev_vert_le_of_diffAt (x := x) (y₁ := T) (y₂ := M)
    (g := fun s : ℝ => A / (t₀ - s) + B / (-s) + cc) hTM hdiff hbound hcont
  -- `Dev` unfolded
  have hdev : Dev Φ ((x : ℂ) + (M : ℂ) * Complex.I) - Dev Φ ((x : ℂ) + (T : ℂ) * Complex.I)
      = (Φ ((x : ℂ) + (M : ℂ) * Complex.I) - ((x : ℂ) + (M : ℂ) * Complex.I))
        - (Φ ((x : ℂ) + (T : ℂ) * Complex.I) - ((x : ℂ) + (T : ℂ) * Complex.I)) := by
    rw [Dev, Dev]
  rw [hdev]
  -- the antiderivative of the majorant: `s ↦ -A log(t₀ - s) - B log(-s) + cc s`
  have hderiv : ∀ s ∈ Set.uIcc T M,
      HasDerivAt (fun u : ℝ => (-A) * Real.log (t₀ - u) + (-B) * Real.log (-u) + cc * u)
        (A / (t₀ - s) + B / (-s) + cc) s := by
    intro s hs
    rw [Set.uIcc_of_le hTM] at hs
    have hs1 : 0 < t₀ - s := by have := hs.2; linarith
    have hs2 : 0 < -s := by have := hs.2; linarith
    have h1 : HasDerivAt (fun u : ℝ => t₀ - u) (-1) s := (hasDerivAt_id s).const_sub t₀
    have h2 : HasDerivAt (fun u : ℝ => Real.log (t₀ - u)) ((-1) / (t₀ - s)) s :=
      h1.log (ne_of_gt hs1)
    have h3 : HasDerivAt (fun u : ℝ => (-A) * Real.log (t₀ - u))
        ((-A) * ((-1) / (t₀ - s))) s := h2.const_mul (-A)
    have h4 : HasDerivAt (fun u : ℝ => -u) (-1) s := (hasDerivAt_id s).neg
    have h5 : HasDerivAt (fun u : ℝ => Real.log (-u)) ((-1) / (-s)) s :=
      h4.log (ne_of_gt hs2)
    have h6 : HasDerivAt (fun u : ℝ => (-B) * Real.log (-u))
        ((-B) * ((-1) / (-s))) s := h5.const_mul (-B)
    have h7 : HasDerivAt (fun u : ℝ => cc * u) cc s := by
      simpa using (hasDerivAt_id s).const_mul cc
    have hsum := (h3.add h6).add h7
    refine hsum.congr_deriv ?_
    ring
  have hint : IntervalIntegrable (fun s : ℝ => A / (t₀ - s) + B / (-s) + cc) volume T M := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hTM]
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- the closed form of the integral
  have key : ((-A) * Real.log (t₀ - M) + (-B) * Real.log (-M) + cc * M)
        - ((-A) * Real.log (t₀ - T) + (-B) * Real.log (-T) + cc * T)
      = A * Real.log ((t₀ - T) / (t₀ - M)) + B * Real.log (T / M) + cc * (M - T) := by
    have hratio : T / M = (-T) / (-M) := by ring
    rw [hratio, Real.log_div (ne_of_gt hdenT) (ne_of_gt hdenM),
      Real.log_div (ne_of_gt hnegT) (ne_of_gt hnegM)]
    ring
  calc ‖(Φ ((x : ℂ) + (M : ℂ) * Complex.I) - ((x : ℂ) + (M : ℂ) * Complex.I))
        - (Φ ((x : ℂ) + (T : ℂ) * Complex.I) - ((x : ℂ) + (T : ℂ) * Complex.I))‖
      ≤ ∫ s in T..M, (A / (t₀ - s) + B / (-s) + cc) := hmain
    _ = ((-A) * Real.log (t₀ - M) + (-B) * Real.log (-M) + cc * M)
        - ((-A) * Real.log (t₀ - T) + (-B) * Real.log (-T) + cc * T) := hF
    _ = A * Real.log ((t₀ - T) / (t₀ - M)) + B * Real.log (T / M) + cc * (M - T) := key

end Work.Pert.PinAux

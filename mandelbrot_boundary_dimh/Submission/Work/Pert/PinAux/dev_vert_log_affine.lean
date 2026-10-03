import Mathlib
import Submission.Work.Pert.PinAux.Basic
import Submission.Work.Pert.Pin3.dev_vert_log

namespace Work.Pert.PinAux

open MeasureTheory

set_option linter.unusedVariables false

/-!
# `Work.Pert.PinAux.dev_vert_log_affine`

Logarithmic bound for the displacement of `Dev := Φ - id` along a vertical segment
`s ↦ x + i s`, `s ∈ [T, M]`, when the deviation of the derivative is bounded by the
**three-term** majorant `A / (s - t₀) + B / s + cc` (the extra constant term `cc` is what
distinguishes this from `Work.Pert.Pin3.dev_vert_log`).

The proof is the statement "displacement ≤ integral of the speed": the difference of `Dev`
along the segment is the integral of `(Φ' - 1) · I`, whose norm is `‖Φ' - 1‖`, so

  `‖Dev z_M - Dev z_T‖ ≤ ∫_T^M (A / (s - t₀) + B / s + cc) ds
    = A log((M - t₀)/(T - t₀)) + B log(M/T) + cc (M - T)`.

The fundamental estimate along the segment from *pointwise* complex differentiability is
`Work.Pert.Pin3.dev_vert_le_of_diffAt` (no neighbourhood hypothesis is needed), and the
integral of the majorant is evaluated in closed form with the antiderivative
`s ↦ A log(s - t₀) + B log s + cc s`.
-/

theorem dev_vert_log_affine {Φ : ℂ → ℂ} {x t₀ T M A B cc : ℝ}
    (hTM : T ≤ M) (hTt : t₀ < T) (hT0 : 0 < T)
    (hdiff : ∀ s ∈ Set.Icc T M, DifferentiableAt ℂ Φ ((x : ℂ) + (s : ℂ) * Complex.I))
    (hbound : ∀ s ∈ Set.Icc T M,
      ‖deriv Φ ((x : ℂ) + (s : ℂ) * Complex.I) - 1‖ ≤ A / (s - t₀) + B / s + cc)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ cc) :
    ‖Work.Pert.PinAux.Dev Φ ((x : ℂ) + (M : ℂ) * Complex.I)
        - Work.Pert.PinAux.Dev Φ ((x : ℂ) + (T : ℂ) * Complex.I)‖
      ≤ A * Real.log ((M - t₀) / (T - t₀)) + B * Real.log (M / T) + cc * (M - T) := by
  -- positivity of the quantities that occur in the logarithms
  have hMt : 0 < M - t₀ := by linarith
  have hTt' : 0 < T - t₀ := by linarith
  have hMpos : 0 < M := lt_of_lt_of_le hT0 hTM
  -- the majorant is continuous on the segment (all denominators are positive there)
  have hcont : ContinuousOn (fun s : ℝ => A / (s - t₀) + B / s + cc) (Set.Icc T M) := by
    refine ContinuousOn.add (ContinuousOn.add ?_ ?_) continuousOn_const
    · refine ContinuousOn.div₀ continuousOn_const
        (continuousOn_id.sub continuousOn_const) ?_
      intro s hs
      have h : t₀ < s := lt_of_lt_of_le hTt hs.1
      exact ne_of_gt (by linarith)
    · refine ContinuousOn.div₀ continuousOn_const continuousOn_id ?_
      intro s hs
      have h : 0 < s := lt_of_lt_of_le hT0 hs.1
      exact ne_of_gt h
  -- the fundamental estimate "displacement ≤ integral of the speed"
  have hmain := Work.Pert.Pin3.dev_vert_le_of_diffAt (x := x) (y₁ := T) (y₂ := M)
    (g := fun s : ℝ => A / (s - t₀) + B / s + cc) hTM hdiff hbound hcont
  -- `Dev` unfolded
  have hdev : Dev Φ ((x : ℂ) + (M : ℂ) * Complex.I) - Dev Φ ((x : ℂ) + (T : ℂ) * Complex.I)
      = (Φ ((x : ℂ) + (M : ℂ) * Complex.I) - ((x : ℂ) + (M : ℂ) * Complex.I))
        - (Φ ((x : ℂ) + (T : ℂ) * Complex.I) - ((x : ℂ) + (T : ℂ) * Complex.I)) := by
    rw [Dev, Dev]
  rw [hdev]
  -- the antiderivative of the majorant
  have hderiv : ∀ s ∈ Set.uIcc T M,
      HasDerivAt (fun u : ℝ => A * Real.log (u - t₀) + B * Real.log u + cc * u)
        (A / (s - t₀) + B / s + cc) s := by
    intro s hs
    rw [Set.uIcc_of_le hTM] at hs
    have hs1 : 0 < s - t₀ := by have := hs.1; linarith
    have hs2 : 0 < s := by have := hs.1; linarith
    have h1 : HasDerivAt (fun u : ℝ => u - t₀) 1 s := (hasDerivAt_id s).sub_const t₀
    have h2 : HasDerivAt (fun u : ℝ => Real.log (u - t₀)) (1 / (s - t₀)) s :=
      h1.log (ne_of_gt hs1)
    have h3 : HasDerivAt (fun u : ℝ => A * Real.log (u - t₀)) (A * (1 / (s - t₀))) s :=
      h2.const_mul A
    have h4 : HasDerivAt (fun u : ℝ => Real.log u) (1 / s) s := by
      simpa [one_div] using Real.hasDerivAt_log (ne_of_gt hs2)
    have h5 : HasDerivAt (fun u : ℝ => B * Real.log u) (B * (1 / s)) s := h4.const_mul B
    have h6 : HasDerivAt (fun u : ℝ => cc * u) cc s := by
      simpa using (hasDerivAt_id s).const_mul cc
    have hsum := (h3.add h5).add h6
    refine (hsum.congr_deriv ?_)
    ring
  have hint : IntervalIntegrable (fun s : ℝ => A / (s - t₀) + B / s + cc) volume T M := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hTM]
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  -- the closed form of the integral
  have key : (A * Real.log (M - t₀) + B * Real.log M + cc * M)
        - (A * Real.log (T - t₀) + B * Real.log T + cc * T)
      = A * Real.log ((M - t₀) / (T - t₀)) + B * Real.log (M / T) + cc * (M - T) := by
    rw [Real.log_div (ne_of_gt hMt) (ne_of_gt hTt'),
      Real.log_div (ne_of_gt hMpos) (ne_of_gt hT0)]
    ring
  calc ‖(Φ ((x : ℂ) + (M : ℂ) * Complex.I) - ((x : ℂ) + (M : ℂ) * Complex.I))
        - (Φ ((x : ℂ) + (T : ℂ) * Complex.I) - ((x : ℂ) + (T : ℂ) * Complex.I))‖
      ≤ ∫ s in T..M, (A / (s - t₀) + B / s + cc) := hmain
    _ = (A * Real.log (M - t₀) + B * Real.log M + cc * M)
        - (A * Real.log (T - t₀) + B * Real.log T + cc * T) := hF
    _ = A * Real.log ((M - t₀) / (T - t₀)) + B * Real.log (M / T) + cc * (M - T) := key

end Work.Pert.PinAux

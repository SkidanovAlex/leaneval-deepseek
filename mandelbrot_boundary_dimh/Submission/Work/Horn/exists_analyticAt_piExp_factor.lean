import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Horn.basic

/-!
# Local logarithm of an analytic function at `0`

If `u` is analytic at `0` with `u 0 = 1`, then near `0` it can be written as
`u ζ = piExp (H ζ) = exp (2πi H ζ)` with `H` analytic at `0` and `H 0 = 0`.

The construction is the principal branch of the complex logarithm: `u` is non-zero on a
neighbourhood of `0` (since `u 0 = 1` lies in the slit plane and `Complex.slitPlane` is open),
and there `H ζ = log (u ζ) / (2πi)` satisfies `piExp (H ζ) = exp (log (u ζ)) = u ζ`.
-/

namespace Work.Horn

open Filter

theorem exists_analyticAt_piExp_factor (u : ℂ → ℂ) (hu : AnalyticAt ℂ u 0) (h1 : u 0 = 1) :
    ∃ H : ℂ → ℂ, H 0 = 0 ∧ AnalyticAt ℂ H 0 ∧ DifferentiableAt ℂ H 0 ∧
      ∀ᶠ ζ in nhds (0 : ℂ), u ζ = MandelDim.piExp (H ζ) := by
  -- `u 0 = 1` is in the slit plane, so `u` is non-zero on a neighbourhood of `0`
  have h0mem : u 0 ∈ Complex.slitPlane := by rw [h1]; exact Complex.one_mem_slitPlane
  have hnonzero : ∀ᶠ ζ in nhds (0 : ℂ), u ζ ≠ 0 :=
    (hu.continuousAt.eventually (Complex.isOpen_slitPlane.mem_nhds h0mem)).mono
      (fun _ h => Complex.slitPlane_ne_zero h)
  refine ⟨fun ζ => Complex.log (u ζ) / (2 * Real.pi * Complex.I), ?_, ?_, ?_, ?_⟩
  · simp [h1, Complex.log_one]
  · exact (hu.clog h0mem).div_const (c := (2 : ℂ) * Real.pi * Complex.I)
  · exact ((hu.clog h0mem).div_const (c := (2 : ℂ) * Real.pi * Complex.I)).differentiableAt
  · filter_upwards [hnonzero] with ζ hζ
    exact (MandelDim.piExp_log_div (u ζ) hζ).symm

end Work.Horn

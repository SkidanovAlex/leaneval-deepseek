import Mathlib
import Submission.Work.Smooth.SphereJordan.Pasting
import Submission.Work.InnermostDisk.exp_eq_exp_mul_I_exists_int

namespace Work.Smooth.SphereJordan

/-- `arcPoint r` is the parametrisation `θ ↦ r • e^{iθ}` of the concentric circle of radius `r` of
the model disc; for `0 < r ≤ 1` it is injective on one period `[0, 2π)`. -/
theorem injOn_arcPoint (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hrne : r ≠ 0) : Set.InjOn (fun θ : ℝ => Work.Smooth.SphereJordan.arcPoint r θ) (Set.Ico 0 (2 * Real.pi)) := by
  intro θ1 h1 θ2 h2 h
  -- On `[0,1]` the clamped radius `max 0 (min r 1)` is `r` itself.
  have hclamp : max 0 (min r 1) = r := by rw [min_eq_left hr1, max_eq_right hr0]
  -- Coerce the equality of disc points to `ℂ`: `r * e^{iθ₁} = r * e^{iθ₂}`.
  have hcoe : ((Work.Smooth.SphereJordan.arcPoint r θ1 : Work.Smooth.Jordan.Disc) : ℂ)
      = ((Work.Smooth.SphereJordan.arcPoint r θ2 : Work.Smooth.Jordan.Disc) : ℂ) :=
    congrArg (fun z : Work.Smooth.Jordan.Disc => (z : ℂ)) h
  simp only [Work.Smooth.SphereJordan.arcPoint_coe] at hcoe
  rw [hclamp] at hcoe
  -- Cancel the nonzero factor `r`.
  have hrneC : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hrne
  have hcirc := mul_left_cancel₀ hrneC hcoe
  have hexp : Complex.exp (θ1 * Complex.I) = Complex.exp (θ2 * Complex.I) := by simpa using hcirc
  -- Two exponentials agree iff the arguments differ by an integer multiple of `2π`.
  obtain ⟨n, hn⟩ := Work.InnermostDisk.exp_eq_exp_mul_I_exists_int hexp
  have hdiff : (n : ℝ) * (2 * Real.pi) = θ1 - θ2 := by linarith [hn]
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  -- The interval bounds squeeze `n * 2π` into `(-2π, 2π)`, hence `n ∉ ℤ \ {0}`.
  have hlt : (n : ℝ) < 1 := by nlinarith [hpi, hdiff, h1.2, h2.1]
  have hgt : (-1 : ℝ) < (n : ℝ) := by nlinarith [hpi, hdiff, h1.1, h2.2]
  have hn0 : n = 0 := by
    have h1' : n < 1 := by exact_mod_cast hlt
    have h2' : (-1:ℤ) < n := by exact_mod_cast hgt
    omega
  rw [hn0] at hn
  simpa using hn

end Work.Smooth.SphereJordan

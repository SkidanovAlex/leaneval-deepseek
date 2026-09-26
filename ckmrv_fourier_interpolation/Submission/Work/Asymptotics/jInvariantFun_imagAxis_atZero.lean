import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.jInvariantFun_imagAxis_atTop

open UpperHalfPlane

namespace Work.Asymptotics

/-- **The cusp asymptotics of `j` at `t → 0` on the imaginary axis.**  Since `j(-1/τ) = j(τ)`
and `-1/(it) = i/t`, the blow-up of `j` at the cusp `t → ∞` transfers to the other cusp: `j(it)`
grows at least like `e^{2π/t}` for `t` small.  With `Work.Asymptotics.DeltaFun_imagAxis_atZero`
this gives the two-sided control of the CKMRV divisor
`Δ(τ)Δ(it)^e (j(τ)-j(it))` on the whole contour. -/
theorem jInvariantFun_imagAxis_atZero :
    ∃ c T : ℝ, 0 < c ∧ 0 < T ∧
      ∀ (t : ℝ) (ht : 0 < t), t ≤ T →
        c * Real.exp (2 * Real.pi / t) ≤ ‖Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by
  -- Transfer the cusp bound at `i∞` at the point `i/t`, which is `S • (it)`.
  obtain ⟨c, T, hc, hT, htop⟩ := jInvariantFun_imagAxis_atTop
  refine ⟨c, 1 / T, hc, one_div_pos.mpr hT, ?_⟩
  intro t ht hle
  -- `t ≤ 1/T` gives `T ≤ 1/t`, so `i/t` lies in the range of the cusp bound.
  have hTt : T ≤ 1 / t := by
    rw [le_div_iff₀ ht]
    calc T * t ≤ T * (1 / T) := mul_le_mul_of_nonneg_left hle hT.le
      _ = 1 := by field_simp
  have hb := htop (1 / t) (one_div_pos.mpr ht) hTt
  -- `S • (it) = i/t`: the modular `S`-action sends `it` to `i/t`.
  have hpt : ModularGroup.S • Work.Kernels.imagAxis t ht
      = Work.Kernels.imagAxis (1/t) (one_div_pos.mpr ht) := by
    apply UpperHalfPlane.ext
    have hcoe : ((ModularGroup.S • Work.Kernels.imagAxis t ht : ℍ) : ℂ)
        = (-((Work.Kernels.imagAxis t ht : ℍ) : ℂ))⁻¹ :=
      congrArg UpperHalfPlane.coe (UpperHalfPlane.modular_S_smul (Work.Kernels.imagAxis t ht))
    rw [hcoe]
    simp only [Work.Kernels.imagAxis, UpperHalfPlane.coe_mk]
    field_simp
    rw [show Complex.I ^ 2 = (-1 : ℂ) by rw [pow_two, Complex.I_mul_I]]
    push_cast
    ring
  -- `j` is `S`-invariant, so `j(it) = j(S • it) = j(i/t)`.
  have hjj : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis (1/t) (one_div_pos.mpr ht)) := by
    rw [← hpt]
    exact (Work.Kernels.KernelFacts.jInvariantFun_S_smul _).symm
  have hexp : 2 * Real.pi / t = 2 * Real.pi * (1/t) := by ring
  rw [hjj, hexp]
  exact hb

end Work.Asymptotics

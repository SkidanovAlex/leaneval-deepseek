import Mathlib
import Submission.Work.Kernels.Section5

namespace Work.Kernels.Section5Facts

/-- The definitional relation `K̂ = -K|^τ_{d/2}S` between the kernels (Theorem 4.9) transfers
to the kernel transforms: since the transform `kernelTransform` is complex-linear in the
kernel and the slash operator `S` acts on the `τ`-variable by `τ ↦ -1/τ` with the factor
`τ^{-d/2}`, we have

  `kernelTransform K̂ τ r = -(kernelTransform K · r |^τ_{d/2} S) τ`. -/
lemma kernelTransform_slash_S {d : ℕ} {K Khat : UpperHalfPlane → UpperHalfPlane → ℂ}
    (hKhat : ∀ τ z : UpperHalfPlane,
      Khat τ z = - (τ : ℂ) ^ (-((d : ℤ) / 2)) * K (ModularGroup.S • τ) z)
    (τ : UpperHalfPlane) (r : ℝ) :
    Work.Kernels.kernelTransform Khat τ r
      = - (SlashAction.map ((d : ℤ) / 2) ModularGroup.S
          (fun σ : UpperHalfPlane => Work.Kernels.kernelTransform K σ r)) τ := by
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_S]
  have hKaxis : ∀ t : ℝ, Work.Kernels.Kaxis Khat τ t
      = - (τ : ℂ) ^ (-((d : ℤ) / 2)) * Work.Kernels.Kaxis K (ModularGroup.S • τ) t := by
    intro t
    rw [Work.Kernels.Kaxis, Work.Kernels.Kaxis]
    by_cases h : 0 < t
    · simp only [dif_pos h]
      rw [hKhat]
    · simp only [dif_neg h]
      ring
  have hInt : (∫ t in Set.Ioi 0,
        Work.Kernels.Kaxis Khat τ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      = - (τ : ℂ) ^ (-((d : ℤ) / 2)) * ∫ t in Set.Ioi 0,
        Work.Kernels.Kaxis K (ModularGroup.S • τ) t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    have : (fun t => Work.Kernels.Kaxis Khat τ t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
        = fun t => (- (τ : ℂ) ^ (-((d : ℤ) / 2))) *
            (Work.Kernels.Kaxis K (ModularGroup.S • τ) t
              * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
      funext t; rw [hKaxis t]; ring
    rw [this]
    exact MeasureTheory.integral_const_mul _ _
  unfold Work.Kernels.kernelTransform
  rw [hInt]
  ring

end Work.Kernels.Section5Facts

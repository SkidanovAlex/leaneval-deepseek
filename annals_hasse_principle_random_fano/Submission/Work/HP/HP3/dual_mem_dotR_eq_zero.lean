import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Vero.span_realify_latOrth_inf

namespace Work.HP.HP3

/-- Any element of the dual of `realify (latOrth x)` is orthogonal to `x`:
`dotR u (toR x) = 0`.

Indeed `realify (latOrth x)` spans, over `ℝ`, the kernel of `z ↦ ∑ i, z i * (x i : ℝ)`
(`Work.HP.Vero.span_realify_latOrth_inf` with `v = w = x`), so every element of its `ℝ`-span and
hence of the dual is in that kernel. -/
theorem dual_mem_dotR_eq_zero {ι : Type*} [Fintype ι] (x : ι → ℤ) (u : ι → ℝ)
    (hu : u ∈ dualLat (realify (latOrth x))) :
    dotR u (toR x) = 0 := by
  classical
  -- `u` lies in the `ℝ`-span of `realify (latOrth x)`.
  obtain ⟨hu1, -⟩ := hu
  unfold realify at hu1
  -- That span is the kernel of the functional `z ↦ ∑ i, z i * (x i : ℝ)`.
  have hspan := Work.HP.Vero.span_realify_latOrth_inf x x
  rw [inf_idem] at hspan
  rw [hspan] at hu1
  -- Hence `u` is in the kernel, i.e. `∑ i, u i * (x i : ℝ) = 0`.
  have h : (Fintype.linearCombination ℝ (fun i => (x i : ℝ))) u = 0 :=
    (Submodule.mem_inf.mp hu1).1
  -- `dotR u (toR x)` is exactly that sum.
  simp only [dotR, toR, Fintype.linearCombination_apply, smul_eq_mul] at h ⊢
  exact h

end Work.HP.HP3

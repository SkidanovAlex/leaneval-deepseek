import Mathlib
import Submission.Work.Diff.GE.kato_deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# A smooth bump function positive only where `f` is positive

Given a smooth `f : M → ℝ` with `f x > 0`, we produce a smooth `ψ : M → ℝ` with `0 ≤ ψ ≤ 1`,
`ψ > 0 → f > 0` (i.e. `support ψ ⊆ {f > 0}`) and `ψ =ᶠ[𝓝 x] 1`.

The construction is the cheapest possible one: it uses **no** manifold bump-function machinery
(no chart, no partition of unity, hence no σ-compactness of `M`), only the pointwise cut-off

`ψ y = Real.smoothTransition (f y / (f x / 2))`,

which is smooth, takes values in `[0,1]`, is `0` for `f y ≤ 0`, and is `1` as soon as
`f y ≥ f x / 2` — a neighbourhood of `x` by continuity of `f`.
-/

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

theorem kato_bump_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (f : M → ℝ) (x : M) (hf : CMDiff ∞ f) (hpos : 0 < f x) :
    ∃ ψ : M → ℝ,
      CMDiff ∞ ψ ∧ (∀ y, 0 ≤ ψ y) ∧ (∀ y, ψ y ≤ 1) ∧
        (∀ y, 0 < ψ y → 0 < f y) ∧ (ψ =ᶠ[𝓝 x] 1) := by
  have hA : (0 : ℝ) < f x / 2 := by linarith
  refine ⟨fun y => Real.smoothTransition (f y / (f x / 2)), ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness: `smoothTransition` is `C^∞` on `ℝ` and `y ↦ f y / (f x / 2)` is smooth on `M`
    have h1 : CMDiff ∞ (fun y : M => f y / (f x / 2)) := hf.div_const _
    have hχ : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ Real.smoothTransition :=
      (Real.smoothTransition.contDiff (n := ⊤)).contMDiff
    exact hχ.comp h1
  · intro y; exact Real.smoothTransition.nonneg _
  · intro y; exact Real.smoothTransition.le_one _
  · -- `ψ` is positive only on `{t > 0}`, where `smoothTransition` vanishes
    intro y hy
    have ht : 0 < f y / (f x / 2) := by
      by_contra h
      rw [not_lt] at h
      have hy' : 0 < Real.smoothTransition (f y / (f x / 2)) := hy
      rw [Real.smoothTransition.zero_of_nonpos h] at hy'
      exact lt_irrefl 0 hy'
    have h2 : 0 < (f y / (f x / 2)) * (f x / 2) := mul_pos ht hA
    rwa [div_mul_cancel₀ _ hA.ne'] at h2
  · -- `f ≥ f x / 2` near `x`, where the transition equals `1`
    filter_upwards [hf.continuous.continuousAt.eventually
      (Ioi_mem_nhds (by linarith : f x / 2 < f x))] with y hy
    exact Real.smoothTransition.one_of_one_le ((one_le_div hA).mpr (le_of_lt hy))

end Work.Diff.GE

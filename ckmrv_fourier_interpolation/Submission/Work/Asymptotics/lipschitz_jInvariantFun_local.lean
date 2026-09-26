/-
# Local Lipschitz continuity of the `j`-invariant

The modular `j`-invariant `j = E₄³/Δ` is holomorphic on `ℍ` (a quotient of a modular form by
the nowhere vanishing cusp form `Δ`).  A holomorphic function is strictly differentiable, and a
strictly differentiable function is Lipschitz on a neighbourhood of the point of
differentiability.  Composing with the chart `UpperHalfPlane.ofComplex : ℂ → ℍ` we therefore
obtain, around every `x : ℍ`, a ball on which `j` is Lipschitz with respect to the Euclidean
distance of the upper half plane.

The proof follows the pattern already established for the modular `λ`-function in
`Submission/Work/Asymptotics/MiddleRange/exists_diffQuotient_lower_general.lean`: holomorphy on
`ℍ` upgrades (via `UpperHalfPlane.mdifferentiable_iff`) to analyticity of the lift
`j ∘ ofComplex` on the open set `{z : ℂ | 0 < z.im}`, whence `HasStrictDerivAt` at `(x : ℂ)`,
and finally `HasStrictFDerivAt.exists_lipschitzOnWith`.

## Main result

* `Work.Asymptotics.lipschitz_jInvariantFun_local`
-/
import Mathlib
import Submission.Work.Kernels.Kernels

noncomputable section

open UpperHalfPlane ModularForm
open scoped Manifold

namespace Work.Asymptotics

/-- `Δ` does not vanish on `ℍ`. -/
private lemma deltaFun_ne_zero_local (z : UpperHalfPlane) : Work.Kernels.DeltaFun z ≠ 0 := by
  simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero z

/-- `E₄` is holomorphic on `ℍ`. -/
private lemma mdifferentiable_E4Fun_local : MDiff Work.Kernels.E4Fun :=
  ModularFormClass.holo ModularForm.E₄

/-- `Δ` is holomorphic on `ℍ`. -/
private lemma mdifferentiable_DeltaFun_local : MDiff Work.Kernels.DeltaFun :=
  CuspFormClass.holo CuspForm.discriminant

/-- `j = E₄³/Δ` is holomorphic on `ℍ`. -/
private lemma mdifferentiable_jInvariantFun_local : MDiff Work.Kernels.jInvariantFun :=
  (mdifferentiable_E4Fun_local.pow 3).div mdifferentiable_DeltaFun_local
    deltaFun_ne_zero_local

/-- **`j` is locally Lipschitz** with respect to the Euclidean metric of the upper half plane:
around every `x : ℍ` there is a radius `r > 0` and a constant `L ≥ 0` such that
`‖j y - j z‖ ≤ L ‖y - z‖` for `y, z` in the ball of radius `r` about `x`. -/
theorem lipschitz_jInvariantFun_local (x : UpperHalfPlane) :
    ∃ r L : ℝ, 0 < r ∧ 0 ≤ L ∧ ∀ y z : UpperHalfPlane,
      ‖(y : ℂ) - (x : ℂ)‖ < r → ‖(z : ℂ) - (x : ℂ)‖ < r →
      ‖Work.Kernels.jInvariantFun y - Work.Kernels.jInvariantFun z‖ ≤ L * ‖(y : ℂ) - (z : ℂ)‖ := by
  -- analyticity of the lift of `j` to the upper half plane set
  have hAnaOn : AnalyticOnNhd ℂ
      (Work.Kernels.jInvariantFun ∘ ↑UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    (UpperHalfPlane.mdifferentiable_iff.mp mdifferentiable_jInvariantFun_local).analyticOnNhd
      UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hAna : AnalyticAt ℂ
      (Work.Kernels.jInvariantFun ∘ ↑UpperHalfPlane.ofComplex) (x : ℂ) :=
    hAnaOn (x : ℂ) (by simpa using x.im_pos)
  -- strict differentiability gives Lipschitz continuity on a neighbourhood
  obtain ⟨K, s, hs, hlip⟩ :=
    (hAna.hasStrictDerivAt.hasStrictFDerivAt).exists_lipschitzOnWith
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨ε, (K : ℝ), hε, K.coe_nonneg, ?_⟩
  intro y z hy hz
  have hy' : (y : ℂ) ∈ s := hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hy)
  have hz' : (z : ℂ) ∈ s := hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hz)
  have h := (lipschitzOnWith_iff_norm_sub_le.mp hlip) hy' hz'
  simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using h

end Work.Asymptotics

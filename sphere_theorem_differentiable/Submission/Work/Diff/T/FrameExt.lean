import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Extending the coordinate frame of a chart to a globally smooth vector field

For the chart at `x₀ : M`, the section `q ↦ (trivializationAt E (TangentSpace I) x₀).symmL ℝ q v`
("the tangent vector at `q` whose coordinates in the chart at `x₀` are `v`") is smooth on the
chart at `x₀`, but not globally.  This file shows that, near any point `p` of that chart, it
agrees with a *globally* smooth vector field.
-/

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField

namespace Work.Diff.T

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [T2Space M]

/-- Near a point `p` of the chart at `x₀`, the frame section
`q ↦ (trivializationAt E (TangentSpace I) x₀).symmL ℝ q v` agrees with a globally smooth vector
field. -/
theorem exists_global_eventuallyEq_symmL (x₀ : M) (v : E) {p : M}
    (hp : p ∈ (chartAt H x₀).source) :
    ∃ Z : Π x : M, TangentSpace I x, CMDiff ∞ (T% Z) ∧
      Z =ᶠ[𝓝 p] (fun q => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q v) := by
  have hmem : (chartAt H x₀).source ∈ 𝓝 p := (chartAt H x₀).open_source.mem_nhds hp
  obtain ⟨ψ, -, hψsupp⟩ :
      ∃ ψ : SmoothBumpFunction I p, True ∧ tsupport (ψ : M → ℝ) ⊆ (chartAt H x₀).source :=
    (SmoothBumpFunction.nhds_basis_tsupport p).mem_iff.mp hmem
  refine ⟨fun q => ψ q • (trivializationAt E (TangentSpace I) x₀).symmL ℝ q v, ?_, ?_⟩
  · refine ContMDiffOn.smul_section_of_tsupport (F := E) (V := TangentSpace I)
      (ψ.contMDiff.contMDiffOn) (chartAt H x₀).open_source hψsupp ?_
    rw [show (chartAt H x₀).source = (trivializationAt E (TangentSpace I) x₀).baseSet
      from (TangentBundle.trivializationAt_baseSet x₀).symm]
    refine (Trivialization.contMDiffOn_section_baseSet_iff (𝕜 := ℝ)
      (e := trivializationAt E (TangentSpace I) x₀)).mpr ?_
    refine (contMDiffOn_const (c := v)).congr (fun y hy => ?_)
    rw [Trivialization.symmL_apply (e := trivializationAt E (TangentSpace I) x₀) (R := ℝ) hy v]
    exact congrArg Prod.snd
      (Trivialization.apply_mk_symm (trivializationAt E (TangentSpace I) x₀) hy v)
  · filter_upwards [ψ.eventuallyEq_one] with q hq
    show ψ q • (trivializationAt E (TangentSpace I) x₀).symmL ℝ q v
      = (trivializationAt E (TangentSpace I) x₀).symmL ℝ q v
    rw [hq, Pi.one_apply, one_smul]

end Work.Diff.T

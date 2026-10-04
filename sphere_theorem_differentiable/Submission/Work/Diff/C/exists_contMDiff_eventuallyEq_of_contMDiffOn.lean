import Mathlib
import Submission.Work.Diff.C.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open scoped Manifold ContDiff Bundle Topology
open Set Filter

/-- **Local extension of a smooth function of a neighbourhood.**

If `F : M → ℝ` is `C^∞` on a neighbourhood `U` of `x`, then there is a globally `C^∞`
function `F'` which agrees with `F` on a neighbourhood of `x`.

The proof multiplies `F` by a smooth bump function `f` centred at `x` whose (topological)
support is contained in `interior U`: outside the support of `f` the product vanishes, while
on the support `F` is differentiable because `interior U` is an open neighbourhood of each
of its points.  Since `f = 1` eventually at `x`, the product agrees with `F` near `x`. -/
theorem exists_contMDiff_eventuallyEq_of_contMDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] {F : M → ℝ} {x : M} {U : Set M}
    (hU : U ∈ 𝓝 x) (hF : CMDiff[U] ∞ F) :
    ∃ F' : M → ℝ, CMDiff ∞ F' ∧ F' =ᶠ[𝓝 x] F := by
  have hxint : x ∈ interior U := mem_interior_iff_mem_nhds.mpr hU
  -- a smooth bump function supported in `interior U`
  obtain ⟨f, ⟨-, hf_sub⟩, -⟩ :=
    ((SmoothBumpFunction.nhds_basis_tsupport (I := I) x).restrict_subset
      (isOpen_interior.mem_nhds hxint)).mem_iff.mp Filter.univ_mem
  refine ⟨fun y => f y * F y, ?_, ?_⟩
  · -- the product is smooth everywhere
    refine contMDiff_of_tsupport fun y hy => ?_
    have hyf : y ∈ tsupport f := tsupport_smul_subset_left _ _ hy
    have hyU : y ∈ interior U := hf_sub hyf
    have : ContMDiffAt I 𝓘(ℝ, ℝ) ∞ F y :=
      (hF.mono interior_subset).contMDiffAt (isOpen_interior.mem_nhds hyU)
    exact ContMDiffAt.mul f.contMDiffAt this
  · -- near `x` the bump function is `1`
    filter_upwards [f.eventuallyEq_one] with y hy
    simp [hy]

end Work.Diff.C

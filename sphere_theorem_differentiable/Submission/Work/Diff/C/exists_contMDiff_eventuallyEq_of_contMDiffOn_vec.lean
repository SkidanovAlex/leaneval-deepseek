import Mathlib
import Submission.Work.Diff.C.exists_contMDiff_eventuallyEq_of_contMDiffOn

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.C

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField

/-- Vector-valued version of `Work.Diff.C.exists_contMDiff_eventuallyEq_of_contMDiffOn`: a map
`Φ : M → V` that is `C^∞` on a neighbourhood of `x` agrees near `x` with a globally `C^∞` map.
(Proof: multiply by a smooth bump function `f` centred at `x` with `tsupport f ⊆ interior U`; the
product `f • Φ` is globally smooth because on `tsupport f` the factor `Φ` is smooth, and `f = 1`
near `x`.) -/
theorem exists_contMDiff_eventuallyEq_of_contMDiffOn_vec
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {x : M} {U : Set M} (hU : U ∈ 𝓝 x) {Φ : M → V}
    (hΦ : ContMDiffOn I (𝓘(ℝ, V)) ∞ Φ U) :
    ∃ Φ' : M → V, ContMDiff I (𝓘(ℝ, V)) ∞ Φ' ∧ Φ' =ᶠ[𝓝 x] Φ := by
  have hxint : x ∈ interior U := mem_interior_iff_mem_nhds.mpr hU
  -- a smooth bump function supported in `interior U`
  obtain ⟨f, ⟨-, hf_sub⟩, -⟩ :=
    ((SmoothBumpFunction.nhds_basis_tsupport (I := I) x).restrict_subset
      (isOpen_interior.mem_nhds hxint)).mem_iff.mp Filter.univ_mem
  refine ⟨fun y => f y • Φ y, ?_, ?_⟩
  · -- the product is smooth everywhere
    refine contMDiff_of_tsupport fun y hy => ?_
    have hyf : y ∈ tsupport f := tsupport_smul_subset_left f Φ hy
    have hyU : y ∈ interior U := hf_sub hyf
    have : ContMDiffAt I (𝓘(ℝ, V)) ∞ Φ y :=
      (hΦ.mono interior_subset).contMDiffAt (isOpen_interior.mem_nhds hyU)
    exact ContMDiffAt.smul f.contMDiffAt this
  · -- near `x` the bump function is `1`
    filter_upwards [f.eventuallyEq_one] with y hy
    simp [hy]

end Work.Diff.C

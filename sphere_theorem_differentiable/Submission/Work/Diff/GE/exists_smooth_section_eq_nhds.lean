import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open Bundle Filter Function
open scoped Manifold ContDiff Bundle Topology

/-- A section of the tangent bundle which is `C^∞` on a neighbourhood of `x`
agrees, near `x`, with a globally `C^∞` section.

The proof cuts `X` off with a smooth bump function whose support is contained in
the open set where `X` is smooth; outside the (closed) topological support of the
bump the resulting section is the zero section, hence smooth, and on the bump's
topological support `X` is smooth and the pointwise product is smooth. -/
theorem exists_smooth_section_eq_nhds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    {x : M} (X : Π y : M, TangentSpace I y)
    (hX : ∀ᶠ y in nhds x, ContMDiffAt I I.tangent ((⊤ : ENat) : WithTop ENat)
        (fun z : M => Bundle.TotalSpace.mk' E z (X z)) y) :
    ∃ X' : Π y : M, TangentSpace I y,
      ContMDiff I I.tangent ((⊤ : ENat) : WithTop ENat)
        (fun z : M => Bundle.TotalSpace.mk' E z (X' z)) ∧
      X' x = X x ∧ X' =ᶠ[nhds x] X := by
  -- Pick an open neighbourhood `T` of `x` on which `X` is smooth.
  obtain ⟨T, hTsub, hTopen, hxT⟩ := mem_nhds_iff.mp hX
  -- Pick a smooth bump function supported (even topologically) inside `T`.
  obtain ⟨f, hfts, _⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (c := x) (hTopen.mem_nhds hxT)).mem_iff.mp
      (hTopen.mem_nhds hxT)
  refine ⟨fun y => f y • X y, ?_, ?_, ?_⟩
  · -- Global smoothness, checked pointwise.
    intro y
    by_cases hy : y ∈ tsupport (f : M → ℝ)
    · -- Inside the topological support the section `X` is smooth.
      exact (SmoothBumpFunction.contMDiffAt f).smul_section (hTsub (hfts hy))
    · -- Outside the topological support the bump vanishes on a neighbourhood,
      -- so the cut-off section agrees with the zero section there.
      have hmem : (tsupport (f : M → ℝ))ᶜ ∈ 𝓝 y :=
        (isClosed_tsupport _).isOpen_compl.mem_nhds hy
      have hev : (fun z => Bundle.TotalSpace.mk' E z (f z • X z)) =ᶠ[𝓝 y]
          Bundle.zeroSection E (TangentSpace I) := by
        filter_upwards [hmem] with z hz
        have hz0 : f z = 0 := by
          by_contra h
          exact hz (subset_tsupport _ (Function.mem_support.mpr h))
        simp only [hz0, zero_smul, Bundle.TotalSpace.mk']
        rfl
      exact (Bundle.contMDiffAt_zeroSection ℝ (TangentSpace I)).congr_of_eventuallyEq hev
  · -- The bump equals one at `x`.
    show f x • X x = X x
    rw [SmoothBumpFunction.eq_one f, one_smul]
  · -- The bump equals one near `x`.
    filter_upwards [SmoothBumpFunction.eventuallyEq_one f] with y hy
    rw [hy, Pi.one_apply, one_smul]

end Work.Diff.GE

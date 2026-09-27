import Mathlib

namespace Work.EKLRelCross

open scoped Pointwise

/-- For a compactly supported function `F` on a locally compact topological group,
every point `w₀` has a neighbourhood `U` such that for all `w ∈ U`, the set of `x`
with `F (w * x) ≠ 0` is contained in a fixed compact set `B`. -/
theorem exists_compact_nhds_comp_mul_support {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    (F : G → ENNReal) (hFs : HasCompactSupport F) (w₀ : G) :
    ∃ (B U : Set G), IsCompact B ∧ U ∈ nhds w₀ ∧ ∀ w ∈ U, ∀ x : G, F (w * x) ≠ 0 → x ∈ B := by
  -- a compact neighbourhood `C` of `w₀`
  obtain ⟨C, hC, hCnhds⟩ := exists_compact_mem_nhds w₀
  -- the compact set `B = C⁻¹ * tsupport F` and the neighbourhood `U = interior C`
  refine ⟨(fun g => g⁻¹) '' C * tsupport F, interior C, ?_, ?_, ?_⟩
  · -- `B` is compact: image of a compact set under inversion, times a compact set
    exact (hC.image continuous_inv).mul hFs
  · -- `interior C` is a neighbourhood of `w₀`
    exact isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hCnhds)
  · -- the containment property
    intro w hw x hx
    have hwC : w ∈ C := interior_subset hw
    have hxK : w * x ∈ tsupport F := subset_tsupport F (Function.mem_support.mpr hx)
    have hxeq : x = w⁻¹ * (w * x) := by group
    rw [hxeq]
    exact Set.mul_mem_mul ⟨w, hwC, rfl⟩ hxK

end Work.EKLRelCross

import Mathlib

namespace Work.Mostow

/-- A cyclic additive subgroup of `ℝ` is the set of the integral multiples of a single
real number. -/
theorem isAddCyclicEqZmultiples (S : AddSubgroup ℝ) (h : IsAddCyclic ↥S) :
    ∃ c : ℝ, (S : Set ℝ) = Set.range (fun m : ℤ => (m : ℝ) * c) := by
  obtain ⟨g, hg⟩ := isAddCyclic_iff_exists_zmultiples_eq_top.mp h
  refine ⟨(g : ℝ), ?_⟩
  ext x
  constructor
  · intro hx
    have hmem : (⟨x, hx⟩ : ↥S) ∈ AddSubgroup.zmultiples g :=
      hg ▸ AddSubgroup.mem_zmultiples g
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    refine ⟨m, ?_⟩
    have h2 := congrArg (fun y : ↥S => (y : ℝ)) hm
    simpa only [AddSubgroup.coe_zsmul, zsmul_eq_mul] using h2
  · rintro ⟨m, rfl⟩
    have h3 : (m : ℤ) • (g : ℝ) ∈ S := AddSubgroup.zsmul_mem S g.2 m
    rwa [zsmul_eq_mul] at h3

end Work.Mostow

import Mathlib

namespace Work.EKLC7

/-- The real line is the union of the symmetric intervals `(-n, n]` for natural `n`. -/
theorem sUnion_range_Ioc_rat_eq_univ :
    ⋃₀ (Set.range (fun n : ℕ => Set.Ioc (-(((n : ℚ)) : ℝ)) (((n : ℚ)) : ℝ))) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  refine Set.mem_sUnion.mpr ⟨Set.Ioc (-(((n : ℚ)) : ℝ)) (((n : ℚ)) : ℝ), ⟨n, rfl⟩, ?_⟩
  have hcast : (((n : ℚ)) : ℝ) = (n : ℝ) := by push_cast; ring
  rw [Set.mem_Ioc, hcast]
  constructor
  · linarith [neg_le_abs x, hn]
  · linarith [le_abs_self x, hn]

end Work.EKLC7

import Mathlib

namespace Work.Projection

/-- The range of the continuous linear map `(x, y) ↦ A y - B x` is the sum of the ranges of `A`
and `B`.  (Pure linear algebra over `𝕜`; here `A : Y →L[𝕜] Z`, `B : X →L[𝕜] Z`, and
`(x,y) ↦ A y - B x` is `A.comp (ContinuousLinearMap.snd 𝕜 X Y) - B.comp (ContinuousLinearMap.fst 𝕜 X Y)`
`.) -/
theorem range_sub_comp_eq_sup {𝕜 : Type*} [NontriviallyNormedField 𝕜] {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X] [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    [NormedAddCommGroup Z] [NormedSpace 𝕜 Z] (A : Y →L[𝕜] Z) (B : X →L[𝕜] Z) :
    (A.comp (ContinuousLinearMap.snd 𝕜 X Y) - B.comp (ContinuousLinearMap.fst 𝕜 X Y)).range
      = A.range ⊔ B.range := by
  apply le_antisymm
  · intro z hz
    rw [LinearMap.mem_range] at hz
    obtain ⟨p, rfl⟩ := hz
    rw [Submodule.mem_sup]
    refine ⟨A p.2, ⟨p.2, rfl⟩, -(B p.1), ?_, ?_⟩
    · exact ⟨-(p.1), by simp⟩
    · simp [sub_eq_add_neg]
  · rw [sup_le_iff]
    constructor
    · rintro z ⟨y, rfl⟩
      exact LinearMap.mem_range.mpr ⟨(0, y), by simp⟩
    · rintro z ⟨x, rfl⟩
      exact LinearMap.mem_range.mpr ⟨(-x, 0), by simp⟩

end Work.Projection

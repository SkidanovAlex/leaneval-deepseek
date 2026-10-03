import Mathlib

namespace Work.Rep

/-- Composition `a * x` vanishes if and only if `x` factors through the orthogonal
projection onto the kernel of `a`. -/
theorem mul_eq_zero_iff_exists_starProjection_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (a x : E →L[ℂ] E) : a * x = 0 ↔ ∃ y : E →L[ℂ] E, x = a.ker.starProjection * y := by
  constructor
  · intro h
    refine ⟨x, ?_⟩
    ext v
    rw [mul_apply_eq_comp]
    exact (Submodule.starProjection_eq_self_iff.mpr
      (LinearMap.mem_ker.mpr (by have := DFunLike.congr_fun h v; simpa using this))).symm
  · rintro ⟨y, rfl⟩
    ext v
    simp only [mul_apply_eq_comp, zero_apply]
    exact LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem a.ker (y v))

end Work.Rep

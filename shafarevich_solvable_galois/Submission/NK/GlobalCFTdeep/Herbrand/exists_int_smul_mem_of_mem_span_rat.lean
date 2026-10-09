import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.GlobalCFTdeep.Herbrand

/-- If `x` lies in the `ℚ`-span of an additive subgroup `M` of a `ℚ`-module `A`, then some nonzero integer multiple of `x` lies in `M`. -/
theorem exists_int_smul_mem_of_mem_span_rat {A : Type} [AddCommGroup A] [Module ℚ A]
    (M : AddSubgroup A) {x : A} (hx : x ∈ Submodule.span ℚ (M : Set A)) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ M := by
  -- `ℚ` is the localization of `ℤ` at its nonzero elements, so an element of the
  -- `ℚ`-span of `M` becomes an element of the `ℤ`-span after multiplying by a
  -- nonzero element of `ℤ`.
  obtain ⟨t, ht⟩ :=
    multiple_mem_span_of_mem_localization_span (nonZeroDivisors ℤ) ℚ (M : Set A) x hx
  refine ⟨(t : ℤ), ?_, ?_⟩
  · exact mem_nonZeroDivisors_iff_ne_zero.mp t.2
  · -- `M` is closed under integer multiples and addition, so its `ℤ`-span is `M`.
    have hle : Submodule.span ℤ (M : Set A) ≤ AddSubgroup.toIntSubmodule M := by
      rw [Submodule.span_le]; intro y hy; exact hy
    have h1 : (t : ℤ) • x ∈ Submodule.span ℤ (M : Set A) := by
      simpa [Submonoid.smul_def] using ht
    exact hle h1

end NK.GlobalCFTdeep.Herbrand

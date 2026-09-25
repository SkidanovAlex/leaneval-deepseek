import Mathlib
import Submission.Work.QuadraticFields.RankTwo

namespace Work.QuadraticFields

/-- The subgroup of squares of a commutative group is exactly the set of squares: the set of
squares is a subgroup (in a commutative group) containing every square. -/
theorem mem_squareSubgroup_iff {A : Type*} [CommGroup A] {a : A} :
    a ∈ squareSubgroup A ↔ ∃ b : A, b ^ 2 = a := by
  constructor
  · intro h
    induction h using Subgroup.closure_induction with
    | mem x hx => obtain ⟨b, rfl⟩ := hx; exact ⟨b, rfl⟩
    | one => exact ⟨1, by simp⟩
    | mul x y hx hy ihx ihy =>
        obtain ⟨b, rfl⟩ := ihx
        obtain ⟨c, rfl⟩ := ihy
        exact ⟨b * c, by rw [mul_pow]⟩
    | inv x hx ih =>
        obtain ⟨b, rfl⟩ := ih
        exact ⟨b⁻¹, by rw [inv_pow]⟩
  · rintro ⟨b, rfl⟩
    exact Subgroup.subset_closure ⟨b, rfl⟩

theorem sqClass_eq_zero_iff {A : Type*} [CommGroup A] {a : A} : sqClass a = 0 ↔ a ∈ squareSubgroup A := by
  rw [mem_squareSubgroup_iff]
  change ModN.mkQ 2 (Additive.ofMul a) = (0 : ModN (Additive A) 2) ↔ ∃ b : A, b ^ 2 = a
  rw [ModN.mkQ]
  change Submodule.Quotient.mk (Additive.ofMul a) = (0 : ModN (Additive A) 2) ↔ ∃ b : A, b ^ 2 = a
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨y, hy⟩
    rw [LinearMap.lsmul_apply] at hy
    refine ⟨y.toMul, ?_⟩
    have hy2 : y + y = Additive.ofMul a := by simpa [two_zsmul] using hy
    have h := congrArg Additive.toMul hy2
    simpa [toMul_add, pow_two] using h
  · rintro ⟨b, hb⟩
    refine ⟨Additive.ofMul b, ?_⟩
    rw [LinearMap.lsmul_apply]
    simpa [two_zsmul, ofMul_mul, pow_two] using congrArg Additive.ofMul hb

end Work.QuadraticFields

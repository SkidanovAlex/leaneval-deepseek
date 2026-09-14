import Mathlib.Algebra.Module.Submodule.Equiv

namespace Commons.LinearAlgebra.Module

theorem comap_linearEquiv_of_subset_range {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module ℤ A] [Module ℤ B] (f : A →ₗ[ℤ] B) (hf : Function.Injective f)
    (P : Submodule ℤ B) (hP : P ≤ LinearMap.range f) :
    Nonempty (P.comap f ≃ₗ[ℤ] P) := by
  let e : P.comap f →ₗ[ℤ] P :=
    { toFun := fun x => ⟨f x.1, Submodule.mem_comap.mp x.2⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp
      map_smul' := by
        intro r x
        apply Subtype.ext
        simp }
  refine ⟨LinearEquiv.ofBijective e ?_⟩
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hval : f x.1 = f y.1 := by
      change (e x : P).1 = (e y : P).1
      exact congrArg Subtype.val hxy
    exact hf hval
  · intro y
    obtain ⟨a, ha⟩ := (LinearMap.mem_range.mp (hP y.2))
    refine ⟨⟨a, ?_⟩, ?_⟩
    · exact Submodule.mem_comap.mpr (by rw [ha]; exact y.2)
    · apply Subtype.ext
      change f a = y.1
      exact ha

end Commons.LinearAlgebra.Module
import Mathlib

namespace Work.Drive.Whitney

/-- If a family is linearly independent and `f` is an injective linear map, the image family
`f ∘ v` is linearly independent.  Version of `LinearIndependent.map'` that only asks for
`AddCommMonoid` (not `AddCommGroup`) on the source, via the definition of `LinearIndependent`
as injectivity of `Finsupp.linearCombination` and `Finsupp.linearCombination_linear_comp`. -/
theorem linearIndependent_comp_of_injective {M N : Type*} [AddCommMonoid M] [Module ℝ M]
    [AddCommMonoid N] [Module ℝ N] {ι : Type*} {v : ι → M} (f : M →ₗ[ℝ] N)
    (hf : Function.Injective f) (hv : LinearIndependent ℝ v) :
    LinearIndependent ℝ (f ∘ v) := by
  rw [LinearIndependent] at *
  rw [Finsupp.linearCombination_linear_comp]
  exact hf.comp hv

theorem appendMapInjective {M N : Type*} [AddCommMonoid M] [Module ℝ M] [AddCommMonoid N] [Module ℝ N]
    {r k : ℕ} (T : M →ₗ[ℝ] N) (hT : Function.Injective T) (u : Fin r → M) (w : Fin k → M) :
    LinearIndependent ℝ (Fin.append (fun i => T (u i)) (fun j => T (w j))) ↔
      LinearIndependent ℝ (Fin.append u w) := by
  have hcomp : Fin.append (fun i => T (u i)) (fun j => T (w j)) = T ∘ Fin.append u w := by
    funext x
    revert x
    refine Fin.addCases ?_ ?_
    · intro i; simp [Fin.append]
    · intro j; simp [Fin.append]
  rw [hcomp]
  exact ⟨fun h => LinearIndependent.of_comp T h, fun h => linearIndependent_comp_of_injective T hT h⟩

end Work.Drive.Whitney

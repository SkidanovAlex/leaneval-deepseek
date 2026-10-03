import Mathlib.Topology.Homotopy.Equiv

namespace Commons.Topology.Homotopy

open ContinuousMap
open unitInterval

variable {X : Type*} [TopologicalSpace X]

/-- A deformation retraction of `X` onto the subspace `C ⊆ X` gives a homotopy
equivalence `X ≃ₕ C` (the inclusion is the homotopy inverse, via the
retraction `ρ`).  `I` is Mathlib's unit interval `Set.Icc (0 : ℝ) 1`. -/
theorem homotopyEquiv_of_deformationRetract (C : Set X)
    (ρ : X × I → X) (hρ : Continuous ρ)
    (h0 : ∀ x : X, ρ (x, (0 : I)) = x)
    (h1 : ∀ x : X, ρ (x, (1 : I)) ∈ C)
    (hfix : ∀ x : X, x ∈ C → ∀ t : I, ρ (x, t) = x) :
    Nonempty (X ≃ₕ C) := by
  let r : C(X, C) := ⟨fun x => ⟨ρ (x, (1 : I)), h1 x⟩,
    Continuous.subtype_mk (f := fun x : X => ρ (x, (1 : I))) (p := fun y : X => y ∈ C)
      (hρ.comp (by fun_prop)) h1⟩
  let i : C(C, X) := ⟨fun x : C => (x : X), continuous_subtype_val⟩
  refine ⟨{ toFun := r, invFun := i, left_inv := ?left, right_inv := ?right }⟩
  · -- the deformation `ρ` itself is a homotopy from the identity to `i ∘ r`
    refine ContinuousMap.Homotopic.symm ?_
    refine ⟨?_⟩
    refine { toContinuousMap := ⟨fun p : I × X => ρ (p.2, p.1), hρ.comp (by fun_prop)⟩,
             map_zero_left := ?m0, map_one_left := ?m1 }
    · intro x; simp [h0]
    · intro x; simp [r, i]
  · -- on `C` the retraction is the identity, by `hfix`
    have h_eq : r.comp i = ContinuousMap.id C := by
      ext x
      simp [r, i, hfix x.1 x.2 (1 : I)]
    simpa [h_eq] using
      (ContinuousMap.Homotopic.refl (ContinuousMap.id C) :
        (ContinuousMap.id C).Homotopic (ContinuousMap.id C))

end Commons.Topology.Homotopy
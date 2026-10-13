import Mathlib

namespace Work.DSG2

/-- Every point of a scheme lies in one of the irreducible components, and each irreducible
component is covered by the closure of its (nonempty) intersection with `P`. -/
theorem dense_of_meets_irreducibleComponents {X : AlgebraicGeometry.Scheme} (P : X.Opens)
    (h : ∀ C ∈ irreducibleComponents X, ((P : Set X) ∩ C).Nonempty) : Dense (P : Set X) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro x
  have hmem : x ∈ ⋃₀ irreducibleComponents X := by
    rw [sUnion_irreducibleComponents]
    exact Set.mem_univ x
  obtain ⟨C, hC, hxC⟩ := Set.mem_sUnion.mp hmem
  -- `C` is irreducible, `P` is a nonempty open subset of it, hence `C ⊆ closure (C ∩ P)`.
  have hne : (C ∩ (P : Set X)).Nonempty := by
    simpa only [Set.inter_comm] using h C hC
  have h1 : C ⊆ closure (C ∩ (P : Set X)) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen hC.1.isPreirreducible P.isOpen hne
  have h2 : closure (C ∩ (P : Set X)) ⊆ closure (P : Set X) :=
    closure_mono Set.inter_subset_right
  exact h2 (h1 hxC)

end Work.DSG2

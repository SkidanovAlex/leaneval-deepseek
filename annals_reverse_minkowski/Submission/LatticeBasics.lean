import ChallengeDeps
import Submission.Determinant

open ReverseMinkowski
open Module Real Matrix

set_option autoImplicit false

namespace Submission

namespace LatticeBasics

variable {n : ℕ}
local notation "ℝⁿ" => EuclideanSpace ℝ (Fin n)

/-- A submodule of a discrete submodule (both as subsets of the ambient normed space)
is discrete. -/
lemma discreteTopology_of_le {ℒ ℒ' : Submodule ℤ ℝⁿ} (hle : ℒ' ≤ ℒ) [DiscreteTopology ℒ] :
    DiscreteTopology ℒ' := by
  change DiscreteTopology (↥(ℒ' : Set ℝⁿ))
  rw [discreteTopology_subtype_iff']
  intro y hy
  have hdiscℒ : ∀ y ∈ (ℒ : Set ℝⁿ), ∃ U : Set ℝⁿ, IsOpen U ∧ U ∩ (ℒ : Set ℝⁿ) = {y} := by
    exact (discreteTopology_subtype_iff'.1 ‹DiscreteTopology ℒ›)
  rcases hdiscℒ y (hle hy) with ⟨U, hUo, hU⟩
  refine ⟨U, hUo, ?_⟩
  have hyU : y ∈ U := by
    have : y ∈ U ∩ (ℒ : Set ℝⁿ) := by
      rw [hU]
      exact Set.mem_singleton y
    exact this.1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨hxU, hx⟩
    have hxℒ : x ∈ (ℒ : Set ℝⁿ) := hle hx
    have hxy : x = y := by
      have : x ∈ U ∩ (ℒ : Set ℝⁿ) := ⟨hxU, hxℒ⟩
      rwa [hU] at this
    exact hxy
  · intro hx
    subst x
    exact ⟨hyU, hy⟩



/-- Under the hypothesis that every sublattice has determinant ≥ 1, every nonzero lattice
vector has norm ≥ 1 (equivalently λ₁(ℒ) ≥ 1). -/
lemma norm_ge_one_of_all_subdet {ℒ : Submodule ℤ ℝⁿ} [DiscreteTopology ℒ]
    (h : ∀ ℒ' (_hℒℒ' : ℒ' ≤ ℒ) [DiscreteTopology ℒ'], determinant ℒ' ≥ 1)
    (v : ℒ) (hv : v ≠ 0) : 1 ≤ ‖(v : ℝⁿ)‖ := by
  let S : Submodule ℤ ℝⁿ := Submodule.span ℤ ({(v : ℝⁿ)} : Set ℝⁿ)
  have hSle : S ≤ ℒ := by
    refine Submodule.span_le.mpr ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    simpa [hx] using v.2
  letI : DiscreteTopology S := discreteTopology_of_le (ℒ := ℒ) (ℒ' := S) hSle
  have hdet : determinant S ≥ 1 := h S hSle
  have hvS : (v : ℝⁿ) ∈ S := by
    exact Submodule.subset_span (by simp)
  have hv' : (v : ℝⁿ) ≠ 0 := by
    intro h
    apply hv
    exact Subtype.ext h
  have hdetv : determinant S = ‖(v : ℝⁿ)‖ := by
    exact Submission.Determinant.det_eq_norm_of_generator S hvS hv' rfl
  linarith

/-- determinant of the lattice itself is ≥ 1 -/
lemma det_ge_one_of_all_subdet {ℒ : Submodule ℤ ℝⁿ} [DiscreteTopology ℒ]
    (h : ∀ ℒ' (_hℒℒ' : ℒ' ≤ ℒ) [DiscreteTopology ℒ'], determinant ℒ' ≥ 1) :
    determinant ℒ ≥ 1 := by
  exact h ℒ le_rfl

end LatticeBasics
end Submission

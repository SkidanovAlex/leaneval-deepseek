import Mathlib.Tactic.Abel
import Submission.Commons.GroupTheory.finiteIndex_subgroup_contains_square_lattice

open scoped Pointwise

namespace Commons.PeriodicTiling

/-- A set `A` in an additive commutative group is a periodic tiling set if it is a
finite union of cosets of a finite-index subgroup.  This is the definition used by the
periodic tiling conjecture; it is stated here in the commons so that the lemma below
does not depend on the problem-specific `ChallengeDeps` module. -/
def IsPeriodicTilingSet {G : Type*} [AddCommGroup G] (A : Set G) : Prop :=
  ∃ H : AddSubgroup G, H.FiniteIndex ∧ ∃ s : Finset G, A = s + H

theorem periodicTilingSet_lattice_period
    {G₀ : Type*} [AddCommGroup G₀] [Finite G₀]
    {A : Set (ℤ × ℤ × G₀)} (hA : IsPeriodicTilingSet A) :
    ∃ n : ℕ, 0 < n ∧
      (∀ x : ℤ × ℤ × G₀, x ∈ A ↔ x + ((n : ℤ), 0, 0) ∈ A) ∧
      (∀ x : ℤ × ℤ × G₀, x ∈ A ↔ x + (0, (n : ℤ), 0) ∈ A) := by
  rcases hA with ⟨H, hHfin, s, hs⟩
  rcases Commons.GroupTheory.finiteIndex_subgroup_contains_square_lattice H hHfin with
    ⟨n, hnpos, hn1, hn2⟩
  refine ⟨n, hnpos, ?_, ?_⟩
  · intro x
    have ht : ((n : ℤ), 0, 0) ∈ H := hn1
    have htneg : -((n : ℤ), 0, 0) ∈ H := AddSubgroup.neg_mem H ht
    rw [hs]
    constructor
    · intro hx
      rw [Set.mem_add] at hx ⊢
      rcases hx with ⟨a, ha, h, hh, hx_eq⟩
      refine ⟨a, ha, h + ((n : ℤ), 0, 0), AddSubgroup.add_mem H hh ht, ?_⟩
      rw [← hx_eq]
      abel
    · intro hx
      rw [Set.mem_add] at hx ⊢
      rcases hx with ⟨a, ha, h, hh, hx_eq⟩
      refine ⟨a, ha, h + (-((n : ℤ), 0, 0)), AddSubgroup.add_mem H hh htneg, ?_⟩
      calc
        a + (h + (-((n : ℤ), 0, 0))) = (a + h) + (-((n : ℤ), 0, 0)) := by abel
        _ = (x + ((n : ℤ), 0, 0)) + (-((n : ℤ), 0, 0)) := by rw [hx_eq]
        _ = x := by abel
  · intro x
    have ht : (0, (n : ℤ), 0) ∈ H := hn2
    have htneg : -(0, (n : ℤ), 0) ∈ H := AddSubgroup.neg_mem H ht
    rw [hs]
    constructor
    · intro hx
      rw [Set.mem_add] at hx ⊢
      rcases hx with ⟨a, ha, h, hh, hx_eq⟩
      refine ⟨a, ha, h + (0, (n : ℤ), 0), AddSubgroup.add_mem H hh ht, ?_⟩
      rw [← hx_eq]
      abel
    · intro hx
      rw [Set.mem_add] at hx ⊢
      rcases hx with ⟨a, ha, h, hh, hx_eq⟩
      refine ⟨a, ha, h + (-(0, (n : ℤ), 0)), AddSubgroup.add_mem H hh htneg, ?_⟩
      calc
        a + (h + (-(0, (n : ℤ), 0))) = (a + h) + (-(0, (n : ℤ), 0)) := by abel
        _ = (x + (0, (n : ℤ), 0)) + (-(0, (n : ℤ), 0)) := by rw [hx_eq]
        _ = x := by abel

end Commons.PeriodicTiling
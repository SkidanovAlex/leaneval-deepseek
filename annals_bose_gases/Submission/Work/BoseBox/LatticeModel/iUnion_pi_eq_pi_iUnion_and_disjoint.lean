import Mathlib.Order.CompletePartialOrder
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.BooleanAlgebra
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBox.LatticeModel

theorem iUnion_pi_eq_pi_iUnion_and_disjoint {ι κ : Type*} (S : κ → ι → Set ℝ)
    (hdisj : ∀ i i' : κ, i ≠ i' → ∀ j : ι, Disjoint (S i j) (S i' j)) :
    (⋃ a : ι → κ, Set.pi Set.univ (fun j => S (a j) j))
        = Set.pi Set.univ (fun j => ⋃ i : κ, S i j) ∧
    (∀ a a' : ι → κ, a ≠ a' →
      Disjoint (Set.pi Set.univ (fun j => S (a j) j))
        (Set.pi Set.univ (fun j => S (a' j) j))) := by
  constructor
  · -- The union of the "choice" boxes equals the box of the pointwise unions.
    apply le_antisymm
    · -- ⊆ : a point of ∏_j S (a j) j lies in ∏_j ⋃_i S i j.
      intro x hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨a, ha⟩ := hx
      rw [Set.mem_univ_pi] at ha ⊢
      exact fun j => Set.mem_iUnion.mpr ⟨a j, ha j⟩
    · -- ⊇ : given x j ∈ ⋃_i S i j for every j, choose a j with x j ∈ S (a j) j.
      intro x hx
      rw [Set.mem_univ_pi] at hx
      choose a ha using fun j => Set.mem_iUnion.mp (hx j)
      exact Set.mem_iUnion.mpr ⟨a, by rw [Set.mem_univ_pi]; exact ha⟩
  · -- Distinct choices give disjoint boxes, splitting in a coordinate where they differ.
    intro a a' haa'
    obtain ⟨j0, hj0⟩ := Function.ne_iff.mp haa'
    rw [Set.disjoint_left]
    intro x hx hx'
    rw [Set.mem_univ_pi] at hx hx'
    exact (Set.disjoint_left.mp (hdisj (a j0) (a' j0) hj0 j0) (hx j0)) (hx' j0)

end Work.BoseBox.LatticeModel

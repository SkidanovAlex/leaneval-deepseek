import Mathlib
import Submission.Work.EKLComp.FlowerDefs

namespace Work.EKLComp

/-- A second-countable `T2` space admits a sequence of open sets that separates points, with the
zeroth member equal to the whole space.  Indeed, take a countable sequence `b` generating the
topology, put `W 0 = univ` and `W (k+1) = b k`; given `x ≠ y`, the complement of the closed
singleton `{y}` is an open neighbourhood of `x`, so some basis element `b k` contains `x` but not
`y`, and `x`, `y` differ on `W (k+1)`. -/
theorem exists_open_sep_seq (α : Type*) [TopologicalSpace α] [T2Space α]
    [SecondCountableTopology α] :
    ∃ W : ℕ → Set α, (∀ i, IsOpen (W i)) ∧ W 0 = Set.univ ∧
      ∀ x y : α, (∀ i, x ∈ W i ↔ y ∈ W i) → x = y := by
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis (α := α)
  let W : ℕ → Set α := fun n => Nat.rec Set.univ (fun k _ => b k) n
  refine ⟨W, ?_, ?_, ?_⟩
  · intro i
    cases i with
    | zero => exact isOpen_univ
    | succ k => exact hb.isOpen (Set.mem_range_self k)
  · rfl
  · intro x y hxy
    by_contra hne
    have hU : IsOpen ({y}ᶜ : Set α) := isClosed_singleton.isOpen_compl
    have hxU : x ∈ ({y}ᶜ : Set α) := Set.mem_compl_singleton_iff.mpr hne
    obtain ⟨v, hv, hxv, hvy⟩ := hb.exists_subset_of_mem_open hxU hU
    obtain ⟨k, rfl⟩ := hv
    have hxW : x ∈ W (k + 1) := hxv
    have hyW : y ∉ W (k + 1) := fun hy => (hvy hy) rfl
    exact hyW ((hxy (k + 1)).mp hxW)

theorem flower_basis_sep [T2Space Work.EKLContract.X3] [SecondCountableTopology Work.EKLContract.X3] :
    ∃ W : ℕ → Set Work.EKLContract.X3, (∀ i, IsOpen (W i)) ∧ W 0 = Set.univ ∧
      ∀ x y : Work.EKLContract.X3, (∀ i, x ∈ W i ↔ y ∈ W i) → x = y :=
  exists_open_sep_seq Work.EKLContract.X3

end Work.EKLComp

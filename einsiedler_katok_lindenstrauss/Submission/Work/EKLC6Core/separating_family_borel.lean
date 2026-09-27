import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.SL3Topology
import Submission.Work.EKLContract.Lemmas.Gamma3Facts

set_option linter.style.haveILetI false

namespace Work.EKLC6Core

open Work.EKLContract

/-- A countable family of measurable subsets of `X₃` contained in `B` which covers `B` and
separates its points: the basis of the quotient topology, intersected with `B`.

`X₃ = SL₃(ℝ)/Γ₃` is second countable (quotient of the second countable group `SL₃(ℝ)`) and `T₁`
(because `Γ₃` is closed), so a countable basis `b : ℕ → Set X₃` has the property that for
`x ≠ y` some basis element contains `x` and not `y`.  Intersecting with `B` gives the family. -/
theorem separating_family_borel {B : Set Work.EKLContract.X3}
    (hB : @MeasurableSet Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 B) :
    ∃ W : ℕ → Set Work.EKLContract.X3,
      (∀ n, @MeasurableSet Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 (W n)) ∧
      (∀ n, W n ⊆ B) ∧ (∀ x ∈ B, ∃ n, x ∈ W n) ∧
      (∀ x ∈ B, ∀ y ∈ B, x ≠ y → ∃ n, x ∈ W n ∧ y ∉ W n) := by
  haveI hSL2 : SecondCountableTopology SL3 := Work.EKLContract.Lemmas.SL3Topology.2
  haveI hΓcl : IsClosed (Γ3 : Set SL3) := Work.EKLContract.Lemmas.isClosed_Γ3
  haveI hX2 : SecondCountableTopology X3 := QuotientGroup.instSecondCountableTopology (N := Γ3)
  haveI hT1 : T1Space X3 := QuotientGroup.instT1Space
  obtain ⟨b, hb⟩ := TopologicalSpace.exists_seq_basis (α := X3)
  refine ⟨fun n => B ∩ b n, ?_, ?_, ?_, ?_⟩
  · intro n
    exact hB.inter ((hb.isOpen (Set.mem_range_self n)).measurableSet)
  · intro n
    exact Set.inter_subset_left
  · intro x hx
    obtain ⟨v, hv, hxv, -⟩ := hb.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    obtain ⟨n, hn⟩ := Set.mem_range.mp hv
    exact ⟨n, hx, hn.symm ▸ hxv⟩
  · intro x hxB y _ hxy
    have hopen : IsOpen ({y}ᶜ : Set X3) := isClosed_singleton.isOpen_compl
    have hxmem : x ∈ ({y}ᶜ : Set X3) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact hxy
    obtain ⟨v, hv, hxv, hvsub⟩ := hb.exists_subset_of_mem_open hxmem hopen
    obtain ⟨n, hn⟩ := Set.mem_range.mp hv
    exact ⟨n, ⟨hxB, hn.symm ▸ hxv⟩, fun hy => hvsub (hn ▸ hy.2) rfl⟩

end Work.EKLC6Core

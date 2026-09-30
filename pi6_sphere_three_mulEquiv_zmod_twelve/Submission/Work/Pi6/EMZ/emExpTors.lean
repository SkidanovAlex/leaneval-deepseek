import Mathlib
import Submission.Work.Pi6.EMZ.Defs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EMZ

theorem emExpTors (hXe : Work.Pi6.EMExp) :
    (∀ (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ), 10 ≤ N →
      Work.Serre.IsEMSpaceUpTo (ZMod 2) 3 (by norm_num) N X x₀ →
      ∃ a : Work.Pi6.HR ℤ X 5, a ∈ Work.Pi6.EMZ.torsP 2 (Work.Pi6.HR ℤ X 5) ∧
        a ∉ Work.Pi6.EMZ.pH 2 (Work.Pi6.HR ℤ X 5)) ∧
    (∀ (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ), 12 ≤ N →
      Work.Serre.IsEMSpaceUpTo (ZMod 2) 4 (by norm_num) N X x₀ →
      ∃ a : Work.Pi6.HR ℤ X 7, a ∈ Work.Pi6.EMZ.torsP 2 (Work.Pi6.HR ℤ X 7) ∧
        a ∉ Work.Pi6.EMZ.pH 2 (Work.Pi6.HR ℤ X 7)) := by
  constructor
  · intro X _ x₀ N hN hE
    obtain ⟨a, ha2, hnd⟩ := hXe.1 X x₀ N hN hE
    exact ⟨a, mem_torsP.mpr ha2, fun hmem => by
      obtain ⟨b, hb⟩ := mem_pH.mp hmem
      exact hnd b hb⟩
  · intro X _ x₀ N hN hE
    obtain ⟨a, ha2, hnd⟩ := hXe.2 X x₀ N hN hE
    exact ⟨a, mem_torsP.mpr ha2, fun hmem => by
      obtain ⟨b, hb⟩ := mem_pH.mp hmem
      exact hnd b hb⟩

end Work.Pi6.EMZ

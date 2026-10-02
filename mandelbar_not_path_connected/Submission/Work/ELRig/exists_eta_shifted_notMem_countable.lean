import Mathlib
import Submission.Work.ELRig.exists_Ioo_notMem_of_countable

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

/-- Given a countable set `W ⊆ ℝ` and a real `y`, there is `η ∈ (0,1)` such that neither
`y + η` nor `-(y + η)` lies in `W`. Indeed the "bad" set of `η` is the union of the two
preimages `(· + y) ⁻¹' W` and `(· ↦ -(y + ·)) ⁻¹' W` of the countable set `W` under injective
maps, hence countable, while `(0,1)` is uncountable. -/
theorem exists_eta_shifted_notMem_countable (W : Set ℝ) (hW : W.Countable) (y : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ y + η ∉ W ∧ -(y + η) ∉ W := by
  have hS1 : ({η : ℝ | y + η ∈ W}).Countable :=
    hW.preimage (f := fun η : ℝ => y + η) (by intro a b h; linarith)
  have hS2 : ({η : ℝ | -(y + η) ∈ W}).Countable :=
    hW.preimage (f := fun η : ℝ => -(y + η)) (by intro a b h; linarith)
  have hSc : ({η : ℝ | y + η ∈ W} ∪ {η : ℝ | -(y + η) ∈ W}).Countable := hS1.union hS2
  obtain ⟨η, hη1, hη2⟩ :=
    exists_Ioo_notMem_of_countable (show (0 : ℝ) < 1 by norm_num) hSc
  rw [Set.mem_Ioo] at hη1
  exact ⟨η, hη1.1, hη1.2, fun h => hη2 (Or.inl h), fun h => hη2 (Or.inr h)⟩

end Work.ELRig

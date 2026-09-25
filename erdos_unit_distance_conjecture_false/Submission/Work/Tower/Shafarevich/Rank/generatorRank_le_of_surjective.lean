import Mathlib
import Submission.Work.Tower.Defs

namespace Work.Tower.Shafarevich.Rank

theorem generatorRank_le_of_surjective {G H : Type} [Group G] [Group H] [Finite G] (f : G →* H)
    (hf : Function.Surjective f) : Work.Tower.generatorRank H ≤ Work.Tower.generatorRank G := by
  classical
  -- Since `G` is finite, the set of `d` for which `G` is a quotient of `FreeGroup (Fin d)`
  -- is nonempty: enumerate `G` by `Fin (Nat.card G)` and lift to the free group.
  have hne : {d : ℕ | ∃ φ : FreeGroup (Fin d) →* G, Function.Surjective φ}.Nonempty := by
    refine ⟨Nat.card G, FreeGroup.lift (Finite.equivFin G).symm, ?_⟩
    intro g
    exact ⟨FreeGroup.of (Finite.equivFin G g), by simp⟩
  -- Hence the infimum is attained: `G` is a quotient of the free group on
  -- `generatorRank G` generators.
  obtain ⟨φ, hφ⟩ := Nat.sInf_mem hne
  -- Composing with the surjection `f` shows `H` is also a quotient of that same free
  -- group, so `generatorRank G` belongs to the defining set of `generatorRank H`.
  exact Nat.sInf_le ⟨f.comp φ, hf.comp hφ⟩

end Work.Tower.Shafarevich.Rank

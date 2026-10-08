import Mathlib
import Submission.Work.Hering.GL32.AppIXDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.HardCore

theorem exists_simple_stable_subgroup {Q : Type} [CommGroup Q] [Finite Q]
    (ρ : Work.Hering.GL32 →* MulAut Q) (hnt : ∃ q : Q, q ≠ 1) :
    ∃ S : Subgroup Q, S ≠ ⊥ ∧ (∀ k : Work.Hering.GL32, ∀ x ∈ S, (ρ k) x ∈ S) ∧
      ∀ T : Subgroup Q, T ≤ S → T ≠ ⊥ →
        (∀ k : Work.Hering.GL32, ∀ x ∈ T, (ρ k) x ∈ T) → T = S := by
  -- `Q` is finite, so there are only finitely many subgroups; the family of
  -- nonzero `ρ`-stable subgroups is nonempty (`⊤` qualifies, as `Q` is nontrivial),
  -- hence has a minimal element under inclusion. This is a minimal (irreducible)
  -- nonzero `ρ`-stable subgroup.
  classical
  let P : Set (Subgroup Q) :=
    {S | S ≠ ⊥ ∧ ∀ k : Work.Hering.GL32, ∀ x ∈ S, (ρ k) x ∈ S}
  have hPne : P.Nonempty := by
    refine ⟨⊤, ?_⟩
    constructor
    · -- `⊤ ≠ ⊥`, because `Q` has a nontrivial element
      intro h
      obtain ⟨q, hq⟩ := hnt
      have hq' : q ∈ (⊤ : Subgroup Q) := trivial
      rw [h] at hq'
      exact hq (by simpa using hq')
    · -- `⊤` is stable under `ρ`
      intro k x hx; trivial
  have hPfin : P.Finite :=
    Set.Finite.subset (Set.finite_univ_iff.mpr (inferInstance : Finite (Subgroup Q)))
      (Set.subset_univ P)
  obtain ⟨S, hSmin⟩ := hPfin.exists_minimal hPne
  refine ⟨S, hSmin.1.1, hSmin.1.2, ?_⟩
  intro T hTS hTne hTstab
  -- `T ∈ P`, so minimality of `S` forces `S ≤ T`; with `T ≤ S` this gives `T = S`.
  exact le_antisymm hTS (hSmin.2 ⟨hTne, hTstab⟩ hTS)

end Work.Hering.HardCore

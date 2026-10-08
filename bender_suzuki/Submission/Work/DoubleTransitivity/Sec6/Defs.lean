import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.DoubleTransitivity.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec6.Defs` — `O_{p'}` of a subgroup, transported to the ambient group

Peterfalvi I §6 uses `O_{p'}(D)` and `O_{p'}(D ∩ D^u)` for subgroups `D ≤ G` of odd order.
`Submission.Blueprint.pPrimeCore p K` is the group-theoretic `O_{p'}(K)` for a group `K`; for a
subgroup `X ≤ G` the ambient-group version is the image of `O_{p'}(↥X)` under the inclusion.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.DoubleTransitivity

/-- `O_{p'}(X)` for a subgroup `X ≤ G`, viewed as a subgroup of `G` (the image of
`Submission.Blueprint.pPrimeCore p ↥X` under the inclusion `X.subtype`). -/
noncomputable def pPrimeCoreSub {G : Type} [Group G] (p : ℕ) (X : Subgroup G) : Subgroup G :=
  (Submission.Blueprint.pPrimeCore p ↥X).map X.subtype

theorem pPrimeCoreSub_le {G : Type} [Group G] (p : ℕ) (X : Subgroup G) :
    pPrimeCoreSub p X ≤ X := Subgroup.map_subtype_le _

theorem mem_pPrimeCoreSub {G : Type} [Group G] {p : ℕ} {X : Subgroup G} {x : G} :
    x ∈ pPrimeCoreSub p X ↔ ∃ hx : x ∈ X, (⟨x, hx⟩ : ↥X) ∈
      Submission.Blueprint.pPrimeCore p ↥X := by
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h
    rw [← hyx]
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hx'⟩
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, hx', rfl⟩

end Work.DoubleTransitivity

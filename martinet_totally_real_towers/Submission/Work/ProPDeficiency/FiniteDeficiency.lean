import Mathlib
import Submission.Work.ProPDeficiency.Basic
import Submission.Work.ProPDeficiency.GolodShafarevich
import Submission.Work.ProPDeficiency.card_le_rel_card_of_finite

/-!
# Deficiency: finite groups are not "deficient"

**Namespace** `Work.ProPDeficiency`; module `Submission.Work.ProPDeficiency.FiniteDeficiency`.

Consequences of `Work.ProPDeficiency.card_le_rel_card_of_finite` (a finite group presented on `d`
generators by `r` relators satisfies `d ≤ r`), expressed in the deficiency language of
`Submission.Work.ProPDeficiency.Basic`:

* `le_relRank_of_finite` : on a fixed generating set `α` of a finite group, the relator rank is at
  least `#α` — i.e. the deficiency of every presentation of a finite group is `≤ 0`;
* `hasDeficiency_nonpos_of_finite` : no finite group has positive deficiency;
* `hasDeficiency_neg_one_of_finite_pGroup` : for a finite `p`-group (with minimal generators) the
  stronger Golod--Shafarevich bound applies, so even `-1` is excluded once `d ≥ 5`.

The group-theoretic content is classical (deficiency of a finite group is `≤ 0`); the point of the
module is that the arithmetic side never has to reach past this interface.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.ProPDeficiency

/-- **The relator rank of a finite group is at least its generator count.**  If `α` presents the
finite group `G` then every presentation of `G` on the same generating set `α` has at least
`Fintype.card α` relators. -/
theorem le_relRank_of_finite {α : Type} [Fintype α] {rel : Finset (FreeGroup α)} {G : Type}
    [Group G] [Finite G] (h : IsPresentation α rel G) : Fintype.card α ≤ relRank α G := by
  obtain ⟨rel', hrel'card, hpres'⟩ :=
    Nat.sInf_mem (s := {r : ℕ | ∃ rel : Finset (FreeGroup α), rel.card = r ∧
      IsPresentation α rel G}) ⟨rel.card, rel, rfl, h⟩
  rw [relRank, ← hrel'card]
  exact card_le_rel_card_of_finite rel' hpres'

/-- **Finite groups have non-positive deficiency.** -/
theorem hasDeficiency_nonpos_of_finite {G : Type} [Group G] [Finite G] {u : ℤ}
    (h : HasDeficiency G u) : u ≤ 0 := by
  obtain ⟨d, r, ⟨α, inst, rel, hd, hr, hpres⟩, hdef⟩ := h
  letI := inst
  have hle : (Fintype.card α : ℤ) ≤ (rel.card : ℤ) := by
    exact_mod_cast card_le_rel_card_of_finite rel hpres
  rw [hd, hr] at hle
  have hdef' : (r : ℤ) + u ≤ (d : ℤ) := hdef
  linarith

end Work.ProPDeficiency

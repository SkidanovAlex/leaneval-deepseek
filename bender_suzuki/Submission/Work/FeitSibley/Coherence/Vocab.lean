import Mathlib
import Submission.Work.Coherence.All
import Submission.Work.CharCore.Main
import Submission.Work.FeitSibley.Defs
import Submission.Work.FeitSibley.Basic
import Submission.Work.FeitSibley.GroupTheory.S_Q1
import Submission.Work.Induction.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.Vocab`

The vocabulary of the two-block argument of Peterfalvi II, Appendice XII, extracted from
`Coherence/coherent_scriptS.lean` so that modules which need only the notation (and not the
linear-shift engine) can import it without a cycle.

* `FSScomm h = ⁅h.S,h.S⁆` (Peterfalvi's `S'`),
* `FSQcomm h = ⁅h.Q,h.Q⁆` (Peterfalvi's `Q'`),
* `FSZ h = ⁅h.Q1,h.Q1⁆ ⊓ Z(h.Q1)` (Peterfalvi's `Z`),
* the elementary API of `𝒮(R) = scriptSR h.H h.Q1 R`,
* `isVChar_indLin_scriptS`: `Ind_H^G` sends `𝒮` to virtual characters.
-/

set_option linter.unusedSectionVars false

namespace Work.FeitSibley.Coherence

open Classical

noncomputable section

variable {H G : Type*} [Group H] [Fintype H] [Group G] [Fintype G]

/-- Peterfalvi's `S' = [S,S]` (`S` is the first direct factor of `Q`). -/
abbrev FSScomm {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G) : Subgroup G :=
  ⁅h.S, h.S⁆

/-- Peterfalvi's `Q' = [Q,Q]`. -/
abbrev FSQcomm {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G) : Subgroup G :=
  ⁅h.Q, h.Q⁆

/-- Peterfalvi's `Z = [Q₁,Q₁] ∩ Z(Q₁)` (the centre of `Q₁`, viewed in `G` as the centralizer of
`Q₁`). -/
abbrev FSZ {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G) : Subgroup G :=
  ⁅h.Q1, h.Q1⁆ ⊓ Subgroup.centralizer (h.Q1 : Set G)

/-- `𝒮(R) = scriptSR H Q₁ R` is a subset of `𝒮`. -/
theorem scriptSR_subset_scriptS {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (R : Subgroup G) :
    Work.FeitSibley.scriptSR h.H h.Q1 R ⊆ Work.FeitSibley.scriptS h.H h.Q1 :=
  Finset.filter_subset _ _

/-- Membership in `𝒮(R)`. -/
theorem mem_scriptSR_iff {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    (R : Subgroup G) {χ : ↥h.H → ℂ} :
    χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 R ↔
      χ ∈ Work.FeitSibley.scriptS h.H h.Q1 ∧ ∀ x : ↥h.H, (x : G) ∈ R → χ x = χ 1 := by
  simp [Work.FeitSibley.scriptSR]

/-- `𝒮(R)` is antitone in `R`, and in particular `𝒮(Q') ⊆ 𝒮`. -/
theorem scriptSR_subset_of_le {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {R R' : Subgroup G} (hRR' : R ≤ R') :
    Work.FeitSibley.scriptSR h.H h.Q1 R' ⊆ Work.FeitSibley.scriptSR h.H h.Q1 R := by
  intro χ hχ
  rw [mem_scriptSR_iff] at hχ ⊢
  exact ⟨hχ.1, fun x hx => hχ.2 x (hRR' hx)⟩

/-- `𝒮(⊥) = 𝒮`. -/
theorem scriptSR_bot {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G) :
    Work.FeitSibley.scriptSR h.H h.Q1 ⊥ = Work.FeitSibley.scriptS h.H h.Q1 := by
  refine (Finset.Subset.antisymm (scriptSR_subset_scriptS h ⊥) ?_)
  intro χ hχ
  rw [mem_scriptSR_iff]
  refine ⟨hχ, fun x hx => ?_⟩
  have hx1 : x = 1 := Subtype.ext (Subgroup.mem_bot.mp hx)
  rw [hx1]

/-- `Ind_H^G` of a member of `𝒮` is a virtual character of `G`. -/
theorem isVChar_indLin_scriptS {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {χ : ↥h.H → ℂ} (hχ : χ ∈ Work.FeitSibley.scriptS h.H h.Q1) :
    Work.Coherence.IsVChar (Work.FeitSibley.indLin h.H χ) := by
  have hIrr : χ ∈ Work.CharCore.Irr ↥h.H := (Finset.mem_filter.mp hχ).1
  have hV : Work.CharCore.IsVChar χ :=
    AddSubgroup.subset_closure (Finset.mem_coe.mpr hIrr)
  have h2 : Work.CharCore.IsVChar (Work.Induction.indFun h.H χ) :=
    Work.Induction.isVChar_indFun hV
  rw [Work.FeitSibley.indLin_apply]
  exact (Work.CharCore.IsVChar_iff_coherence _).mp h2

end

end Work.FeitSibley.Coherence

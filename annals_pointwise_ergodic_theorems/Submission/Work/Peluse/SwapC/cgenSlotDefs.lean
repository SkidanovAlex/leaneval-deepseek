import Mathlib
import Submission.Work.Peluse.SwapC.concatState

/-!
# Slot vocabulary for `Work.Peluse.SwapC.cgenSlotsEndpoints`

The concatenated slots appearing in `Work.Peluse.SwapC.genuineDiffs` are indexed by a pair of
strings `(a, b)` and a coordinate `j : Fin s`: the pair contributes the slot `CC.dff j a b` exactly
when `a` and `b` agree strictly below the pivot `s - 1 - j`, `a` carries `true` at the pivot and `b`
carries `false` there.  That condition is `slotCond j a b` below (a copy of the conjunction
occurring in the body of `genuineDiffs`, so that it can be named and reasoned about); `pairSlots a b`
is the list of slots contributed by the pair, and `slotOfF a b` is its `Option`-valued form.

The main consumers are `Work.Peluse.SwapC.cgenSlotsEndpoints` and the lemmas
`Work.Peluse.SwapC.slotCond_iff_mem_slotSet` / `Work.Peluse.SwapC.ofFn_equivFin_perm`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapC

open CC
open Classical

noncomputable section

/-- The pointwise condition under which the pair of strings `(a, b)` contributes the slot `j` in
`genuineDiffs`: `a` and `b` agree strictly below the pivot `s - 1 - j`, `a` carries `true` at the
pivot and `b` carries `false` there. -/
def slotCond {s : ℕ} (j : Fin s) (a b : Fin s → Bool) : Prop :=
  (∀ i : Fin s, i.val < s - 1 - j.val → a i = b i) ∧
    a ⟨s - 1 - j.val, by omega⟩ = true ∧ b ⟨s - 1 - j.val, by omega⟩ = false

/-- The pivot of the slot `j` is determined by the condition: at most one `j` can be compatible
with a given pair of strings. -/
lemma slotCond_unique {s : ℕ} {j j' : Fin s} {a b : Fin s → Bool}
    (h : slotCond j a b) (h' : slotCond j' a b) : j = j' := by
  have hp : s - 1 - j.val < s := by omega
  have hp' : s - 1 - j'.val < s := by omega
  have hkey : s - 1 - j.val = s - 1 - j'.val := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : a ⟨s - 1 - j.val, hp⟩ = b ⟨s - 1 - j.val, hp⟩ :=
        h'.1 ⟨s - 1 - j.val, hp⟩ (by omega)
      have h2 : a ⟨s - 1 - j.val, hp⟩ = true := h.2.1
      have h3 : b ⟨s - 1 - j.val, hp⟩ = false := h.2.2
      rw [h2, h3] at h1
      exact Bool.noConfusion h1
    · have h1 : a ⟨s - 1 - j'.val, hp'⟩ = b ⟨s - 1 - j'.val, hp'⟩ :=
        h.1 ⟨s - 1 - j'.val, hp'⟩ (by omega)
      have h2 : a ⟨s - 1 - j'.val, hp'⟩ = true := h'.2.1
      have h3 : b ⟨s - 1 - j'.val, hp'⟩ = false := h'.2.2
      rw [h2, h3] at h1
      exact Bool.noConfusion h1
  refine Fin.ext ?_
  omega

/-- The list of slots contributed by a pair of strings. -/
def pairSlots {s : ℕ} (a b : Fin s → Bool) : List (CC s) :=
  (List.finRange s).filterMap fun j : Fin s =>
    if slotCond j a b then some (CC.dff j a b) else none

/-- The (optional) slot attached to a pair of strings `(a, b)`. -/
def slotOfF {s : ℕ} (a b : Fin s → Bool) : Option (CC s) :=
  if h : ∃ j : Fin s, slotCond j a b then some (CC.dff (Classical.choose h) a b) else none

lemma slotOfF_eq_some_iff {s : ℕ} (a b : Fin s → Bool) (c : CC s) :
    slotOfF a b = some c ↔ ∃ j : Fin s, slotCond j a b ∧ c = CC.dff j a b := by
  unfold slotOfF
  by_cases h : ∃ j : Fin s, slotCond j a b
  · rw [dif_pos h]
    constructor
    · intro hc
      exact ⟨Classical.choose h, Classical.choose_spec h, (Option.some.inj hc).symm⟩
    · rintro ⟨j, hj, hc⟩
      rw [hc, slotCond_unique hj (Classical.choose_spec h)]
  · rw [dif_neg h]
    constructor
    · intro hc
      exact absurd hc (by simp)
    · rintro ⟨j, hj, -⟩
      exact absurd ⟨j, hj⟩ h

lemma slotOfF_eq_none_iff {s : ℕ} (a b : Fin s → Bool) :
    slotOfF a b = none ↔ ∀ j : Fin s, ¬ slotCond j a b := by
  unfold slotOfF
  by_cases h : ∃ j : Fin s, slotCond j a b
  · rw [dif_pos h]
    simp only [reduceCtorEq, false_iff]
    intro hh
    exact hh (Classical.choose h) (Classical.choose_spec h)
  · rw [dif_neg h]
    simpa using h

end

end Work.Peluse.SwapC

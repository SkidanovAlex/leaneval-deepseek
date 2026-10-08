import Mathlib
import Submission.Work.Tame.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

/-- Feit–Thompson Definition 9.1: `𝔇 = L̂^# - 𝔏₀` is empty exactly when the centralizer in `X` of
every non-identity element of `L̂` is contained in `𝔏 = N(L̂)`. -/
theorem Dset_eq_empty_iff {X : Type*} [Group X] {Lhat : Set X} :
    Dset Lhat = ∅ ↔ ∀ l : X, l ∈ Lhat → l ≠ 1 →
      Subgroup.centralizer ({l} : Set X) ≤ Lgrp Lhat := by
  rw [Set.eq_empty_iff_forall_notMem]
  constructor
  · intro h l hl hl1
    by_contra hc
    exact h l ⟨hl, hl1, hc⟩
  · intro h l hl
    exact hl.2.2 (h l hl.1 hl.2.1)

end Work.Tame

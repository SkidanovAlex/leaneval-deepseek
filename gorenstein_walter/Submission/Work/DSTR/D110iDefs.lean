import Mathlib

/-!
# `DS9a`: the statement of Bender 1.10(i) for a fixed group

This small module contains the definition `Work.DSTR.CentInvariant`, the conclusion of Bender
1981, 1.10(i) for a single group.  It is separated from
`Submission/Work/DSTR/d110iModel.lean` so that the model cases (`L₂(q)`, `PGL₂(q)`, `A₇`) can be
stated and proved in modules that import only this file.
-/

namespace Work.DSTR

open Subgroup

/-- **Bender 1.10(i) for a fixed group.**  Every odd `p`-subgroup `P` normalised by the
centralizer of an involution `t` is centralized by `t`. -/
def CentInvariant (Q : Type*) [Group Q] : Prop :=
  ∀ (t : Q), orderOf t = 2 → ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ P : Subgroup Q, IsPGroup p P →
    Subgroup.centralizer ({t} : Set Q) ≤ Subgroup.normalizer (P : Set Q) →
    P ≤ Subgroup.centralizer ({t} : Set Q)

end Work.DSTR

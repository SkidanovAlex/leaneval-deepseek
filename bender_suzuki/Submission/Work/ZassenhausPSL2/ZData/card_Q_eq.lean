import Submission.Work.ZassenhausPSL2.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-! `|Q| = |D| + 1` from `|𝒮| = 1` and `|𝒮| · |D| = |Q| - 1` (design Z1′). -/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausPSL2.ZData

/-- **Z1′.** `|Q| = |D| + 1`, from F2b (`|𝒮| · |D| = |Q| - 1`) and F8 (`|𝒮| = 1`). -/
theorem card_Q_eq {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G}
    (h1 : (excludingKernel H Q).card = 1)
    (h2 : (excludingKernel H Q).card * Nat.card (twoPoint H t) = Nat.card Q - 1) :
    Nat.card Q = Nat.card (twoPoint H t) + 1 := by
  have hpos : 1 ≤ Nat.card Q := Nat.card_pos
  rw [h1, one_mul] at h2
  omega

end Work.ZassenhausPSL2.ZData

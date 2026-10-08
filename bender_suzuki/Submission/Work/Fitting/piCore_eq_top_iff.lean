import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.piCore_isPiNat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `O_π(G) = ⊤ ↔ |G|` is a `π`-number

`O_π(G) = Work.Fitting.piCore π G` is the supremum of the normal `π`-subgroups of `G`
(`Submission.Work.Fitting.Defs`).  For a finite group we show

  `O_π(G) = ⊤ ↔ IsPiNat π (Nat.card G)`.

* If `O_π(G) = ⊤` then `⊤ = O_π(G)` is a `π`-group, by `Work.Fitting.piCore_isPiNat`
  (the `π`-core of a finite group is itself a `π`-group).  Transporting along the
  isomorphism `↥(⊤ : Subgroup G) ≃* G` gives `IsPiNat π (Nat.card G)`.
* Conversely if `|G|` is a `π`-number then the whole group `⊤` is a normal `π`-subgroup,
  so `⊤ ≤ O_π(G)`, whence `O_π(G) = ⊤`.
-/

noncomputable section

open Classical

namespace Work.Fitting

theorem piCore_eq_top_iff (π : ℕ → Prop) (G : Type*) [Group G] [Finite G] :
    Work.Fitting.piCore π G = ⊤ ↔ Work.Fitting.IsPiNat π (Nat.card G) := by
  have htop : Nat.card ↥(⊤ : Subgroup G) = Nat.card G :=
    Nat.card_congr Subgroup.topEquiv.toEquiv
  constructor
  · intro h
    rw [← htop, ← h]
    exact piCore_isPiNat G π
  · intro h
    refine le_antisymm le_top ?_
    exact le_piCore (N := ⊤) Subgroup.normal_top (by rw [htop]; exact h)

end Work.Fitting

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Crossing a Galois realization over `ℚ` with a cyclic group

If `G` is realizable over `ℚ` and `n ≠ 0`, then so is `G × Multiplicative (ZMod n)`: take a
realization `L/ℚ` of `G` inside `AlgebraicClosure ℚ`, a cyclic degree-`n` extension `M/ℚ` with
`L ⊓ M = ⊥` (`exists_disjoint_cyclic`), and use that the Galois group of the compositum of
linearly disjoint Galois extensions is the product
(`Submission.realizableOver_prod_of_inf_eq_bot_closure`).

## Main declarations

* `realizableOver_prod_zmod`

-/
import Mathlib
import Submission.Combine
import Submission.Work.FieldTheory.Crossing.Defs
import Submission.Work.FieldTheory.Crossing.ExistsDisjoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.FieldTheory.Crossing

open scoped Classical

noncomputable section

set_option linter.style.haveILetI false

/-- **Crossing with a cyclic group of order `n`.**  If `G` is realizable over `ℚ`, so is
`G × Multiplicative (ZMod n)`, for every `n ≠ 0`. -/
theorem realizableOver_prod_zmod (G : Type) [Group G] (n : ℕ) (hn : n ≠ 0) :
    Submission.RealizableOver ℚ G → Submission.RealizableOver ℚ (G × Multiplicative (ZMod n)) := by
  intro h
  obtain ⟨L, hLfd, hLG, ⟨e⟩⟩ := Submission.RealizableOver.toClosure h
  obtain ⟨M, hMfd, hMG, hdisj, ⟨psi⟩⟩ := exists_disjoint_cyclic L hLfd hLG n hn
  have hprod := Submission.realizableOver_prod_of_inf_eq_bot_closure L M hLfd hLG hMfd hMG hdisj
  exact hprod.of_mulEquiv (MulEquiv.prodCongr e psi).symm

end

end Work.FieldTheory.Crossing

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The lower central series is contained in the descending `p`-central series

For a group `P` the descending central series `γ₀ = ⊤`, `γ_{ν+1} = ⁅γ_ν, ⊤⁆` is contained
term by term in the descending `p`-central series `P₀ = ⊤`, `P_{ν+1} = P_ν^p ⁅P_ν, ⊤⁆`
(Definition 3 of A. Schmidt and K. Wingberg, *Šafarevič's theorem on solvable groups as
Galois groups*, arXiv:math/9809211): the commutator term `⁅γ_ν, ⊤⁆` is one of the two
generating pieces of the next `p`-central term.

This is what allows statements about the `p`-central filtration of `P` to be applied to the
lower central series, i.e. it links the descending central series (which governs nilpotency
and the nilpotency class) with the filtration used in the shrinking procedure.
-/

import Mathlib
import Submission.Work.ProP.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.ProP

/-- The lower central series of `P` (the series `γ₀ = ⊤`, `γ_{ν+1} = ⁅γ_ν, ⊤⁆`) is
contained in the descending `p`-central series `P₀ = ⊤`, `P_{ν+1} = P_ν^p ⁅P_ν, ⊤⁆`.

Indeed `γ_{ν+1} = ⁅γ_ν, ⊤⁆ ≤ ⁅P_ν, ⊤⁆ ≤ P_ν^p ⁅P_ν, ⊤⁆ = P_{ν+1}` as soon as
`γ_ν ≤ P_ν`, and `γ₀ = ⊤ = P₀`. -/
theorem lowerCentralSeries_le_pCentralSeries (p : ℕ) (P : Type*) [Group P] (ν : ℕ) :
    (⊤ : Subgroup P).lowerCentralSeries ν ≤ Work.Shrinking.pCentralSeries p P ν := by
  induction ν with
  | zero => simp
  | succ n ih =>
    rw [Subgroup.lowerCentralSeries_succ, Work.Shrinking.pCentralSeries_succ,
      Work.Shrinking.pCentralStep]
    exact le_trans (Subgroup.commutator_mono ih le_rfl) le_sup_right

end Work.ProP

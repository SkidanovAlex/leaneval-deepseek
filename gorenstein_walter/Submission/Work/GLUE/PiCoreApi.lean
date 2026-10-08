/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GLUE area (fundmath3-gorenstein_walter)
-/
import Submission.Work.GLUE.Bridge

set_option autoImplicit false

open scoped MatrixGroups
open Subgroup

/-!
# GLUE: the `π`-cores `O_π(G)`, the odd core `O(G)`, and `F_π(G)`

Elementary API of `Work.GW2.piCore`, `Work.GW2.oddCore` and `Work.GW2.fittingPi` in our own
notation, so that consumer areas (`RED`, `DSTR`, the `CORE` areas) can use them without
unfolding definitions:

* `le_piCore_of_normal_isPiGroup`, `le_oddCore_of_odd_normal` — universal properties;
* `isPiSubgroup_oddCore`, `odd_card_oddCore` — `O(G)` really has odd order;
* `fittingPi_le`, `fittingPi_eq_oPiCore` — the shape of `F_π(G) = O_π(F(G))`.
-/

namespace Work.GW2

variable {G : Type*} [Group G]

/-- **Universal property of `O_π(G)`.** Every normal `π`-subgroup lies in `piCore π G`. -/
theorem le_piCore_of_normal_isPiGroup {π : Set ℕ} {N : Subgroup G} [N.Normal]
    (hN : Subgroup.IsPiSubgroup π N) : N ≤ piCore π G :=
  Subgroup.normal_le_normalCore.mpr (le_sSup ⟨‹N.Normal›, hN⟩)

/-- **Universal property of `O(G)`.** Every normal subgroup of odd order lies in `oddCore G`. -/
theorem le_oddCore_of_odd_normal {N : Subgroup G} [N.Normal] (hN : Odd (Nat.card N)) :
    N ≤ oddCore G :=
  Subgroup.normal_le_normalCore.mpr (le_sSup ⟨‹N.Normal›, hN⟩)

/-- `O(G) = O_{2'}(G)` is a `{2}ᶜ`-subgroup. -/
theorem isPiSubgroup_oddCore [Finite G] :
    Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) (oddCore G) := by
  rw [oddCore_eq_oPiCore]
  exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup {q : ℕ | q ≠ 2}

/-- `O(G)` has odd order. -/
theorem odd_card_oddCore [Finite G] : Odd (Nat.card (oddCore G)) :=
  (odd_card_iff_isPiSubgroup_ne_two (oddCore G)).mpr isPiSubgroup_oddCore

/-- `O_π` is monotone in `π`. -/
theorem piCore_mono {π₁ π₂ : Set ℕ} (h : π₁ ⊆ π₂) : piCore π₁ G ≤ piCore π₂ G := by
  rw [piCore, piCore]
  refine Subgroup.normalCore_mono (sSup_le ?_)
  rintro N ⟨hN, hpi⟩
  exact le_sSup ⟨hN, fun q hq => h (hpi q hq)⟩

/-- `F_π(G) = O_π(F(G)) ≤ F(G)`. -/
theorem fittingPi_le (π : Set ℕ) : fittingPi π G ≤ fitting G :=
  Subgroup.map_subtype_le _

/-- `F_π(G)` written with the library's `O_π`: `F_π(G) = O_π(F(G))`, realized inside `G`. -/
theorem fittingPi_eq_oPiCore (π : Set ℕ) :
    fittingPi π G
      = (OddOrder.Isaacs.Ch03.oPiCore π ↥(fitting G)).map (fitting G).subtype := by
  rw [fittingPi, piCore_eq_oPiCore]

end Work.GW2

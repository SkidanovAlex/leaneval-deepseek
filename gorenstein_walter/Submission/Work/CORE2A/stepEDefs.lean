/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs

/-!
# CORE2A: the subgroup `P₁` of Bender 1981, p. 221 (step 3 of Theorem 2.6)

For a Bender setup `B`, a `B.H`-invariant `p`-subgroup `P` and an involution `s` we write

`stepP1sub B P s = ⁅⟨B.t⟩, P ⊓ C_G(s)⁆`,

the subgroup called `P₁` in Bender 1981, p. 221 (proof of Theorem 2.6, third paragraph):
`1 ≠ P₁ := [t, C_P(s)] ≤ C_P(s) = Ĥ^g ∩ P`.

Its main properties (proved elsewhere in the area) are

* `P₁ ≤ O_p(Ĥ^g)` — `Work.CORE2A.bender26c_stepP1`;
* `P₁ ≤ P ≤ O_p(Ĥ)` — `Work.CORE2A.b26c_commutator_eq`, `b26c_commutator_le_pCoreIn`;
* `P₁ = C_P(s)`, because `C_P(t) = 1` in the configuration.

It is introduced here only so that the statements of the lemmas of this step
(`CORE2A/bender26c_stepS1`, `CORE2A/bender26c_stepE`, …) stay readable; it is a plain `def`
and is meant to be unfolded by `simp [Work.CORE2A.stepP1sub]` or `rfl`.
-/

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-- `P₁ = ⁅⟨t⟩, P ⊓ C_G(s)⁆` (Bender 1981, p. 221, step 3 of Theorem 2.6). -/
noncomputable def stepP1sub {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (P : Subgroup G) (s : G) : Subgroup G :=
  ⁅Subgroup.zpowers B.t, P ⊓ Subgroup.centralizer ({s} : Set G)⁆

@[simp]
theorem stepP1sub_def {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (P : Subgroup G) (s : G) :
    Work.CORE2A.stepP1sub B P s =
      ⁅Subgroup.zpowers B.t, P ⊓ Subgroup.centralizer ({s} : Set G)⁆ := rfl

end Work.CORE2A

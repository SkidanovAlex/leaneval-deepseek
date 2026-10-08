/-
Copyright (c) 2024. All rights reserved.

# The `C₄` residual: an elementary fact about `Erad := {x : ⁅x,⊤⁆ ≤ A²}`

Session 9.  In the `C₄` setting with the residual hypothesis (`⁅⊤,D⁆ = A`, `D/A` a minimal
`ξ`-section, `⁅D,D⁆ = D² = A²`, `|D| = q³`) the subgroup

  `Erad := {x : ⁅x,⊤⁆ ≤ A²}`  (`= C_{P/A²}(P/A²)`-preimage)

satisfies `Erad = A`, equivalently `Z(P/Z) = A/Z = W`.  The full derivation is recorded in
`NOTES_c4_sq_a2_SESSION9.md` §3b′; the elementary ingredient is

* `comm_sq_eq_one_of_comm_mem_omega1`: if `⁅x,y⁆` is a central involution (in particular if
  `⁅x,y⁆ ∈ Ω₁(P)` and `Ω₁(P) ⊆ Z(P)`) then `⁅x²,y⁆ = 1`.  Consequently
  `x ∈ Erad ⟹ x² ∈ Z(P) = Ω₁(P)`, i.e. `Erad ⊆ {x : x² ∈ Ω₁(P)}`.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.OmegaAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman.H8

variable {P : Type} [Group P]

/-- `⁅x²,y⁆ = ⁅x,⁅x,y⁆⁆ ⁅x,y⁆²`. -/
theorem comm_sq_self (x y : P) :
    ⁅x ^ 2, y⁆ = ⁅x, ⁅x, y⁆⁆ * ⁅x, y⁆ ^ 2 := by
  simp only [commutatorElement_def, pow_two]
  group

/-- If `⁅x,⁅x,y⁆⁆ = 1` and `⁅x,y⁆ ^ 2 = 1` then `⁅x²,y⁆ = 1`.  In a Suzuki 2-group, taking
`y : P` and `x ∈ Erad := {x : ⁅x,⊤⁆ ≤ Ω₁(P)}` these two hypotheses hold because `⁅x,y⁆` is a
central involution. -/
theorem comm_sq_eq_one_of_comm_sq_eq_one (x y : P)
    (h1 : ⁅x, ⁅x, y⁆⁆ = 1) (h2 : ⁅x, y⁆ ^ 2 = 1) : ⁅x ^ 2, y⁆ = 1 := by
  rw [comm_sq_self x y, h1, one_mul, h2]

/-- `x ∈ Erad` (i.e. `⁅x,y⁆ ∈ Ω₁(P)` for all `y`) implies `x²` is central, hence
`x² ∈ Z(P) = Ω₁(P)`. -/
theorem comm_eq_one_of_mem_omega1_left {x y : P}
    (hZ : Work.Higman.omega1 P ≤ Subgroup.center P) (hx : ⁅x, y⁆ ∈ Work.Higman.omega1 P)
    (h2 : ⁅x, y⁆ ^ 2 = 1) : ⁅x ^ 2, y⁆ = 1 := by
  have hc : ⁅x, y⁆ ∈ Subgroup.center P := hZ hx
  exact comm_sq_eq_one_of_comm_sq_eq_one x y
    (commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hc x)) h2

end Work.Higman.H8

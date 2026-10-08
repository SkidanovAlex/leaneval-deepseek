/-
Copyright (c) 2024. All rights reserved.

# The class-two case: every square is central

Let `P` be a Suzuki 2-group (Higman 1963, `Submission.Work.Higman.Defs`) admitting a
fixed-point-free `ξ` with `|P| = |Z(P)|³` and `orderOf ξ = |Z(P)| - 1` (`FpfXi ξ`).
Assume moreover that `P` is of **class two**, i.e. `P' = derivTop P ≤ Z(P)`.

Then every square of an element of `P` is central, i.e. `P / Z(P)` is elementary abelian.

The argument is the standard one for class-two groups and uses only

* `[x², y] = [x, y] ^ x · [x, y]`, which for a central `[x, y]` gives `[x², y] = [x, y]²`
  (`Commute.commutatorElement_pow_left`), and
* `Z(P) = Ω₁(P)` (`center_eq_omega1_of_fpf`, `center_sq_one`): the central element `[x, y]`
  has order `2`, so `[x, y]² = 1` and `x²` centralises `y`.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.typeB
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.LayersAlt.fpf_defs
import Submission.Work.Higman.LayersAlt.GroupSide
import Submission.Work.Higman.BS.fpf
import Submission.Work.Higman.MSA.lemma8_clean

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open scoped commutatorElement

namespace Work.Higman.LayersAlt

/-- In a group of class two (i.e. with `P' ≤ Z(P)`) every square is central.  This is the
purely group-theoretic core of `class_two_target`; the Suzuki hypothesis then only enters to
provide `[x, y]² = 1` for central `[x, y]`. -/
theorem sq_mem_center_of_commutator_le_center {G : Type} [Group G]
    (h : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) {x y : G}
    (hxy2 : ⁅x, y⁆ ^ 2 = 1) : x ^ 2 * y = y * x ^ 2 := by
  have hZ : ⁅x, y⁆ ∈ Subgroup.center G :=
    h (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
  have hcomm : Commute x ⁅x, y⁆ := Subgroup.mem_center_iff.mp hZ x
  have h1 : ⁅x ^ 2, y⁆ = 1 := by
    rw [← hcomm.commutatorElement_pow_left 2, hxy2]
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem class_two_target {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {ξ : MulAut P} (hξ : Work.Higman.FpfXi ξ)
    (hcl2 : Work.Higman.LayersAlt.derivTop P ≤ Subgroup.center P) :
    ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
  intro x
  rw [Subgroup.mem_center_iff]
  intro y
  have hmem : ⁅x, y⁆ ∈ Work.Higman.LayersAlt.derivTop P :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  have hZ : ⁅x, y⁆ ∈ Subgroup.center P := hcl2 hmem
  refine (sq_mem_center_of_commutator_le_center hcl2 ?_).symm
  -- `Z(P) = Ω₁(P)`, so a central element has order dividing two
  rw [pow_two]
  exact center_sq_one h hξ hZ

end Work.Higman.LayersAlt

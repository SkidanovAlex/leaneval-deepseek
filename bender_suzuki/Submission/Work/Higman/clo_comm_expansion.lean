import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The commutator of the first layer, modulo `A ^ (2)`

Setting: `P` a Suzuki 2-group, `A` a `ξ`-invariant abelian normal subgroup, `C` a subgroup with
`⁅C, C⁆ = A`.  Since `⁅A, P⁆ ≤ A ^ (2)` (unipotence, `commutator_mem_powSub_two`), every
commutator of two elements of `C` — an element of `A` — behaves multiplicatively modulo `A ^ (2)`
in each variable:

* `⁅x * y, z⁆ ≡ ⁅y, z⁆ * ⁅x, z⁆ (mod A ^ (2))`;
* `⁅x, y * z⁆ ≡ ⁅x, y⁆ * ⁅x, z⁆ (mod A ^ (2))`.

These are the two identities that make the pairing `(uA, vA) ↦ ⁅u⁻¹, v⁆` on `C/A` additive modulo
`A ^ (2)`; raising to the power `2 ^ (e-1)` (with `2 ^ e` the exponent of `A`) turns that into
biadditivity of `cloBPair`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- **Left expansion.**  For `x, y, z ∈ C` the commutator is additive in the first variable modulo
`A ^ (2)`: `⁅x * y, z⁆ · (⁅y, z⁆ * ⁅x, z⁆)⁻¹ ∈ A ^ (2)`.

Indeed `⁅x * y, z⁆ = x · ⁅y, z⁆ · x⁻¹ · ⁅x, z⁆` and the correction
`x · ⁅y, z⁆ · x⁻¹ · ⁅y, z⁆⁻¹ = ⁅x, ⁅y, z⁆⁆` lies in `A ^ (2)` because `⁅y, z⁆ ∈ ⁅C,C⁆ = A`
and `⁅A, P⁆ ≤ A ^ (2)`. -/
theorem clo_comm_mul_left (h : IsSuzuki2Grp P) {A C : Subgroup P} (hA : IsXiAbelNormal h A)
    (hCd : ⁅C, C⁆ = A) {x y z : P} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C) :
    ⁅x * y, z⁆ * (⁅y, z⁆ * ⁅x, z⁆)⁻¹ ∈ powSub A 2 := by
  have hid : ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
    simp only [commutatorElement_def]; group
  have hmem : ⁅y, z⁆ ∈ A := hCd ▸ Subgroup.commutator_mem_commutator hy hz
  have h2 : ⁅x, ⁅y, z⁆⁆ ∈ powSub A 2 := commutator_mem_powSub_two h hA x ⁅y, z⁆ hmem
  have heq : ⁅x * y, z⁆ * (⁅y, z⁆ * ⁅x, z⁆)⁻¹ = ⁅x, ⁅y, z⁆⁆ := by
    rw [hid]; simp only [commutatorElement_def]; group
  rw [heq]; exact h2

/-- **Right expansion.**  For `x, y, z ∈ C` the commutator is additive in the second variable modulo
`A ^ (2)`: `⁅x, y * z⁆ · (⁅x, y⁆ * ⁅x, z⁆)⁻¹ ∈ A ^ (2)`.

Indeed `⁅x, y * z⁆ = ⁅x, y⁆ · (y · ⁅x, z⁆ · y⁻¹)` and the correction
`y · ⁅x, z⁆ · y⁻¹ · ⁅x, z⁆⁻¹ = ⁅y, ⁅x, z⁆⁆` lies in `A ^ (2)`. -/
theorem clo_comm_mul_right (h : IsSuzuki2Grp P) {A C : Subgroup P} (hA : IsXiAbelNormal h A)
    (hCd : ⁅C, C⁆ = A) {x y z : P} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C) :
    ⁅x, y * z⁆ * (⁅x, y⁆ * ⁅x, z⁆)⁻¹ ∈ powSub A 2 := by
  have hid : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
    simp only [commutatorElement_def]; group
  have hmem : ⁅x, y⁆ ∈ A := hCd ▸ Subgroup.commutator_mem_commutator hx hy
  have hmem2 : ⁅x, z⁆ ∈ A := hCd ▸ Subgroup.commutator_mem_commutator hx hz
  have h2 : ⁅y, ⁅x, z⁆⁆ ∈ powSub A 2 := commutator_mem_powSub_two h hA y ⁅x, z⁆ hmem2
  have h2A : ⁅y, ⁅x, z⁆⁆ ∈ A := powSub_le (by norm_num) h2
  have heq : ⁅x, y * z⁆ * (⁅x, y⁆ * ⁅x, z⁆)⁻¹ = ⁅y, ⁅x, z⁆⁆ := by
    have hconj : y * ⁅x, z⁆ * y⁻¹ = ⁅y, ⁅x, z⁆⁆ * ⁅x, z⁆ := by
      simp only [commutatorElement_def]; group
    have hstep : ⁅x, y * z⁆ * (⁅x, y⁆ * ⁅x, z⁆)⁻¹
        = ⁅x, y⁆ * ⁅y, ⁅x, z⁆⁆ * ⁅x, y⁆⁻¹ := by
      rw [hid, hconj]; group
    rw [hstep, hA.abelian ⁅x, y⁆ hmem ⁅y, ⁅x, z⁆⁆ h2A]
    group
  rw [heq]; exact h2

end Work.Higman

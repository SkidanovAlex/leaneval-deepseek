import Mathlib
import Submission.Work.MotT.Defs
import Submission.Work.MotC2.InfPlaceCore
import Submission.Work.MotC2.PoleOrder
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Auxiliary vocabulary for `Work.MotT.exists_kleinPoint`

The Klein model `C = V(p_0, …, p_4) ⊂ ℙ⁴` of the Weierstrass curve `E = D.E` is the image of `E`
under the degree-`5` embedding given by the Klein coordinates `κ_i` in the basis
`b = (1, x, y, x², xy)` of `𝓛(5·O)`.  At the point at infinity `O`, the basis elements have poles of
order `0, 2, 3, 4, 5`; normalising by powers of the uniformizer `w = y/x²` makes them units of the
local ring `↥(infPlace E)` (this is the content of `kP`/`kQ` below and of
`infW_genX_sub_one_mem`).

* `kP m` is the pole order at `O` of the `m`-th basis element `1, x, y, x², xy`;
* `kQ m` is the exponent of `g = w²·x` with `w^{kP m} · b_m = g^{kQ m}`.
-/

namespace Work.MotT

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine

/-- Pole orders at the point at infinity of the basis `1, x, y, x², xy` of `𝓛(5·O)`. -/
def kP : Fin 5 → ℕ := ![0, 2, 3, 4, 5]

/-- Exponents of `g = (infW E)²·genX E` in the normalised basis `w^{kP m}·b_m`. -/
def kQ : Fin 5 → ℕ := ![0, 1, 2, 2, 3]

@[simp] theorem kP_zero : kP 0 = 0 := rfl
@[simp] theorem kP_one : kP 1 = 2 := rfl
@[simp] theorem kP_two : kP 2 = 3 := rfl
@[simp] theorem kP_three : kP 3 = 4 := rfl
@[simp] theorem kP_four : kP 4 = 5 := rfl

@[simp] theorem kQ_zero : kQ 0 = 0 := rfl
@[simp] theorem kQ_one : kQ 1 = 1 := rfl
@[simp] theorem kQ_two : kQ 2 = 2 := rfl
@[simp] theorem kQ_three : kQ 3 = 2 := rfl
@[simp] theorem kQ_four : kQ 4 = 3 := rfl

/-- `kP` is strictly increasing: the pole orders distinguish the five basis elements. -/
theorem kP_lt_iff {m m' : Fin 5} : kP m < kP m' ↔ m < m' := by
  fin_cases m <;> fin_cases m' <;> decide

theorem kP_le_iff {m m' : Fin 5} : kP m ≤ kP m' ↔ m ≤ m' := by
  fin_cases m <;> fin_cases m' <;> decide

theorem kP_le_five (m : Fin 5) : kP m ≤ 5 := by
  fin_cases m <;> decide

/-- `w³·y = (w²·x)²`: the second basis element in the normalised form. -/
theorem infW_cube_mul_genY_eq {L : Type} [Field L] (E : WeierstrassCurve L) :
    (Work.MotC2.infW E) ^ 3 * Work.MotC2.genY E =
      (Work.MotC2.genX E * (Work.MotC2.infW E) ^ 2) ^ 2 := by
  rw [Work.MotC2.genY_eq_infW_mul]; ring

/-- `w⁴·x² = (w²·x)²`: the third basis element in the normalised form. -/
theorem infW_pow_four_mul_genX_sq_eq {L : Type} [Field L] (E : WeierstrassCurve L) :
    (Work.MotC2.infW E) ^ 4 * (Work.MotC2.genX E) ^ 2 =
      (Work.MotC2.genX E * (Work.MotC2.infW E) ^ 2) ^ 2 := by
  first | refl_ring1 | ring

/-- `w⁵·x·y = (w²·x)³`: the fourth basis element in the normalised form. -/
theorem infW_pow_five_mul_genX_mul_genY_eq {L : Type} [Field L] (E : WeierstrassCurve L) :
    (Work.MotC2.infW E) ^ 5 * (Work.MotC2.genX E * Work.MotC2.genY E) =
      (Work.MotC2.genX E * (Work.MotC2.infW E) ^ 2) ^ 3 := by
  rw [Work.MotC2.genY_eq_infW_mul]; ring

end

end Work.MotT

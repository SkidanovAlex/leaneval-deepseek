-- LOCAL COPY of `Submission/Work/Higman/suzuki_class_two_squares.lean` (namespace `Work.ZassenhausSuzuki.HigmanLocal`), made so that the modules
-- `Submission.Work.Higman.no_square_maximal` and `Submission.Work.Higman.reducible_aux`
-- (which do not build while `Work.Higman.NSM.redcase` is unfinished) are not needed.
-- Identical to the original except for the import/namespace changes below.
import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.ZassenhausSuzuki.HigmanGap.commutator_le_omega1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.ZassenhausSuzuki.HigmanLocal

open Work.Higman

open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

/-- `x * y * x⁻¹ = ⁅x, y⁆ * y`. -/
theorem mul_mul_inv_eq_commutator_mul' (x y : P) : x * y * x⁻¹ = ⁅x, y⁆ * y := by
  rw [commutatorElement_def]; group

/-- Every commutator of `P` lies in `Ω₁(P)` when `[P,P] ≤ Ω₁(P)`. -/
theorem commutator_mem_omega1_of_le
    (hcomm : commutator P ≤ omega1 P) (x y : P) : ⁅x, y⁆ ∈ omega1 P :=
  hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))

/-- `[P,P] ≤ Ω₁(P)` implies `[P,P] ≤ Z(P)`. -/
theorem commutator_le_center_of_le_omega1 (h : IsSuzuki2Grp P)
    (hcomm : commutator P ≤ omega1 P) :
    ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P :=
  (le_of_eq (commutator_def P).symm).trans (hcomm.trans h.omega1_le_center)

/-- In a Suzuki 2-group, `[P,P] ≤ Ω₁(P)` makes every square central: the class-`2` computation
`x ^ 2 * y = ⁅x, y⁆ ^ 2 * y * x ^ 2 = y * x ^ 2`. -/
theorem sq_mul_eq_mul_sq_of_le_omega1 (h : IsSuzuki2Grp P)
    (hcomm : commutator P ≤ omega1 P) (x y : P) : x ^ 2 * y = y * x ^ 2 := by
  have hc : ⁅x, y⁆ ∈ Subgroup.center P :=
    h.omega1_le_center (commutator_mem_omega1_of_le hcomm x y)
  have hcc : ⁅x, y⁆ * ⁅x, y⁆ = 1 := by
    have h1 := h.mem_omega1.mp (commutator_mem_omega1_of_le hcomm x y)
    rwa [pow_two] at h1
  have hcx : x * ⁅x, y⁆ = ⁅x, y⁆ * x := (Subgroup.mem_center_iff.mp hc) x
  have h1 : x * y = ⁅x, y⁆ * y * x := by
    have h2 := mul_mul_inv_eq_commutator_mul' x y
    rw [← h2]; group
  calc x ^ 2 * y = x * (x * y) := by rw [pow_two]; group
    _ = x * (⁅x, y⁆ * y * x) := by rw [h1]
    _ = (x * ⁅x, y⁆) * y * x := by group
    _ = (⁅x, y⁆ * x) * y * x := by rw [hcx]
    _ = ⁅x, y⁆ * (x * y) * x := by group
    _ = ⁅x, y⁆ * (⁅x, y⁆ * y * x) * x := by rw [h1]
    _ = (⁅x, y⁆ * ⁅x, y⁆) * y * (x * x) := by group
    _ = y * (x * x) := by rw [hcc]; group
    _ = y * x ^ 2 := by rw [pow_two]

/-- In a Suzuki 2-group with `[P,P] ≤ Ω₁(P)`, every square is central. -/
theorem sq_mem_center_of_le_omega1 (h : IsSuzuki2Grp P)
    (hcomm : commutator P ≤ omega1 P) (x : P) : x ^ 2 ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  intro y
  exact (sq_mul_eq_mul_sq_of_le_omega1 h hcomm x y).symm

/-- **Suzuki 2-groups have class two and squares central.**  In a Suzuki 2-group `P` the
commutator subgroup is central and the square of every element is central.  Both follow from
Higman's Theorem 1 (`Ω₁(P) = Z(P) = Φ(P) = P'`, i.e. `[P,P] ≤ Ω₁(P)`). -/
theorem suzuki_class_two_squares {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) :
    (⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P) ∧ (∀ x : P, x ^ 2 ∈ Subgroup.center P) := by
  have hcomm : commutator P ≤ omega1 P := Work.ZassenhausSuzuki.HigmanLocal.commutator_le_omega1 h
  exact ⟨commutator_le_center_of_le_omega1 h hcomm,
    fun x => sq_mem_center_of_le_omega1 h hcomm x⟩

end Work.ZassenhausSuzuki.HigmanLocal

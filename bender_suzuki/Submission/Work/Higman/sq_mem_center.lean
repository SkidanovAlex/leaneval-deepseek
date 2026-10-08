import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.commutator_le_omega1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman

open scoped commutatorElement

/-- In a Suzuki 2-group the commutator subgroup is central: `P' ≤ Z(P)`
(`P' ≤ Ω₁(P)` by `commutator_le_omega1` and `Ω₁(P) ≤ Z(P)` by `omega1_le_center`). -/
theorem commutator_le_center {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P) :
    ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P :=
  (commutator_le_omega1 h).trans h.omega1_le_center

/-- In a Suzuki 2-group every commutator is a central involution:
`⁅x, y⁆ ∈ Z(P)` (via `P' ≤ Ω₁(P) ≤ Z(P)`) and `⁅x, y⁆ * ⁅x, y⁆ = 1`. -/
theorem commutator_mem_center_invol {P : Type} [Group P] [Finite P]
    (h : IsSuzuki2Grp P) (x y : P) :
    ⁅x, y⁆ ∈ Subgroup.center P ∧ ⁅x, y⁆ * ⁅x, y⁆ = 1 := by
  have hmem : ⁅x, y⁆ ∈ omega1 P :=
    commutator_le_omega1 h
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
  refine ⟨h.omega1_le_center hmem, ?_⟩
  have h1 : ⁅x, y⁆ ^ 2 = 1 := h.mem_omega1.mp hmem
  rwa [pow_two] at h1

/-- In a Suzuki 2-group every square commutes with every element: the class-`2` computation
`x ^ 2 * y = ⁅x, y⁆ ^ 2 * y * x ^ 2 = y * x ^ 2` (using that `⁅x, y⁆` is a central involution). -/
theorem sq_mul_eq_mul_sq {P : Type} [Group P] [Finite P] (h : IsSuzuki2Grp P) (x y : P) :
    x ^ 2 * y = y * x ^ 2 := by
  obtain ⟨hcZ, hcc⟩ := commutator_mem_center_invol h x y
  have hc : x * ⁅x, y⁆ = ⁅x, y⁆ * x := (Subgroup.mem_center_iff.mp hcZ) x
  have h1 : x * y = ⁅x, y⁆ * y * x := by
    have := congrArg (fun t => t * x) (mul_mul_inv_eq_commutator_mul x y)
    simpa [mul_assoc] using this
  calc x ^ 2 * y = x * (x * y) := by rw [pow_two]; group
    _ = x * (⁅x, y⁆ * y * x) := by rw [h1]
    _ = (x * ⁅x, y⁆) * y * x := by group
    _ = (⁅x, y⁆ * x) * y * x := by rw [hc]
    _ = ⁅x, y⁆ * (x * y) * x := by group
    _ = ⁅x, y⁆ * (⁅x, y⁆ * y * x) * x := by rw [h1]
    _ = (⁅x, y⁆ * ⁅x, y⁆) * y * (x * x) := by group
    _ = y * (x * x) := by rw [hcc]; group
    _ = y * x ^ 2 := by rw [pow_two]

/-- In a Suzuki 2-group every square is central (`P / Z(P)` is elementary abelian;
Higman 1963: `P` has exponent `4` and class `2`, so `x ^ 2 ∈ Φ(P) = Z(P)`). -/
theorem sq_mem_center {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) (x : P) :
    x ^ 2 ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  intro y
  exact (sq_mul_eq_mul_sq h x y).symm

end Work.Higman

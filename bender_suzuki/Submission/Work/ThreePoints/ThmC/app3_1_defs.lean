/-
# Elementary vocabulary for Peterfalvi I Appendix III (1)

The kernel of a group action and its basic properties.  Kept in a separate, `hole`-free
module so that helper lemmas proved elsewhere can import it.
-/
import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.ThreePoints.ThmC

open LeanEval.GroupTheory.Defs

variable {F A : Type} [Group F] [MulAction F A]

/-- The kernel of a group action, as a subgroup of the acting group. -/
def actKer (F A : Type) [Group F] [MulAction F A] : Subgroup F where
  carrier := {x | ∀ c : A, x • c = c}
  mul_mem' := by
    intro a b ha hb c
    rw [mul_smul, hb c, ha c]
  one_mem' := by
    intro c
    exact one_smul F c
  inv_mem' := by
    intro a ha c
    have h := ha (a⁻¹ • c)
    rw [← mul_smul, mul_inv_cancel, one_smul] at h
    exact h.symm

/-- Elements of the kernel fix every point. -/
theorem mem_actKer {x : F} : x ∈ actKer F A ↔ ∀ c : A, x • c = c := Iff.rfl

/-- The kernel is contained in every point stabiliser. -/
theorem actKer_le_stabilizer (c : A) : actKer F A ≤ MulAction.stabilizer F c :=
  fun _ hx => MulAction.mem_stabilizer_iff.mpr (mem_actKer.mp hx c)

/-- The kernel of the action is normal. -/
theorem actKer_normal : (actKer F A).Normal := by
  refine Subgroup.Normal.mk fun n hn g => ?_
  intro c
  have hn' : n • (g⁻¹ • c) = g⁻¹ • c := hn (g⁻¹ • c)
  rw [mul_smul, mul_smul, hn', smul_inv_smul]

/-- A normal subgroup contained in a point stabiliser acts trivially. -/
theorem le_actKer_of_normal_le_stabilizer (a : A) (htrans : MulAction.IsPretransitive F A)
    {N : Subgroup F} (hN : N.Normal) (hle : N ≤ MulAction.stabilizer F a) : N ≤ actKer F A := by
  haveI : MulAction.IsPretransitive F A := htrans
  intro x hx
  rw [mem_actKer]
  intro c
  obtain ⟨g, rfl⟩ := MulAction.IsPretransitive.exists_smul_eq (M := F) (α := A) a c
  have hconj : g⁻¹ * x * g ∈ N := by simpa using hN.conj_mem x hx g⁻¹
  have hfix : (g⁻¹ * x * g) • a = a :=
    MulAction.mem_stabilizer_iff.mp (hle hconj)
  calc x • (g • a) = (x * g) • a := (mul_smul x g a).symm
    _ = (g * (g⁻¹ * x * g)) • a := by rw [mul_assoc, mul_inv_cancel_left]
    _ = g • ((g⁻¹ * x * g) • a) := mul_smul g _ a
    _ = g • a := by rw [hfix]

end Work.ThreePoints.ThmC

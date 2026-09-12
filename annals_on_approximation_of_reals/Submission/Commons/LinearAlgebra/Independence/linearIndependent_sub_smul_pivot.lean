import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs

noncomputable section

namespace Commons.LinearAlgebra.Independence

/-- Shear preserves linear independence over ℝ: if `v : ι → E` is a linearly independent
family and `a : ι` is a distinguished index, then the family obtained by subtracting from
every other vector a scalar multiple of the pivot `v a` (with the pivot itself unchanged)
is still linearly independent. -/
theorem linearIndependent_sub_smul_pivot {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι)
    {E : Type*} [AddCommGroup E] [Module ℝ E] (v : ι → E) (m : ι → ℝ)
    (hv : LinearIndependent ℝ v) :
    LinearIndependent ℝ (fun i : ι => v i - (if i = a then 0 else m i • v a)) := by
  -- Shear with coefficient function c (vanishing at the pivot index a):
  -- w i = v i + c i • v a, where c i = -m i for i ≠ a and c a = 0.
  let c : ι → ℝ := fun i => - (if i = a then 0 else m i)
  have hc : c a = 0 := by
    simp [c]
  have hfam : (fun i : ι => v i + c i • v a) =
      fun i : ι => v i - (if i = a then 0 else m i • v a) := by
    funext i
    by_cases hi : i = a
    · subst i
      simp [c]
    · simp [c, hi, neg_smul, sub_eq_add_neg]
  rw [← hfam]
  exact (linearIndependent_add_smul_iff (v := v) (c := c) (i := a) hc).2 hv

end Commons.LinearAlgebra.Independence
import Mathlib
import Submission.Work.HP.Defs

set_option autoImplicit false
noncomputable section

namespace Work.HP

/-- The linear functional `u ↦ ∑ i, c i * u i` on `ι → ℝ`, for an integer vector `c`.  For
`c ≠ 0` its kernel is the real hyperplane `c^⊥`, the real span of `latOrth c`. -/
def dotLin {ι : Type*} [Fintype ι] (c : ι → ℤ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun u := ∑ i, (c i : ℝ) * u i
  map_add' u v := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a u := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

@[simp] lemma dotLin_apply {ι : Type*} [Fintype ι] (c : ι → ℤ) (u : ι → ℝ) :
    dotLin c u = ∑ i, (c i : ℝ) * u i := rfl

end Work.HP

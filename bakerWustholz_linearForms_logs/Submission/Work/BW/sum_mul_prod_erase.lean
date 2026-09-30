import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

lemma sum_mul_prod_erase {m : ℕ} (h : Fin m → ℝ) :
    ∑ i, h i * ∏ j ∈ Finset.univ.erase i, h j = (m : ℝ) * ∏ i, h i := by
  have hterm : ∀ i : Fin m, h i * ∏ j ∈ Finset.univ.erase i, h j = ∏ i, h i := by
    intro i
    rw [Finset.mul_prod_erase Finset.univ h (Finset.mem_univ i)]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  simp

end Work.BW

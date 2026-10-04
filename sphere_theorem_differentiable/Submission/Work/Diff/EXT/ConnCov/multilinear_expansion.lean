import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov

theorem multilinear_expansion
    {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*} [∀ i, AddCommMonoid (V i)]
    [∀ i, Module ℝ (V i)]
    (T : MultilinearMap ℝ V ℝ) (n : ℕ) (lam : (i : ι) → Fin n → ℝ) (w : (i : ι) → Fin n → V i) :
    T (fun i => ∑ j, lam i j • w i j)
      = ∑ r : ι → Fin n, (∏ i, lam i (r i)) * T (fun i => w i (r i)) := by
  rw [MultilinearMap.map_sum]
  congr 1
  funext r
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]

end Work.Diff.EXT.ConnCov

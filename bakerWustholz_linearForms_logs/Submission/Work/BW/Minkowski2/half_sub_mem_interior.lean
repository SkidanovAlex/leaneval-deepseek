import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW.Minkowski2

theorem half_sub_mem_interior {d : ℕ} {K : Set (Fin d → ℝ)} (hKc : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) {u v : Fin d → ℝ} (hu : u ∈ interior K) (hv : v ∈ interior K) :
    (1/2 : ℝ) • (u - v) ∈ interior K := by
  have hvK : v ∈ K := interior_subset hv
  have hnvK : -v ∈ K := hsym v hvK
  have hmem : (1/2 : ℝ) • u + (1/2 : ℝ) • (-v) ∈ interior K :=
    hKc.combo_interior_self_mem_interior hu hnvK (by norm_num) (by norm_num) (by norm_num)
  have heq : (1/2 : ℝ) • (u - v) = (1/2 : ℝ) • u + (1/2 : ℝ) • (-v) := by
    rw [smul_sub, smul_neg, sub_eq_add_neg]
  rwa [heq]

end Work.BW.Minkowski2

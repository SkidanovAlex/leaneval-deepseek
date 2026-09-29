import Mathlib

namespace Work.Holonomy3

lemma filter_div_eq_top {m d k u : ℕ} (hk : 0 < k) (hmul : m * k = d) (hu : u ≤ m) :
    (Finset.univ.filter (fun j : Fin d => u ≤ (j : ℕ) / k)) =
      (Finset.univ.filter (fun j : Fin d => d - (m - u) * k ≤ (j : ℕ))) := by
  have hk_le : u * k ≤ m * k := Nat.mul_le_mul_right k hu
  have hsub : d - (m - u) * k = u * k := by
    rw [← hmul, Nat.sub_mul, Nat.sub_sub_self hk_le]
  apply Finset.filter_congr
  intro j _
  rw [hsub]
  exact Nat.le_div_iff_mul_le hk

end Work.Holonomy3

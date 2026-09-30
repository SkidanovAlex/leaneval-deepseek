import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

theorem unit_nodes_prod_inv_le {n : ℕ} (hn : 1 ≤ n) (r : Fin (n+1)) :
    (∏ m ∈ Finset.univ.erase r,
        |((-1 : ℝ) + 2 * (r:ℝ) / n) - ((-1 : ℝ) + 2 * (m:ℝ) / n)|)⁻¹ ≤ ((n:ℝ)/2)^n := by
  rw [← Finset.prod_inv_distrib]
  -- Bound each factor by n/2.
  have key : ∀ m : Fin (n+1), m ≠ r →
      |((-1 : ℝ) + 2 * (r:ℝ) / n) - ((-1 : ℝ) + 2 * (m:ℝ) / n)|⁻¹ ≤ (n:ℝ)/2 := by
    intro m hm
    -- The distance between two distinct nodes is at least 1.
    have hd : (1:ℝ) ≤ |(r:ℝ) - (m:ℝ)| := by
      have hz : ((r.val : ℤ) - (m.val : ℤ)) ≠ 0 := by
        intro h
        apply hm
        apply Fin.ext
        have : (m.val : ℤ) = (r.val : ℤ) := by linarith
        exact_mod_cast this
      have h1 : (1:ℤ) ≤ |((r.val : ℤ) - (m.val : ℤ))| := Int.one_le_abs hz
      have h2 : (1:ℝ) ≤ ((|((r.val : ℤ) - (m.val : ℤ))| : ℤ) : ℝ) := by exact_mod_cast h1
      rw [Int.cast_abs] at h2
      have hcast : ((↑((r.val : ℤ) - (m.val : ℤ)) : ℝ)) = (r:ℝ) - (m:ℝ) := by
        push_cast
        ring
      rwa [hcast] at h2
    have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    -- Simplify the difference of the two nodes.
    have hA : ((-1 : ℝ) + 2 * (r:ℝ) / n) - ((-1 : ℝ) + 2 * (m:ℝ) / n)
        = 2 * ((r:ℝ) - (m:ℝ)) / n := by ring
    rw [hA]
    have habs : |2 * ((r:ℝ) - (m:ℝ)) / n| = 2 * |(r:ℝ) - (m:ℝ)| / n := by
      rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg (le_of_lt hnpos)]
    rw [habs, inv_div]
    -- n / (2 * |r - m|) ≤ n / 2 since |r - m| ≥ 1.
    exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
  calc ∏ m ∈ Finset.univ.erase r,
          |((-1 : ℝ) + 2 * (r:ℝ) / n) - ((-1 : ℝ) + 2 * (m:ℝ) / n)|⁻¹
      ≤ ∏ m ∈ Finset.univ.erase r, (n:ℝ)/2 :=
        Finset.prod_le_prod₀ (fun m _ => inv_nonneg.mpr (abs_nonneg _))
          (fun m hm => key m (Finset.mem_erase.mp hm).1)
    _ = ((n:ℝ)/2) ^ (Finset.univ.erase r).card := Finset.prod_const _
    _ = ((n:ℝ)/2) ^ n := by
        congr 1
        rw [Finset.card_erase_of_mem (Finset.mem_univ r), Finset.card_univ, Fintype.card_fin]
        simp

end Work.BMF

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic

namespace Commons.Analysis.Real

theorem prod_le_div_pow_of_uniform_lower {b : ℕ} (x : Fin b → ℝ) {m P : ℝ}
    (hm : 0 < m) (hx : ∀ i, m ≤ x i) (hP : Finset.univ.prod x ≤ P) (i : Fin b) :
    x i ≤ P / m ^ (b - 1) := by
  have hmnonneg : 0 ≤ m := le_of_lt hm
  have hpow_pos : 0 < m ^ (b - 1) := pow_pos hm _
  -- split off the factor x i
  have hprod_eq : Finset.univ.prod x = x i * (Finset.univ.erase i).prod x :=
    (Finset.mul_prod_erase Finset.univ x (Finset.mem_univ i)).symm
  -- cardinality of the remaining set
  have hcard : (Finset.univ.erase i).card = b - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  -- the product of the remaining factors is at least m^(b-1)
  have hlow : m ^ (b - 1) ≤ (Finset.univ.erase i).prod x := by
    rw [← hcard]
    rw [← Finset.prod_const m]
    exact Finset.prod_le_prod (fun j _ => hmnonneg) (fun j _ => hx j)
  -- x i ≥ 0
  have hxi_nonneg : 0 ≤ x i := le_trans hmnonneg (hx i)
  -- hence x i * m^(b-1) ≤ P
  have hmul : x i * m ^ (b - 1) ≤ P := by
    have h1 : x i * m ^ (b - 1) ≤ x i * (Finset.univ.erase i).prod x :=
      mul_le_mul_of_nonneg_left hlow hxi_nonneg
    rw [← hprod_eq] at h1
    exact le_trans h1 hP
  rw [le_div_iff₀ hpow_pos]
  exact hmul

end Commons.Analysis.Real
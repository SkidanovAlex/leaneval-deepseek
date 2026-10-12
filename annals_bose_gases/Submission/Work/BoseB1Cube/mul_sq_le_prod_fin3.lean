import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

/-- If every entry of `s : Fin 3 → ℝ` is at least `δ ≥ 0`, then the full product dominates
`s j` times the square of `δ` (the remaining two factors being each `≥ δ`). -/
lemma mul_sq_le_prod_fin3 {δ : ℝ} (hδ : 0 ≤ δ) {s : Fin 3 → ℝ} (hs : ∀ k : Fin 3, δ ≤ s k) (j : Fin 3) : s j * δ ^ 2 ≤ ∏ k : Fin 3, s k := by
  have hprod : ∏ k : Fin 3, s k = s j * ∏ x ∈ (Finset.univ.erase j), s x :=
    (Finset.mul_prod_erase Finset.univ s (Finset.mem_univ j)).symm
  rw [hprod]
  have hcard : (Finset.univ.erase j).card = 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  have hsq : δ ^ 2 ≤ ∏ x ∈ (Finset.univ.erase j), s x := by
    calc δ ^ 2 = ∏ _x ∈ (Finset.univ.erase j), δ := by rw [Finset.prod_const, hcard]
      _ ≤ ∏ x ∈ (Finset.univ.erase j), s x :=
        Finset.prod_le_prod₀ (fun x _ => hδ) (fun x _ => hs x)
  exact mul_le_mul_of_nonneg_left hsq (le_trans hδ (hs j))

end Work.BoseB1Cube

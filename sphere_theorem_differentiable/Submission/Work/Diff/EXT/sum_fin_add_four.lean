import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

/-- The equivalence `((Fin n × Fin n) × Fin n) × Fin n ≃ (Fin 4 → Fin n)`
sending `(((i, j), l), m)` to the function `![i, j, l, m]`. -/
def fin4Equiv (n : ℕ) : ((Fin n × Fin n) × Fin n) × Fin n ≃ (Fin 4 → Fin n) where
  toFun p := ![p.1.1.1, p.1.1.2, p.1.2, p.2]
  invFun v := (((v 0, v 1), v 2), v 3)
  left_inv := by intro p; ext <;> simp
  right_inv := by intro v; funext i; fin_cases i <;> simp

/-- Splitting a function on `Fin (k + 4)` into its first `k` coordinates and its last four
coordinates. -/
def splitEquiv (k n : ℕ) :
    (Fin k → Fin n) × (((Fin n × Fin n) × Fin n) × Fin n) ≃ (Fin (k + 4) → Fin n) :=
  (Equiv.prodCongr (Equiv.refl _) (fin4Equiv n)).trans (Fin.appendEquiv k 4)

theorem sum_fin_add_four {k n : ℕ} (H : (Fin (k + 4) → Fin n) → ℝ) :
    (∑ w : Fin (k + 4) → Fin n, H w)
      = ∑ ι : Fin k → Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, ∑ m : Fin n,
          H (Fin.append ι ![i, j, l, m]) := by
  have h1 : (∑ w : Fin (k + 4) → Fin n, H w)
      = ∑ p : (Fin k → Fin n) × (((Fin n × Fin n) × Fin n) × Fin n),
          H (Fin.append p.1 ![p.2.1.1.1, p.2.1.1.2, p.2.1.2, p.2.2]) := by
    exact (Fintype.sum_equiv (splitEquiv k n) (fun p =>
      H (Fin.append p.1 ![p.2.1.1.1, p.2.1.1.2, p.2.1.2, p.2.2])) H (by intro p; rfl)).symm
  rw [h1]
  simp only [Fintype.sum_prod_type]

end Work.Diff.EXT

import Mathlib
import Submission.Work.Peluse.UControl.PetWinTower

/-!
# The tower weight `WinTower.nu` is a probability weight

`WinTower.nu H n a` is the product of the `n` window weights `μ_H` of the points of the tower
`a : WinTower H n` (see `PetWinTower`).  Here we show that it is nonnegative and that it sums to
`1`, i.e. that `ν` is a probability weight on the PET parameter tower.  The one step input is
`PetStep.sum_winVal_muL` (`∑_{k : Fin (2H+1)} μ_H (winVal H k) = 1`).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

/-- The tower weight of a point `(a, k)` of the `(n+1)`-st level: the weight at level `n` times the
weight `μ_H` of the new window position `k`. -/
lemma WinTower.nu_succ (H n : ℕ) (a : WinTower H n) (k : Fin (2 * H + 1)) :
    WinTower.nu H (n + 1) (a, k) = WinTower.nu H n a * Work.Peluse.muL H (PetStep.winVal H k) := by
  simp [WinTower.nu]

/-- Nonnegativity of the tower weight, by induction on the number of windows. -/
lemma WinTower.nu_nonneg (H : ℕ) : ∀ n, ∀ a : WinTower H n, 0 ≤ WinTower.nu H n a
  | 0, _ => by simp [WinTower.nu]
  | (n + 1), a => by
      obtain ⟨a, k⟩ := a
      rw [WinTower.nu_succ]
      exact mul_nonneg (WinTower.nu_nonneg H n a) (Work.Peluse.PET.pet_muL_nonneg H _)

/-- The tower weight is a probability weight: it sums to `1`. -/
lemma WinTower.sum_nu (H : ℕ) (hH : 1 ≤ H) :
    ∀ n, (∑ a : WinTower H n, WinTower.nu H n a) = 1
  | 0 => by
      have h : (∑ a : WinTower H 0, WinTower.nu H 0 a) = ∑ _ : Fin 1, (1 : ℝ) := rfl
      rw [h]; simp
  | (n + 1) => by
      -- Move the sum to the product type on which the recursion unfolds.
      have h1 : (∑ a : WinTower H (n + 1), WinTower.nu H (n + 1) a)
          = ∑ p : WinTower H n × Fin (2 * H + 1), WinTower.nu H (n + 1) p := rfl
      rw [h1]
      -- Rewrite the summand with the recursion, *before* splitting the product sum.
      have h2 : (∑ p : WinTower H n × Fin (2 * H + 1), WinTower.nu H (n + 1) p)
          = ∑ p : WinTower H n × Fin (2 * H + 1),
              WinTower.nu H n p.1 * Work.Peluse.muL H (PetStep.winVal H p.2) :=
        Finset.sum_congr rfl (fun p _ => by simp [WinTower.nu])
      rw [h2, Fintype.sum_prod_type]
      rw [Finset.sum_congr rfl (fun a _ => (Finset.mul_sum _ _ _).symm)]
      rw [Finset.sum_congr rfl (fun a _ => by rw [PetStep.sum_winVal_muL H hH, mul_one])]
      exact WinTower.sum_nu H hH n

theorem petWinTowerSumNu (H n : ℕ) (hH : 1 ≤ H) :
    (∀ a : Work.Peluse.UControl.WinTower H n, 0 ≤ Work.Peluse.UControl.WinTower.nu H n a) ∧
    (∑ a : Work.Peluse.UControl.WinTower H n, Work.Peluse.UControl.WinTower.nu H n a) = 1 :=
  ⟨WinTower.nu_nonneg H n, WinTower.sum_nu H hH n⟩

end Work.Peluse.UControl

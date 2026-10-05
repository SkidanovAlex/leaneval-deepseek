import Mathlib
import Submission.Work.RPCore.Chain.C4Defs

namespace Work.RPCore.Chain

theorem sum_ite_Wrot (m : ℕ) (c : Fin m → Prop) [DecidablePred c] (δ : ℝ)
    (q P : Fin m → ℝ × ℝ) :
    (∑ j : Fin m, (if c j then Work.RPV.Wrot δ (q j, P j) else 0))
      = (1 / Real.cos δ - 1) * (∑ j : Fin m, if c j then (q j).1 * (P j).1 else 0)
        - (Real.tan δ / 2) * (∑ j : Fin m, if c j then ((q j).1 ^ 2 + (P j).1 ^ 2) else 0)
        + δ * (∑ j : Fin m, if c j then (P j).2 else 0) := by
  -- `Wrot δ` is an affine (linear) function of `(x.1.1 * x.2.1, x.1.1 ^ 2 + x.2.1 ^ 2, x.2.2)`,
  -- and for each `j` the indicator `if c j then · else 0` commutes with that linear combination.
  have h : ∀ j : Fin m,
      (if c j then Work.RPV.Wrot δ (q j, P j) else 0)
        = (1 / Real.cos δ - 1) * (if c j then (q j).1 * (P j).1 else 0)
          - (Real.tan δ / 2) * (if c j then ((q j).1 ^ 2 + (P j).1 ^ 2) else 0)
          + δ * (if c j then (P j).2 else 0) := by
    intro j
    by_cases hc : c j <;> simp [Work.RPV.Wrot, hc, mul_assoc]
  rw [Finset.sum_congr rfl (fun j _ => h j)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]

end Work.RPCore.Chain

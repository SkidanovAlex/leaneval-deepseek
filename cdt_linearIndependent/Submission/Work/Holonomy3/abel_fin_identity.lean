import Mathlib

namespace Work.Holonomy3

/-- Abel summation by parts for the specific index pattern used in the holonomy bound:
writing `a k = (γ k)^2` (with `a 0 = 0`) and `b k = L k`,

`∑_{k=0}^{l} (a (k+1) - a k) b k = a (l+1) b l - ∑_{k=0}^{l-1} a (k+1) (b (k+1) - b k)`. -/
theorem abel_fin_identity {l : ℕ} (γ : Fin (l + 2) → ℝ) (hγ0 : γ 0 = 0) (L : Fin (l + 1) → ℝ) :
    ∑ k : Fin (l + 1), ((γ k.succ) ^ 2 - (γ k.castSucc) ^ 2) * L k
      = (γ (Fin.last (l + 1))) ^ 2 * L (Fin.last l)
        - ∑ k : Fin l, (γ k.succ.castSucc) ^ 2 * (L k.succ - L k.castSucc) := by
  have hpt : ∀ k : Fin (l + 1), ((γ k.succ) ^ 2 - (γ k.castSucc) ^ 2) * L k
      = (γ k.succ) ^ 2 * L k - (γ k.castSucc) ^ 2 * L k := fun k => by ring
  simp only [hpt]
  rw [Finset.sum_sub_distrib]
  rw [Fin.sum_univ_castSucc (f := fun k : Fin (l + 1) => (γ k.succ) ^ 2 * L k)]
  rw [Fin.sum_univ_succ (f := fun k : Fin (l + 1) => (γ k.castSucc) ^ 2 * L k)]
  have h0 : γ (((0 : Fin (l + 1)).castSucc)) ^ 2 * L 0 = 0 := by
    rw [Fin.castSucc_zero, hγ0]; ring
  rw [h0, zero_add]
  simp only [Fin.succ_castSucc, Fin.succ_last]
  have hC : ∑ k : Fin l, γ k.succ.castSucc ^ 2 * (L k.succ - L k.castSucc)
      = (∑ k : Fin l, γ k.succ.castSucc ^ 2 * L k.succ)
        - (∑ k : Fin l, γ k.succ.castSucc ^ 2 * L k.castSucc) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [hC]
  ring

end Work.Holonomy3

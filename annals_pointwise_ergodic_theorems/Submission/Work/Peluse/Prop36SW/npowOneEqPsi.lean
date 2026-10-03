import Mathlib
import Submission.Work.Peluse.TransferUp.boxNormPow_transfer_up

namespace Work.Peluse.Prop36SW

open scoped BigOperators

/-- At `t = 1` and `d = 1`, the normalised box-norm power `Npow 1` unwinds to the `ψ`-weighted
correlation sum: both sides equal `H⁻¹ ∑_x ‖∑_{n ≤ H} G (x + n)‖²`, the left through
`TransferUp.Npow_one_eq` (the level-one window identity) and the right through
`TransferUp.sum_psi_corr_eq`. -/
theorem npowOneEqPsi (S : Finset ℤ) (hS : 0 < S.card) (G : ℤ → ℂ)
    (hG : Work.Peluse.FinSuppZ G) (H : ℕ) :
    Work.Peluse.TransferUp.Npow 1 (fun _ : Fin 1 => (1 : ℤ)) S G H
      = ∑ e ∈ Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1),
          Work.Peluse.TransferUp.psi H e * (Work.Peluse.TransferUp.corr G e).re := by
  have h1 := Work.Peluse.TransferUp.Npow_one_eq (d := fun _ : Fin 1 => (1 : ℤ))
      (by norm_num) S G hG (H := H) hS
  have h2 := Work.Peluse.TransferUp.sum_psi_corr_eq (d := (1 : ℤ)) (H := H) (G := G) hG
  rw [h1, ← h2]
  simp only [one_mul]

end Work.Peluse.Prop36SW

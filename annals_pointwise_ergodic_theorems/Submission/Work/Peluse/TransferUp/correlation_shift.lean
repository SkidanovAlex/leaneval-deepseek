import Mathlib

namespace Work.Peluse.TransferUp

/-- The autocorrelation of a function `G : ℤ → ℂ` is invariant under shifting both arguments:
`∑_x G (x+a) * conj (G (x+b)) = ∑_x G x * conj (G (x + (b-a)))`.

This is the reindexing `x ↦ x + a` (an additive bijection of `ℤ`), which leaves the (possibly
non-summable) `tsum` unchanged because `tsum` is invariant under every equivalence of the index
type. -/
theorem correlation_shift (a b : ℤ) (G : ℤ → ℂ) :
    tsum (fun x : ℤ => G (x + a) * star (G (x + b)))
      = tsum (fun x : ℤ => G x * star (G (x + (b - a)))) := by
  rw [← Equiv.tsum_eq (Equiv.addRight a) (fun y : ℤ => G y * star (G (y + (b - a))))]
  apply tsum_congr
  intro x
  simp only [Equiv.coe_addRight]
  rw [show x + a + (b - a) = x + b by ring]

end Work.Peluse.TransferUp

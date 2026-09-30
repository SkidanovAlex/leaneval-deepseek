import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Rescaling every base of a vanishing exponential-polynomial identity by a fixed nonzero constant
`z a` preserves the identity: `∑ i ∈ s, z i^t Q i t = 0` implies
`∑ i ∈ s, (z i / z a)^t Q i t = 0` (divide through by `z a^t`). -/
theorem div_base_vanish {ι : Type*} (s : Finset ι) (z : ι → ℂ) (Q : ι → Polynomial ℂ) (a : ι)
    (hza : z a ≠ 0)
    (h : ∀ t : ℕ, ∑ i ∈ s, z i ^ t * (Q i).eval (t : ℂ) = 0) :
    ∀ t : ℕ, ∑ i ∈ s, (z i / z a) ^ t * (Q i).eval (t : ℂ) = 0 := by
  intro t
  have key : ∀ i ∈ s, (z i / z a) ^ t * (Q i).eval (t : ℂ)
      = (z i ^ t * (Q i).eval (t : ℂ)) / (z a) ^ t := by
    intro i _
    rw [div_pow]
    ring
  calc ∑ i ∈ s, (z i / z a) ^ t * (Q i).eval (t : ℂ)
      = ∑ i ∈ s, (z i ^ t * (Q i).eval (t : ℂ)) / (z a) ^ t := Finset.sum_congr rfl key
    _ = (∑ i ∈ s, z i ^ t * (Q i).eval (t : ℂ)) / (z a) ^ t := (Finset.sum_div s _ _).symm
    _ = 0 := by rw [h t, zero_div]

end Work.BW

import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.VfdDefs

/-!
# The near-diagonal counting kernel of the variance

For the near-diagonal part of the "flipping of moduli" estimate (FI §12) one has to bound the
bilinear form

`Σ_{p,q ∈ boxF} α_p conj(α_q) (1 - nearCut a b (xPair p q)) · pairWeight D p q`

by a counting kernel: the factor `(1 - nearCut a b (xPair p q))` is supported where the *difference
ratio* `xPair p q = s₁/r₁ - s₂/r₂` is small, and there the integer difference
`Δ_{pq} = r₁ s₂ - r₂ s₁` satisfies `|Δ_{pq}| H ≤ 8RS`; the weight `pairWeight` is then bounded by
the number of divisors of `Δ_{pq}` in the window `(D/2, 3D]`.

This module provides the two local notions (`nearDelta`, `nearKernel`) so that the pieces can be
stated and proved independently.
-/

namespace Work.FIArea4.Vflip.Vfd

noncomputable section

/-- The integer difference `Δ_{pq} = r₁ s₂ - r₂ s₁` attached to a pair of points
`p = (r₁,s₁)`, `q = (r₂,s₂)` (the quantity whose divisors occur after the flip of moduli). -/
def nearDelta (p q : ℕ × ℕ) : ℤ := (p.1 : ℤ) * (q.2 : ℤ) - (q.1 : ℤ) * (p.2 : ℤ)

/-- The near-diagonal counting kernel: the indicator of the near condition
`|Δ_{pq}|·H ≤ 8RS`, multiplied by the number of divisors of `Δ_{pq}` in the window `(D/2, 3D]`. -/
def nearKernel (D R S : ℕ) (H : ℝ) (p q : ℕ × ℕ) : ℝ :=
  if ((nearDelta p q).natAbs : ℝ) * H ≤ 8 * (R : ℝ) * (S : ℝ) then
    (((Finset.Ioc (D / 2) (3 * D)).filter (fun d => d ∣ (nearDelta p q).natAbs)).card : ℝ)
  else 0

lemma nearKernel_nonneg (D R S : ℕ) (H : ℝ) (p q : ℕ × ℕ) :
    0 ≤ nearKernel D R S H p q := by
  unfold nearKernel
  split
  · positivity
  · exact le_refl 0

lemma nearDelta_swap (p q : ℕ × ℕ) : nearDelta q p = - nearDelta p q := by
  unfold nearDelta; ring

lemma nearKernel_symm (D R S : ℕ) (H : ℝ) (p q : ℕ × ℕ) :
    nearKernel D R S H p q = nearKernel D R S H q p := by
  unfold nearKernel
  rw [nearDelta_swap, Int.natAbs_neg]

end

end Work.FIArea4.Vflip.Vfd

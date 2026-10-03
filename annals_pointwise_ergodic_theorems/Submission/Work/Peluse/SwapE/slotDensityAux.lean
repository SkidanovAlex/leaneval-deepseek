import Mathlib
import Submission.Work.Peluse.SwapE.Defs

/-!
# `SwapE` — auxiliary vocabulary for the slot-density lemma (`SlotDensity`, KKL Cor. 7.2 at `ℓ = 2`)

The slot count `SlotDensity.slotCount q₁ q₂ M n` has two natural parametrisations:

* the *slot points* `Fin M × Fin M`, whose slot value is `pdir q₁ q₂ m = q₁(m₁+1) - q₂(m₂+1)`;
* the *difference variables* `X = (m₁+1) - (m₁'+1)`, `Y = (m₂+1) - (m₂'+1)`, which lie in
  `[-(M-1), M-1]²` and satisfy the linear equation `q₁ X - q₂ Y = n`.

This module names the second one: `diffBox K` is the difference box `[-K,K]²`,
`slotDiffSet q₁ q₂ K n` its intersection with the hyperplane `q₁ X - q₂ Y = n`, and
`slotDiffCount` the cardinality.  The two counting lemmas about it (`slotCount_le` in
`SwapE/slotCountBound.lean`, `slotDiffCount_le` in `SwapE/slotDiffCountBound.lean`) are the two
halves of the density estimate; the main file assembles them.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapE

noncomputable section

/-- The difference box `[−K, K]² ⊆ ℤ²`. -/
def diffBox (K : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(K : ℤ)) (K : ℤ) ×ˢ Finset.Icc (-(K : ℤ)) (K : ℤ)

/-- The solutions of `q₁ X − q₂ Y = n` with `|X| ≤ K` and `|Y| ≤ K`. -/
def slotDiffSet (q₁ q₂ : ℤ) (K : ℕ) (n : ℤ) : Finset (ℤ × ℤ) :=
  (diffBox K).filter (fun p => q₁ * p.1 - q₂ * p.2 = n)

/-- The number of solutions of `q₁ X − q₂ Y = n` in the difference box `[−K,K]²`. -/
def slotDiffCount (q₁ q₂ : ℤ) (K : ℕ) (n : ℤ) : ℕ := (slotDiffSet q₁ q₂ K n).card

/-- `q₁ / gcd(q₁, q₂)`: the first coordinate of the *primitive* direction of the slot equation
`q₁ X − q₂ Y = n`.  Writing `g = gcd(q₁,q₂)`, `a = slotA q₁ q₂`, `b = slotB q₁ q₂`, one has
`q₁ = a g`, `q₂ = b g` and `gcd(a,b) = 1`. -/
def slotA (q₁ q₂ : ℤ) : ℤ := q₁ / (Int.gcd q₁ q₂ : ℤ)

/-- `q₂ / gcd(q₁, q₂)`: the second coordinate of the primitive direction. -/
def slotB (q₁ q₂ : ℤ) : ℤ := q₂ / (Int.gcd q₁ q₂ : ℤ)

/-- Membership in the difference box. -/
@[simp] theorem mem_diffBox {K : ℕ} {p : ℤ × ℤ} :
    p ∈ diffBox K ↔ p.1 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) ∧
      p.2 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
  simp [diffBox]

/-- Membership in the solution set: the two coordinates lie in `[−K,K]` and the linear equation
holds. -/
@[simp] theorem mem_slotDiffSet {q₁ q₂ : ℤ} {K : ℕ} {n : ℤ} {p : ℤ × ℤ} :
    p ∈ slotDiffSet q₁ q₂ K n ↔
      p.1 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) ∧ p.2 ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) ∧
        q₁ * p.1 - q₂ * p.2 = n := by
  simp only [slotDiffSet, diffBox, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

end

end Work.Peluse.SwapE

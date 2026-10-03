/-
# Vocabulary for the two hard pieces of the `g`-side low-pass variational estimate

This file defines the partial-sum maximal function of the annuli of the low-pass
Ionescu--Wainger family, the quantity that the Men'shov/lacunary-maximal piece bounds.
-/
import Mathlib
import Submission.Work.KMTAreas.A7Hi.LowpassDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7HiRep

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- The partial-sum maximal function of the annuli `Δ_k = T_{k+1} - T_k` of the low-pass
Ionescu--Wainger family `T_k = lpf ρ l₁ m₀ k f = kmtProj ρ l₁ (-(m₀+k)) f`:
`partMaxD ρ l₁ m₀ f x = ⨆_K ‖∑_{k<K} Δ_k f x‖ₑ`. -/
noncomputable def partMaxD (ρ : ℝ) (l₁ m₀ : ℕ) (f : ℤ → ℂ) : ℤ → ℝ≥0∞ :=
  fun x => ⨆ K : ℕ, ‖(∑ i ∈ Finset.range K,
      (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (i + 1) f x
        - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ i f x))‖ₑ

end Work.KMTAreas.A7HiRep

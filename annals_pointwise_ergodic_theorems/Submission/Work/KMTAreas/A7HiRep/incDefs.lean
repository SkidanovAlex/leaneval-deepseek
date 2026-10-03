import Mathlib
import Submission.Work.KMTAreas.A7Hi.LowpassDefs

/-!
# Vocabulary for the increment of the Ionescu--Wainger low-pass family

* `Work.KMTAreas.A7HiRep.incArc ρ l k` — the union of the major arcs `α + realArc k` over the
  Ionescu--Wainger arithmetic frequency set `α ∈ (ℚ/ℤ)_{≤l}`;
* `Work.KMTAreas.A7HiRep.incFam ρ l₁ m₀ m f` — the increment `lpf (m+1) f − lpf m f` of the
  low-pass family of `Work.KMTAreas.A7Hi`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7HiRep

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- The union of the major arcs `α + realArc k`, `α ∈ (ℚ/ℤ)_{≤l}`, as a subset of the circle. -/
def incArc (ρ : ℝ) (l : ℕ) (k : ℤ) : Set Work.Analysis.IonescuWainger.Circle :=
  {ξ | ∃ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
    ∃ θ ∈ Work.Analysis.IonescuWainger.realArc k, ξ = α + (θ : _)}

/-- The increment `Δ_m f = T_{m+1} f − T_m f` of the low-pass family. -/
noncomputable def incFam (ρ : ℝ) (l₁ m₀ m : ℕ) (f : ℤ → ℂ) : ℤ → ℂ :=
  fun x => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (m + 1) f x
    - Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x

end Work.KMTAreas.A7HiRep

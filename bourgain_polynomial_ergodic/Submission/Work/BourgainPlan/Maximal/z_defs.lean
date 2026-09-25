import Mathlib
import Submission.BourgainPlan.Interfaces
import Submission.Work.BourgainPlan.Maximal.foundations

/-!
# The `ℤ`-form of the discrete maximal inequality

The circle method is naturally carried out on `ℤ` (Fourier coefficients of a
finitely supported function, the torus, the Weyl kernel
`N⁻¹ ∑_{i<N} e(θ P(i))`).  This file records the `ℤ`-form of the maximal
inequality and the (purely measure-theoretic) transfer `ℤ ⟹ ℕ` that turns it
into `Submission.BourgainPlan.MaximalStatement`.
-/

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Submission.BourgainPlan (NonnegOnNat)

/-- The polynomial average on `ℤ`: `N⁻¹ ∑_{i<N} g (m + P i)`. -/
noncomputable def discAvgZ (P : Polynomial ℤ) (N : ℕ) (g : ℤ → ℝ) (m : ℤ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i ∈ Finset.range N, g (m + (((P.eval (i : ℤ)).toNat : ℕ) : ℤ))

/-- The maximal function of the polynomial averages on `ℤ`. -/
noncomputable def maxFZ (P : Polynomial ℤ) (g : ℤ → ℝ) (m : ℤ) : ℝ≥0∞ :=
  ⨆ N : ℕ, ‖discAvgZ P N g m‖ₑ

/-- **The `ℤ`-form of Bourgain's maximal inequality**: the same inequality as
`Submission.BourgainPlan.MaximalStatement`, but for `ℤ`-valued functions and with the `ℤ`-maximal
function. -/
def MaximalStatementZ : Prop :=
  ∀ P : Polynomial ℤ, NonnegOnNat P → ∀ p : ℝ, 1 < p → ∃ C : ℝ, 0 ≤ C ∧
    ∀ g : ℤ → ℝ, (∃ s : Finset ℤ, ∀ n, n ∉ s → g n = 0) →
      ∫⁻ m : ℤ, (maxFZ P g m) ^ p ∂Measure.count
        ≤ ENNReal.ofReal (C ^ p) * ∫⁻ m : ℤ, ‖g m‖ₑ ^ p ∂Measure.count

end Work.BourgainPlan.Maximal

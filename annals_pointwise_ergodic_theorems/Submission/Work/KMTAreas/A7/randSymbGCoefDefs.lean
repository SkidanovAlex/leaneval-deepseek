/-
# The telescoping coefficients of the `g`-side randomised symbol

The `g`-side randomised cut-off of the area-`A7` small-scale assembly is

  `randSymb (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K
     = ∑_{n < K} ε n • (smallSymbG … (n+1) - smallSymbG … n)`,

a randomised *telescoping* sum of the modulated `g`-side bumps at the lacunary scales `⌊a n⌋`.
Telescoping the sum gives the equivalent form

  `randSymb (smallSymbG …) ε K = ∑_{m ≤ K} c m • φ̃_{N_m,t}`,

where `c m = (1_{1 ≤ m ≤ K} ε (m-1) - 1_{m < K} ε m) · 1_{randAct m}` is the coefficient defined
below.  Its two relevant properties are

* `‖c m‖ ≤ 2`, and
* the partial sums `∑_{m ∈ Icc u v} c m` are bounded by `4` — this is the "telescoping" property
  which (in contrast with arbitrary bounded coefficients) makes the symbol's Mikhlin constant
  independent of the number of scales `K`; it is used by
  `Work.KMTAreas.A7.randSymbG_mikhlin`.

The decidable predicate `randAct` (the "active" indices of `smallSymbG`: `m ≠ 0` and
`smallCond`) has an *interval* level set whenever `a` is monotone
(`Work.KMTAreas.A7.randAct_interval`), which is what turns the partial-sum bound for the raw
telescoping coefficients into the partial-sum bound for `randSymbGCoef`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.randSymbDefs

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar

/-- **The telescoping coefficient** of `φ m` in the identity
`randSymb φ ε K = ∑_{m ≤ K} c m • φ m` for an arbitrary family `φ`:
`c m = 1_{1 ≤ m ≤ K} ε (m-1) - 1_{m < K} ε m`. -/
def teleCoef (ε : ℕ → ℂ) (K m : ℕ) : ℂ :=
  (if 1 ≤ m ∧ m ≤ K then ε (m - 1) else 0) - (if m < K then ε m else 0)

/-- **The coefficient of the `g`-side telescoped symbol**: the telescoping coefficient, restricted
to the *active* indices of the small-scale condition. -/
noncomputable def randSymbGCoef (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ)
    (ε : ℕ → ℂ) (K m : ℕ) : ℂ :=
  if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then teleCoef ε K m else 0

/-- The `g`-side bump family, index by index: it is the bump `φ̃_{N_m,t}` on the active indices
(and at `m ≠ 0`) and `0` otherwise. -/
theorem smallSymbG_apply (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (m : ℕ) :
    smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t m =
      (if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then
        varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t else 0) := by
  funext ξ
  unfold smallSymbG randAct
  by_cases h0 : m = 0
  · subst h0; simp
  · by_cases hc : smallCond ρ C₀ a l₁ l₂ k₁ k₂ m <;> simp [h0, hc]

end

end Work.KMTAreas.A7

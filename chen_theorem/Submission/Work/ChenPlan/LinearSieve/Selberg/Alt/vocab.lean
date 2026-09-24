import Mathlib

/-!
# Vocabulary for the sharp `G`-bound (exponential partial sums)

The extremal configuration for `gSum · Vf ≥ s/(2e^γ)` is the "infinitely finely saturated"
measure; the reference random variable is `Σ_{k≥1} e^{-S_k}` where `S_k` are the partial sums of
iid standard exponentials (`S_k` are the points of a unit-rate Poisson process).
-/

open MeasureTheory

set_option autoImplicit false

namespace Work.ChenPlan.LinearSieve.Selberg.Alt

open scoped ENNReal

/-- `IsStdExp X P`: `X` has the standard exponential law under `P`, described by its CDF. -/
def IsStdExp {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ x : ℝ, P {ω | X ω ≤ x} = ENNReal.ofReal (1 - Real.exp (-x))

/-- Partial sums of a sequence. -/
def partialSum (E : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i ∈ Finset.range k, E i

/-- The extremal reference variable `Y = Σ_{k ≥ 1} e^{-S_k}` (`k ≥ 1`: the `k = 0` term is
excluded, so `Y ≤ 1` is not forced). -/
noncomputable def refSum (E : ℕ → ℝ) : ℝ := ∑' k : ℕ, Real.exp (- partialSum E (k + 1))

/-- The intervals `(a j, b j]` are pairwise disjoint. -/
def PairwiseDisjointIoc {n : ℕ} (a b : Fin n → ℝ) : Prop :=
  ∀ j j', j ≠ j' → Disjoint (Set.Ioc (a j) (b j)) (Set.Ioc (a j') (b j'))

/-- The event that `refSum E < θ`. -/
def refSumLt {Ω : Type*} (E : ℕ → Ω → ℝ) (θ : ℝ) : Set Ω :=
  {ω | refSum (fun i => E i ω) < θ}

/-- The event that some partial sum `S_k` lies in the interval `(a, b]`. -/
def IntervalHit {Ω : Type*} (E : ℕ → Ω → ℝ) (a b : ℝ) : Set Ω :=
  {ω | ∃ k, partialSum (fun i => E i ω) k ∈ Set.Ioc a b}

/-- The event that each of `n` intervals `(a j, b j]` contains some partial sum. -/
def AllIntervalHits {Ω : Type*} {n : ℕ} (E : ℕ → Ω → ℝ) (a b : Fin n → ℝ) : Set Ω :=
  {ω | ∀ j, ω ∈ IntervalHit E (a j) (b j)}

end Work.ChenPlan.LinearSieve.Selberg.Alt

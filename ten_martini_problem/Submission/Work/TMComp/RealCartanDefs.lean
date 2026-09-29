import Mathlib
import Submission.Work.TMContract.Components

/-!
# Component C10 (`P_RealCartan`): shared vocabulary

This file fixes the vocabulary used by the proof of `Work.TMContract.P_RealCartan`
(the "real-line Cartan lemma" of Avila--Jitomirskaya, Ten Martini Problem, §2.4 replacement).

The statement is: for `U ⊆ ℂ` open, `f k` holomorphic on `U`, `w k, s k > 0`, with a
locally uniform bound `‖f k z‖ ≤ w k * exp (M * s k)` on compacts, the set

`A = {x : ℝ | (x:ℂ) ∈ U ∧ ∃ η > 0, ∀ᶠ k, ‖f k x‖ ≤ w k * exp (-(η * s k))}`

is either Lebesgue-null or contains an open interval.

The proof is the barrier/Cartan argument: if `A` has positive measure, a density point `x₀`
of a closed piece `B` of `A` of positive measure is chosen, and the logarithmic potential of
`B` is used as a harmonic barrier.  The ingredients are:
* `logPot`, `pot`: the logarithmic potential of a set `B ⊆ ℝ` at scale `R`;
* `Aη`, `Amn`: the two descriptions of the "good" set;
* `barrier`: the harmonic comparison function.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace Work.TMComp.RC

/-- The (unnormalised) logarithmic potential of `B ⊆ ℝ` at scale `R`, evaluated at `z : ℂ`:
`∫_{t ∈ B} log (R / ‖z - t‖) dt`. -/
noncomputable def logPot (B : Set ℝ) (R : ℝ) (z : ℂ) : ℝ :=
  ∫ t in B, Real.log (R / ‖z - (t : ℂ)‖)

/-- The logarithmic potential of `B ⊆ ℝ` normalised by the measure of `B`. -/
noncomputable def pot (B : Set ℝ) (R : ℝ) (z : ℂ) : ℝ :=
  (volume B).toReal⁻¹ * logPot B R z

/-- The "good set" of the Cartan lemma, with the exponential rate `η` fixed. -/
def Aη (U : Set ℂ) (f : ℕ → ℂ → ℂ) (w s : ℕ → ℝ) (η : ℝ) : Set ℝ :=
  {x : ℝ | (x : ℂ) ∈ U ∧ ∀ᶠ k in atTop, ‖f k x‖ ≤ w k * Real.exp (-(η * s k))}

/-- The closed pieces whose union is the good set: `η = 1/(m+1)` and the "eventually" made
explicit at the index `n`. -/
def Amn (U : Set ℂ) (f : ℕ → ℂ → ℂ) (w s : ℕ → ℝ) (m n : ℕ) : Set ℝ :=
  {x : ℝ | (x : ℂ) ∈ U ∧ ∀ k ≥ n, ‖f k x‖ ≤ w k * Real.exp (-(s k / (m + 1)))}


/-- The good set of the Cartan lemma, in the exact form of the frozen statement. -/
def Aall (U : Set ℂ) (f : ℕ → ℂ → ℂ) (w s : ℕ → ℝ) : Set ℝ :=
  {x : ℝ | (x : ℂ) ∈ U ∧ ∃ η : ℝ, 0 < η ∧ ∀ᶠ k in atTop, ‖f k x‖ ≤ w k * Real.exp (-(η * s k))}


/-- The boundary normalisation of the logarithmic potential: an upper bound for
`pot B R z` valid on the circle `‖z - x₀‖ = R`. -/
noncomputable def cc (R ρ : ℝ) : ℝ := Real.log (R / (R - ρ))

/-- The interior normalisation of the logarithmic potential: an upper bound for `pot B R z`
valid on the whole disc, given `volume B ≥ (1 - τ) * 2 * ρ`. -/
noncomputable def CC (R ρ τ : ℝ) : ℝ := Real.log R + (1 / (1 - τ)) * (Real.log (1 / ρ) + 1)

/-- The harmonic barrier used in the comparison (maximum) principle:
`M - (M + ε) * ((Φ z - c)/(C - c))`, where `Φ` is the logarithmic potential of the "bad"
set `B`, `M` is the a priori local bound, `ε` the required rate and `c`, `C` the boundary
and interior normalisations of `Φ`. -/
noncomputable def barrier (Φ : ℂ → ℝ) (M ε c C : ℝ) (z : ℂ) : ℝ :=
  M - (M + ε) * ((Φ z - c) / (C - c))

end Work.TMComp.RC

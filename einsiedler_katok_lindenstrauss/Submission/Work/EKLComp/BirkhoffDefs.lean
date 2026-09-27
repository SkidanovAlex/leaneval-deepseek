/-
Helper definitions for component C11c (Birkhoff pointwise ergodic theorem).

The Birkhoff theorem is proved here from scratch (Mathlib has the Birkhoff *sum*
`birkhoffSum` but no pointwise ergodic theorem).  The proof follows the classical
route: reduce to the case where the conditional expectation of `f` w.r.t. the
invariant σ-algebra vanishes, and apply the Hopf maximal ergodic inequality to
the function `(g - ε) · 1_U`, where `U` is the (invariant) set of points where the
Birkhoff averages of `g` frequently exceed `ε` by a rational margin.

The "bad set" is deliberately phrased with `∃ᶠ ... q < birkA ...` for rational `q`
rather than with `limsup`: this makes the set exactly `T`-invariant (the `q`
absorbs the `n/(n+1)` slop coming from the shift identity), and it is counting
`U = {x | ∃ q ∈ ℚ, ε < q ∧ ∃ᶠ n, q < birkA n x}` which avoids all the junk-value
issues of `Filter.limsup` in a conditionally complete linear order.
-/
import Mathlib

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Work.EKLComp.Birkhoff

/-- The Birkhoff average of `f` along the orbit of `x` under `T`,
`n⁻¹ ∑_{k<n} f (T^[k] x)`. -/
def birkA {X : Type*} (T : X → X) (f : X → ℝ) (n : ℕ) (x : X) : ℝ :=
  (n : ℝ)⁻¹ * birkhoffSum T f n x

@[simp]
theorem birkA_def {X : Type*} (T : X → X) (f : X → ℝ) (n : ℕ) (x : X) :
    birkA T f n x = (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, f (T^[k] x) := rfl

/-- The maximal Birkhoff sum `max_{0 ≤ k ≤ n} ∑_{j<k} f (T^[j] x)`. -/
def maxBirkSum {X : Type*} (T : X → X) (f : X → ℝ) (n : ℕ) (x : X) : ℝ :=
  (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos n)⟩
    (fun k => birkhoffSum T f k x)

/-- The set of points where the Birkhoff averages of `f` frequently exceed `ε` by a
rational margin.  This set is exactly `T`-invariant (see `preimage_badSet`). -/
def badSet {X : Type*} (T : X → X) (f : X → ℝ) (ε : ℝ) : Set X :=
  {x | ∃ q : ℚ, ε < (q : ℝ) ∧ ∃ᶠ n in atTop, (q : ℝ) < birkA T f n x}

/-- The set of points where some Birkhoff sum of `f` is positive.  This is the set
occurring in the conclusion of the Hopf maximal ergodic inequality. -/
def posSumSet {X : Type*} (T : X → X) (f : X → ℝ) : Set X :=
  {x | ∃ n : ℕ, 0 < birkhoffSum T f n x}

end Work.EKLComp.Birkhoff

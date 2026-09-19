import Mathlib
import Submission.LocalFactorComparison

open scoped BigOperators
open MeasureTheory

noncomputable section

/-!
# The Maynard--Polymath variational functionals

Definitions of the functionals used in the Maynard sieve (Maynard 2015,
Prop. 4.1/4.2; Polymath8a 2014, Theorem 3.8/3.12): for `F` a real function on
`[0,∞)^k` (represented as a function `Fin k → ℝ`),

  * `IFunc k F := ∫_{R^k} F(t)² dt` where `R^k = {t ≥ 0 : Σ_i t_i ≤ 1}`,
  * `JFunc k c i F := ∫_{c·R^{k-1}} (∫₀^∞ F dt_i)² dt_≠i`,
  * `MkEps k ε` the supremum of `(Σ_i J_i)/I` over square-integrable `F`
    supported on `(1+ε)·R^k`.

These are pure real-analysis objects (no number theory); the sieve theorems
convert them into the `α`, `β_i` coefficients of the DHL criterion of
`Submission/DHLCriterion.lean`.
-/

namespace Commons.NumberTheory.MaynardSieve

/-- The scaled simplex `c · R^k := {t ∈ [0,∞)^k : Σ_i t_i ≤ c}` as a set of
functions `Fin k → ℝ`. -/
def simplexSet (k : ℕ) (c : ℝ) : Set (Fin k → ℝ) :=
  {t | (∀ i : Fin k, 0 ≤ t i) ∧ (∑ i : Fin k, t i) ≤ c}

/-- The indicator of the scaled simplex, as a real-valued function. -/
noncomputable def simplexIndicator (k : ℕ) (c : ℝ) : (Fin k → ℝ) → ℝ := by
  classical
  exact fun t => if t ∈ simplexSet k c then 1 else 0

/-- The `I_k(F) := ∫_{R^k} F(t)² dt` functional (Polymath8a Theorem 3.8/3.12,
Maynard Prop. 4.1).  All integrals below are Lebesgue integrals over the
corresponding Euclidean spaces. -/
def IFunc (k : ℕ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  ∫ t : Fin k → ℝ, (F t) ^ 2 * simplexIndicator k 1 t

/-- Extend a function on the coordinates other than `i` by the value `x` at
coordinate `i`, giving a function on all `k` coordinates. -/
def extendAt {k : ℕ} (i : Fin k) (x : ℝ) (t' : {j : Fin k // j ≠ i} → ℝ) : Fin k → ℝ :=
  fun j => if h : j = i then x else t' ⟨j, h⟩

/-- The marginal simplex condition on the coordinates other than `i`:
`t' ≥ 0` and `Σ_{j ≠ i} t' j ≤ c`, encoded on the domain `{j // j ≠ i}`. -/
def marginalSet (k : ℕ) (i : Fin k) (c : ℝ) : Set ({j : Fin k // j ≠ i} → ℝ) :=
  {t' | (∀ j : {j : Fin k // j ≠ i}, 0 ≤ t' j) ∧ (∑ j : {j : Fin k // j ≠ i}, t' j) ≤ c}

/-- `J_i(F; c) := ∫_{t' ∈ c·R^{k-1}} (∫_{ℝ} F(extendAt i x t') dx)² dt'`,
the `J_{i,c}(F)` of Polymath8a Theorem 3.12 (with `c = 1 - ε`) / Maynard's
`J_k^(i)(F)` (with `c = 1`). -/
noncomputable def JFunc (k : ℕ) (i : Fin k) (c : ℝ) (F : (Fin k → ℝ) → ℝ) : ℝ := by
  classical
  exact ∫ t' : ({j : Fin k // j ≠ i} → ℝ),
    (∫ x : ℝ, F (extendAt i x t')) ^ 2 *
      (if t' ∈ marginalSet k i c then 1 else 0)

/-- `I(F) := ∫_{[0,∞)^k} F(t)² dt`, the orthant integral of Polymath8a (31)
(for `F` vanishing outside `(1+ε)·R^k` this is the integral over that simplex). -/
noncomputable def IFuncOrth (k : ℕ) (F : (Fin k → ℝ) → ℝ) : ℝ :=
  ∫ t : Fin k → ℝ, (F t) ^ 2

/-- `M_{k,ε} := sup { Σ_i J_{i,1-ε}(F) / I(F) }` over functions `F` supported on
the enlarged simplex `(1+ε)·R^k` with `I(F) > 0`; as a `sSup` of reals.
(Defined for reference; concrete lower bounds in applications are obtained from
explicit `F`.)  Note that the `I`-integral is the orthant integral Polymath8a
(31), not the integral over the unit simplex. -/
def MkEps (k : ℕ) (ε : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ F : (Fin k → ℝ) → ℝ,
    (∀ t, t ∉ simplexSet k (1 + ε) → F t = 0) ∧
    0 < IFuncOrth k F ∧
    r < (∑ i : Fin k, JFunc k i (1 - ε) F) / IFuncOrth k F}

/-- `M_k := M_{k,0}` (Maynard's constant on the plain simplex). -/
def Mk (k : ℕ) : ℝ := MkEps k 0

end Commons.NumberTheory.MaynardSieve

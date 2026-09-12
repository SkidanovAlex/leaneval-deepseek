import Mathlib.Algebra.Polynomial.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Polynomial

/-!
# Minkowski black box — statements (Smith `prop:Mink`, GON.tex)

Shared *statement* module for the two consequences of Minkowski's theorems on
successive minima used by the squarefree-polynomial chain (contract 1):

* `minkUpper` — existence of many linearly independent integer polynomials
  with small evaluation product (Hilbert lemma; needs the UPPER bound of
  Minkowski's second theorem).
* `minkLower` — any linearly independent family has evaluation product not too
  small (squeeze lemma; elementary cross-polytope volume proof).

Indexing convention: `d ≥ 2` evaluation points `α : Fin d → ℝ` (distinct) and
positive weights `v : Fin d → ℝ`.  We look for `d` linearly independent integer
polynomials `Q i` (i : Fin d) of degree `≤ d−1`.  For each `i`, the *gauge* is
`μ_i := max_k v_k·|Q_i(α_k)|`; the statements are phrased with arbitrary upper
bounds `mu : Fin d → ℝ` (`∀ i k, v k * |Q i at α k| ≤ mu i`) so that the
conclusions read `∏ mu ≤ poly·D` (upper) resp. `D ≤ poly·∏ mu` (lower), where

    D = (∏_k v k) · (∏_{i<j} |α_i − α_j|).

Both allow a polynomial slack `(d : ℝ)^(C·(d : ℝ))` for a fixed constant
`C > 0` (chosen by the prover; any fixed C works — the downstream chains
absorb factors `d^{O(d)}`).
-/

noncomputable section

open Polynomial
open scoped Real BigOperators

namespace Submission.MinkBox

/-- The ℚ-coefficient vector of length `d` of an integer polynomial (degrees
`0..d−1`). -/
def coeffVec (d : ℕ) (Q : Polynomial ℤ) : Fin d → ℚ :=
  fun j => (Q.coeff j.val : ℚ)

/-- Linear independence over ℚ of a family of integer polynomials, via their
length-`d` coefficient vectors. -/
def LinIndepInt (d : ℕ) (Q : Fin d → Polynomial ℤ) : Prop :=
  LinearIndependent ℚ (fun i : Fin d => coeffVec d (Q i))

/-- The evaluation at a real point of an integer polynomial (over ℝ). -/
def evalInt (Q : Polynomial ℤ) (x : ℝ) : ℝ :=
  (Q.map (algebraMap ℤ ℝ)).eval x

/-- `∏_{i<j} |α_i − α_j|` over `Fin d`. -/
def pairProd (d : ℕ) (α : Fin d → ℝ) : ℝ :=
  ∏ i : Fin d, ∏ j ∈ (Finset.univ.filter (fun j : Fin d => i < j)), |α i - α j|

/-- The Minkowski determinant `D = (∏_k v k)·(∏_{i<j}|α_i−α_j|)`. -/
def Dval (d : ℕ) (α : Fin d → ℝ) (v : Fin d → ℝ) : ℝ :=
  (∏ k : Fin d, v k) * pairProd d α

/-- **Upper bound** (existence; Smith prop:Mink upper half, slack allowed):
there are `d` ℚ-linearly-independent integer polynomials `Q i` of degree
`≤ d−1` and bounds `mu i` on their weighted evaluations whose product is
`≤ (d:ℝ)^(C·d) · D`. -/
def minkUpper : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ), 2 ≤ d →
    ∀ (α : Fin d → ℝ), Function.Injective α →
    ∀ (v : Fin d → ℝ), (∀ k, 0 < v k) →
      ∃ (Q : Fin d → Polynomial ℤ),
        LinIndepInt d Q ∧ (∀ i, (Q i).natDegree ≤ d - 1) ∧
        ∃ (mu : Fin d → ℝ),
          (∀ i k, v k * |evalInt (Q i) (α k)| ≤ mu i) ∧
          (∏ i : Fin d, mu i) ≤ (d : ℝ) ^ (C * (d : ℝ)) * Dval d α v

/-- **Lower bound** (universal; Smith prop:Mink lower half with slack):
for any `d` ℚ-linearly-independent integer polynomials `Q i` of degree
`≤ d−1` and any bounds `mu i` on their weighted evaluations,
`D ≤ (d:ℝ)^(C·d) · ∏ mu`. -/
def minkLower : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ), 2 ≤ d →
    ∀ (α : Fin d → ℝ), Function.Injective α →
    ∀ (v : Fin d → ℝ), (∀ k, 0 < v k) →
    ∀ (Q : Fin d → Polynomial ℤ),
      LinIndepInt d Q → (∀ i, (Q i).natDegree ≤ d - 1) →
    ∀ (mu : Fin d → ℝ),
      (∀ i k, v k * |evalInt (Q i) (α k)| ≤ mu i) →
      Dval d α v ≤ (d : ℝ) ^ (C * (d : ℝ)) * (∏ i : Fin d, mu i)

end Submission.MinkBox

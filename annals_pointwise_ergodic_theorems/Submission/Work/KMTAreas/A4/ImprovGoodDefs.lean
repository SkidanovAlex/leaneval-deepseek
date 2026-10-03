/-
# The good-major-arc form of Theorem `improv` (A4)

Krause--Mirek--Tao prove §5 (Theorem `improv`, the single scale minor arc estimate) in the regime
of *good major arcs*: after reducing to the case `Log N ≥ C_ρ 2^{ρl}` ("(2l)" in the paper), the
estimate carries the single gain `2^{-cl}`, and the general case follows by monotonicity of the
projection in `(l,k)`: one applies the good-arc estimate at the largest `l' ≤ l` for which
`(l', l' - Log N)` has good major arcs, and the resulting gain `2^{-cl'}` is `≲_ρ (Log N)^{-c/ρ}`.

This module fixes that intermediate statement as a predicate, so that the §5 development can aim
at it, and so that the (purely bookkeeping) reduction to `ImprovKMT` can be delegated/proved
separately.
-/
import Mathlib
import Submission.Work.KMTContract.Areas

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A4

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems

open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier
open Work.Analysis.EndVar
open Work.KMTContract

/-- **The good-major-arc form of `improv`** (§5, Theorem `improv` in the regime in which the paper
proves it).  There is a rate `c > 0` **independent of `ρ`** such that for every `ρ ∈ (0,1]` there
are `Cρ > 0` and a constant `C` with

`‖Ã_N(f,g)‖_{ℓ¹(ℤ)} ≤ C · 2^{-cl} · ‖f‖_{ℓ²} ‖g‖_{ℓ²}`

for all `N ≥ 1`, `l ∈ ℕ` and `f, g ∈ ℓ²(ℤ)` such that

* the pair `(l, l - Log N)` has **good major arcs** (constant `Cρ`), and
* `Π_{≤l, ≤ -Log N + l} f = 0` or `Π_{≤l, ≤ d(-Log N + l)} g = 0` (`d = deg P`).

This differs from `ImprovKMT` only by the good-major-arcs hypothesis and by the absence of the
secondary term `(Log N)^{-c/ρ}`; `improvOfImprovGood` reduces the latter to the former. -/
def ImprovGood (P : Polynomial ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∃ (Cρ : ℝ) (C : ℝ≥0), 0 < Cρ ∧ 0 < C ∧
    ∀ (N l : ℕ) (f g : ℤ → ℂ), 1 ≤ N →
      MemLp f 2 Measure.count → MemLp g 2 Measure.count →
      GoodMajorArcs ρ Cρ l ((l : ℤ) - logN N) →
      (kmtProj ρ l (-(logN N) + (l : ℤ)) f = 0 ∨
        kmtProj ρ l ((P.natDegree : ℤ) * (-(logN N) + (l : ℤ))) g = 0) →
      eLpNorm (fun x : ℤ => AhalfR TZ (N : ℝ≥0) X P f g x) 1 Measure.count
        ≤ (C : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-(c * (l : ℝ)))) *
            eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count

end

end Work.KMTAreas.A4

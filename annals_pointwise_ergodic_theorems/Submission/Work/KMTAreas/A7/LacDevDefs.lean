/-
# The linearized deviation kernel of the lacunary bump-dilation family, and its symbol

This module fixes the two objects in which `Work.KMTAreas.A7.lacDilDevSqSum` — the
almost-orthogonality (square-function) half of the lacunary bump-dilation variational estimate —
and its supporting lemmas are stated.

For a Schwartz kernel `K`, a `2`-lacunary scale sequence `σ`, a finite set of indices `U` and signs
`ω`, the *linearized* (signed-sum) kernel is

  `lacDevLin K σ U ω = ∑_{n ∈ U} ω_n · devKern K σ n`,

where `devKern K σ n j = (1/σ_n) K (j/σ_n) − (∫K) · triKernel (lacLev σ n) j` is the kernel of the
deviation operator `devOp` (`Work.KMTAreas.A7.lacDilDefs`).  Its symbol (in the `chr`-convention of
`Work.KMTAreas.ADev`, `chr j θ = e^{2πijθ}`) is `lacDevSym`, the signed sum of the deviation
symbols `bumpSym K (σ n) θ − (∫K) · triSym (lacLev σ n) θ`.

The three analytic inputs about these objects used by the square-function bound are

* `lacDevSym` is the symbol of `lacDevLin` and is bounded by a constant depending only on `K`
  (`KMTAreas/A7/lacDevSymbol`);
* `lacDevLin` satisfies the discrete Hörmander condition with a constant depending only on `K`
  (`KMTAreas/A7/lacDevHormander`);
* the convolution with `lacDevLin` is bounded on `ℓ²(ℤ)` with a constant depending only on `K`
  (`KMTAreas/A7/lacDevL2`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacDilDefs
import Submission.Work.KMTAreas.ADev.Defs

set_option autoImplicit false

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- The symbol of the deviation kernel at scale `m` and level `L`, in the `chr`-convention of
`Work.KMTAreas.ADev`: `∑'_j ((1/m) K (j/m) − (∫K) triKernel L j) · e^{2πijθ}`. -/
def lacDevSymK (K : SchwartzMap ℝ ℂ) (m L : ℕ) (θ : ℝ) : ℂ :=
  Work.KMTAreas.ADev.bumpSym K m θ - lacConst K * Work.KMTAreas.ADev.triSym L θ

/-- The linearized (signed-sum) kernel of the deviation operators over the index set `U`. -/
def lacDevLin (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (U : Finset ℕ) (ω : ℕ → Bool) : ℤ → ℂ :=
  fun j => ∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n * devKern K σ n j

/-- The symbol of the linearized kernel: the signed sum of the deviation symbols. -/
def lacDevSym (K : SchwartzMap ℝ ℂ) (σ : ℕ → ℕ) (U : Finset ℕ) (ω : ℕ → Bool) (θ : ℝ) : ℂ :=
  ∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n * lacDevSymK K (σ n) (lacLev σ n) θ

end

end Work.KMTAreas.A7

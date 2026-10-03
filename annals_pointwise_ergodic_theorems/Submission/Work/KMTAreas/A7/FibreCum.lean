/-
# The cumulative-height fibres of the twisted projection

The workspace's exact-height fibre `Work.KMTAreas.A7.fiberOp`/`fiberOpD` of §7 of

* B. Krause, M. Mirek, T. Tao, *Pointwise ergodic theorems for non-conventional bilinear
  polynomial averages*, Annals of Math. 195 (3) 2022,

is the **difference** of two consecutive *cumulative-height* fibres:

  `fiberOpD ρ l m n₀ = fiberOpCum ρ l m n₀ - fiberOpCum ρ (l-1) m n₀`   (`l ≥ 1`),

where the cumulative fibre at height `l` is the convolution with the kernel
`j ↦ C_l(n₀ - j) · cw m j`, `C_l(y) = ∑_{α ∈ (ℚ/ℤ)_{≤l}} e(α y)` being the cumulative arithmetic
character.  The point of the cumulative normalisation is that

  `C_l(y) = ∑_{α ∈ iwArithFreqs ρ l} e(α y)`,

and the corresponding multiplier is exactly the Ionescu--Wainger projection symbol
`iwSymbolSet (iwArithFreqs ρ l) Φ`, so that the *linear* theory of area `A1` (the Ionescu--Wainger
multiplier theorem, in the interpolated form `Work.KMTAreas.A7.IwLqGeneral`) applies to it
*without* any narrow-window (`Shannon`) hypothesis on the arithmetic modulus.  Comparing with
the paper's §7, this is why the fibre bound of Lemma `ssu` is available for
`(l, -(2u))` merely *good major arcs* (`2u ≳ 2^{ρl}`), and not only in the narrow regime
`2^{2u} ≳ arithQ ρ l` used by the projection-based proof
`Work.KMTAreas.A7.residueLp_fiberOpD_le` of the workspace.

This file contains only the definition of the cumulative fibre, so that the fibre estimate
`Work.KMTAreas.A7.fiberOpCum_lp_goodArcs` and its consumers can refer to it.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-- **The cumulative-height fibre of the twisted projection** at the residue `n₀`: the convolution
with the kernel `j ↦ C_l(n₀ - j) · cw m j`, where `C_l(y) = ∑_{α ∈ iwArithFreqs ρ l} e(α y)` is
the cumulative arithmetic character of height `≤ 2^l`.

It is the multiplier with symbol `∑_{α ∈ (ℚ/ℤ)_{≤l}} e(α n₀) (periodize m)(θ - α)`; equivalently
it is the composition of the translation by `n₀` with the Ionescu--Wainger multiplier of symbol
`iwSymbolSet (iwArithFreqs ρ l) (periodize (fun ξ => ee (-(n₀ : ℝ) * ξ) * m ξ))`.

The exact-height fibres `fiberOp`, `fiberOpD` and `fiberOpPD` of the workspace recover from the
cumulative ones by taking differences in `l` (for `l ≥ 1`). -/
noncomputable def fiberOpCum (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (n₀ : ℤ) (v : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑' j : ℤ, (∑ α ∈ iwArithFreqs ρ l, fourier (T := 1) (n₀ - j) α) * cw m j * v (x - j)

end

end Work.KMTAreas.A7

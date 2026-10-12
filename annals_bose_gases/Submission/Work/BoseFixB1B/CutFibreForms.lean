import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.sectorCountBoxAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.CutFibreForms`

The **peeled fibre forms** of the smooth approximants of the sharp box state, in the vocabulary of
`Submission.Work.BoseFixB1B.sectorCountBoxAux` (`cutProd`, `sharpBoxState`, `IsCutFamily`).

**Why this module exists.**  The sharp-fibre program needs, for the two states
`Ψ_δ = (∏ i, γ δ (x i)) * ψ` and `W = 1_{B(u)^k} * ψ`, the position-space forms

* `cutFibreDir L A volA χ i Ψ` — the **Dirichlet (first-derivative) form** of the `i`-th
  windowed box-mean-free fibre, and
* `cutFibreMass L A volA χ i Ψ` — the **mass form** of the same fibre;

these are the two quantities to which the weighted `p`-space kinetic form `tBdiagForm` is
compared (via the windowed Plancherel identities, cf. `Work.BoseFixB1B.pform_sq_le_fibreDir`
and `Work.BoseFixB1B.pform_one_le_fibreMass`).

The same two quantities are *also* named `Work.BoseFixB1B.fibreDir` / `fibreMass` in
`Submission/Work/BoseFixB1B/SharpFibreDefs.lean`; that module, however, declares
`Work.BoseFixB1B.sharpState_apply` a second time (it is already in
`Submission.Work.BoseFixB1B.sectorCountBoxAux`), so **no module can import both** — the
`fibreWord_tendsto_cutProd` chain, which must import `sectorCountBoxAux` for its own statement,
therefore cannot use them.  This module re-declares the two forms under fresh names so that the
estimates can be stated, proved and used inside that chain.

Everything here is a definition; the estimates live in the sibling modules.
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The peeled fibre Dirichlet form** of slot `i` of the state `Ψ`: the `L²`-norm-squared of the
gradient of the windowed, box-mean-free slot-`i` fibre, integrated over the outside
configurations `r ∈ abox n L` and the slot position `y ∈ acube L`. -/
noncomputable def cutFibreDir {n : ℕ} (L : ℝ) (A : Set E3) (volA : ℝ) (χ : E3 → ℝ)
    (i : Fin (n + 1)) (Ψ : Submission.BoseGases.X (n + 1) → ℝ) : ℝ :=
  ∫ r in Submission.BoseGases.abox n L, ∫ y in Submission.BoseGases.acube L,
    ∑ k : Fin 3, (fderiv ℝ (fun z : E3 =>
      χ z * Work.SmallBoxTBWord.boxQ volA A i Ψ (Submission.BoseGases.kcInsN n i (z, r)))
        y (Submission.BoseGases.kcStdBasis k)) ^ 2

/-- **The peeled fibre mass form** of slot `i` of the state `Ψ`: the `L²`-norm-squared of the
windowed, box-mean-free slot-`i` fibre, integrated over the outside configurations and the slot
position. -/
noncomputable def cutFibreMass {n : ℕ} (L : ℝ) (A : Set E3) (volA : ℝ) (χ : E3 → ℝ)
    (i : Fin (n + 1)) (Ψ : Submission.BoseGases.X (n + 1) → ℝ) : ℝ :=
  ∫ r in Submission.BoseGases.abox n L, ∫ y in Submission.BoseGases.acube L,
    (χ y * Work.SmallBoxTBWord.boxQ volA A i Ψ (Submission.BoseGases.kcInsN n i (y, r))) ^ 2

/-! ## 2. The per-slot `p`-space form

`Work.UBBInputs8.tBdiagFormInd` (equivalently `Work.SmallBoxTBWord.tBdiagForm`) is the sum over
slots of `cutSlotForm`.  Splitting it off makes the two comparisons the sharp-fibre convergence
needs (`cutSlotForm` at the symbol `fsKinCoeff c` versus at `(·)²` and at `1`, and the
Cauchy–Schwarz comparison between the forms of `u`, `w` and `u - w`) statements about a single
slot, with the (junk-safe) integrability hypotheses displayed explicitly. -/

/-- **The per-slot amplitude mass**: `|B|⁻¹` times the `L²(x)`-mass-squared of the windowed,
box-mean-free slot-`i` amplitude of `Ψ` at momentum `p`.  It is `≥ 0` and is the `p`-integrand of
the slot-`i` term of the `p`-diagonal form. -/
noncomputable def cutSlotAmp {N : ℕ} (L : ℝ) (A : Set E3) (volA : ℝ) (χ : E3 → ℝ)
    (i : Fin N) (Ψ : Submission.BoseGases.X N → ℝ) : E3 → ℝ :=
  fun p => (L ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox N L,
    ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i Ψ) i x‖ ^ 2

/-- **The per-slot `p`-space form** of the symbol `F`: `(2π)⁻³ ∫_p F ‖p‖ · cutSlotAmp`.
`Work.UBBInputs8.tBdiagFormInd a A volA χ F Ψ = ∑ i, cutSlotForm a A volA χ F i Ψ`. -/
noncomputable def cutSlotForm {N : ℕ} (L : ℝ) (A : Set E3) (volA : ℝ) (χ : E3 → ℝ)
    (F : ℝ → ℝ) (i : Fin N) (Ψ : Submission.BoseGases.X N → ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, F ‖p‖ * cutSlotAmp L A volA χ i Ψ p

end Work.BoseFixB1B

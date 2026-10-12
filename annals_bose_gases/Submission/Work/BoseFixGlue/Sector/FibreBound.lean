import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixGlue.EΛBound
import Submission.Work.BoseKinLoc.Sector.boxForm_fibreSumA_of_integrable
import Submission.Work.BoseKinLoc.Sector.fibreNormA_eq
import Submission.Work.BoseKinLoc.Sector.integrable_sqNormB_fibStateA
import Submission.Work.BoseKinLoc.Sector.per_fibre_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Sector.FibreBound` — the fibre bound (C3) split into its two halves

FS `thm:CompareBoxEnergy` needs the fibre/box bound (`hfib` of
`Work.BoseKinLoc.Compare.compare_box_energy_v2`): for a smooth symmetric state `Φ` supported in a
centred box `abox N L` and every translation parameter `u`,

`min 0 (E_Λ(μ)) · ∫Φ² ≤ boxForm N v g ℓ μ d s ε_T b u Φ`.

This is the `C3` node of `BOSE_BOXNODES_LEAD.md` §3.2 (BoseKinLoc's
`Sector/fibre_bound_v3`).  The correction recorded there splits the proof into

* the **sector (fibre) sum bound** `FibreSumBound`: the bound with the *fibre sum*
  `fibreSumA` in place of the box form.  Its proof is the per-fibre argument
  (`Sector/per_fibre_bound`, proved) plus the norm bookkeeping (`fibreNormA_eq`,
  `integrable_sqNormB_fibStateA`, proved); the bounded-below inputs `hEo`, `hEi` come from
  `LHYBoxB` (`Work.BoseFixGlue.hEo_hEi_of_LHYBoxB`);
* the **case analysis** (`fibreInput_of_fibreSumBound`): the sector decomposition of the box
  form `boxForm_fibreSumA_of_integrable` (proved) handles the case in which the whole-space
  potential integrand is integrable; in the opposite case the potential integral is Mathlib's
  junk value `0` and the box form reduces to the kinetic word, which is nonnegative in FS's
  regime (`Word/fsT_nonneg`).
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseFixGlue

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The sector-sum form of the fibre bound.**  For every admissible chemical potential `μ`, every
`N`, every support box `L`, every translation `c` and every smooth symmetric state supported in the
translated box `c + abox N L`, the fibre sum (over the slot sets `S` of the box forms of the fibre
states, integrated over the outside configurations in `c + acube (max L ℓ)`) dominates
`min 0 E_Λ · ∫Ψ²`.

This is the "first half" of FS's fibre bound; `boxForm_fibreSumA_of_integrable` turns it into a
statement about `boxForm` itself when the potential integrand is integrable. -/
def FibreSumBound (v : ℝ³ → ℝ) (h : ScatSol v) (ε : ℝ) : Prop :=
  ∀ μ : ℝ, Adm v ε μ → ∀ (N : ℕ) (L : ℝ) (c : ℝ³) (Ψ : X N → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) Ψ → PermInvariant N Ψ →
    tsupport Ψ ⊆ (fun x : X N => fun i : Fin N => c + x i) '' abox N L →
    min 0 (EΛ v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ) (bB v μ))
        * (∫ z : X N, (Ψ z) ^ 2)
      ≤ Work.BoseKinLoc.Sector.fibreSumA v (g0 v h) (ℓB v μ) μ (dB v μ) (sB v μ) (eTB v μ)
          (bB v μ) ((fun z : ℝ³ => c + z) '' acube (max L (ℓB v μ))) Ψ

end Work.BoseFixGlue

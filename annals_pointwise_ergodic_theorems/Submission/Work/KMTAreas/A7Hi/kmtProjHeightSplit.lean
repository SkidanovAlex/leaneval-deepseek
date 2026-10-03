import Mathlib
import Submission.Work.KMTAreas.A7Hi.LowpassDefs
import Submission.Work.KMTAreas.A7.FiberL2Defs
import Submission.Work.KMTPlan.A6.MdlTleKer

set_option autoImplicit false

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open Work.Analysis.IonescuWainger
open scoped BigOperators

/-!
# The height splitting of the smooth Ionescu--Wainger projection: the fibre link

The IW projection `Π_{≤l,≤k} = kmtProj ρ l k` is the IW multiplier with the frequency set
`A_l = iwArithFreqs ρ l`; its kernel is `arithChar ρ l (-j) · cw (η_{≤k}) j`
(`Work.KMTPlan.A6.TleKer_eq_arChar_cw`).  Splitting `A_l = A_{l-1} ⊔ (A_l \ A_{l-1})` gives the
height decomposition

  `kmtProj ρ l k f − kmtProj ρ (l−1) k f = fiberOp ρ l (η_{≤k}) 0 f`,

where `fiberOp ρ l m 0` is the "exact-height fibre" of the sampling/residue machinery
(`Work.KMTAreas.A7.fiberOp`, `Work.KMTAreas.A7ResidueCharDefs`), i.e. the convolution with
`j ↦ arithCharNew ρ l (0 − j) · cw m j`.

This is the smooth-family companion of the paper's `T^{≤l}_Φ = T^{≤l-1}_Φ + T^{l}_Φ`
(`iwSymbol_eq_sdiff`) and is the first link of the adelic/sampling correspondence: any bound on the
*fibre* operators (the `FiberOp*`/`residueLp*`/`MSW_*` chain, e.g.
`Work.KMTAreas.A7Hi.FiberRephaseNarrowBand`, `Work.KMTAreas.A7Rep.fiberResidueMaxRephase`) gives,
after summation over the heights, a bound for the projection family `k ↦ kmtProj ρ l (−(m₀+k))` and
hence (through `Work.KMTAreas.A7Hi.lacunaryMaxPieceRep_of_lFreeVarPart`) for the lacunary maximal
piece of the paper's `(lin-1)`/`(lin-2)`.
-/

/-- The kernel of `kmtProj` is the arithmetic character times the continuous Fourier transform
`cw` of the rescaled cut-off. -/
lemma kmtKernel_eq_arithChar_cw (ρ : ℝ) (l : ℕ) (k j : ℤ) :
    Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize
            (etaCut Work.KMTContract.kmtEta k))) j
      = Work.KMTAreas.A7.arithChar ρ l (-j)
        * Work.KMTAreas.A7.cw (etaCut Work.KMTContract.kmtEta k) j := by
  have hφint : Integrable (etaCut Work.KMTContract.kmtEta k) := by
    rw [← Work.KMTAreas.A7.etaCutSchwartz_coe k]
    exact SchwartzMap.integrable _
  simpa only [Work.KMTPlan.A6.TleKer, Work.KMTPlan.A6.TleArChar, Work.KMTAreas.A7.arithChar]
    using Work.KMTPlan.A6.TleKer_eq_arChar_cw ρ l hφint j

end Work.KMTAreas.A7Hi

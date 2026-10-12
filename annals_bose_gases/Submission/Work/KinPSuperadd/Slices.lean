import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Submission.Work.KinPSuperadd.slice_contDiff_top
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `KinPSuperadd.Slices` — the `ContDiff ℝ ∞` slices of a smooth state

`Work.KinPSuperadd.slice_contDiff_top` proves the slices of a smooth state smooth
in the ANALYTIC sense `ContDiff ℝ ⊤` (`ω`); the corpus's trial states
(`Submission.BoseGases.CSBox`) are smooth in the sense `ContDiff ℝ ∞`, and the
statements of this chapter (`SlotSplit`, `slotEB_perState`, ...) are stated for
`ContDiff ℝ ∞` states.  This module supplies the `ContDiff ℝ ∞` slice lemmas
used by `slotEB_perState` and `rayleigh_diagSlotWord`.

Note `ContDiff ℝ ⊤` (`ω`) means ANALYTIC (`Mathlib/Analysis/Calculus/ContDiff/Defs.lean`:
"the parameter `n` ... can be a natural number, `∞`, or `ω`"; `n = ω` requires
analyticity).  That is why the chapter's hypotheses are stated with `∞`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.KinPSuperadd

open Submission BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The first-block slice `u ↦ Φ (mergeBlock N₁ N₂ (u,w))` of a `C^∞` state is
`C^∞`. -/
lemma slice_contDiff_infty_fst {N1 N2 : ℕ} {Φ : X (N1 + N2) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (w : X N2) :
    ContDiff ℝ ∞ (fun u : X N1 => Φ (mergeBlock N1 N2 (u, w))) :=
  hΦ.comp ((contDiff_mergeBlock_fst N1 N2 w).of_le le_top)

/-- The second-block slice `w ↦ Φ (mergeBlock N₁ N₂ (u,w))` of a `C^∞` state is
`C^∞`. -/
lemma slice_contDiff_infty_snd {N1 N2 : ℕ} {Φ : X (N1 + N2) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (u : X N1) :
    ContDiff ℝ ∞ (fun w : X N2 => Φ (mergeBlock N1 N2 (u, w))) :=
  hΦ.comp ((contDiff_mergeBlock_snd N1 N2 u).of_le le_top)

/-- Both families of block slices of a `C^∞` state are `C^∞`. -/
lemma slice_contDiff_infty_pair {N1 N2 : ℕ} {Φ : X (N1 + N2) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) :
    (∀ w : X N2, ContDiff ℝ ∞ (fun u : X N1 => Φ (mergeBlock N1 N2 (u, w))))
      ∧ (∀ u : X N1, ContDiff ℝ ∞ (fun w : X N2 => Φ (mergeBlock N1 N2 (u, w)))) :=
  ⟨fun w => slice_contDiff_infty_fst hΦ w, fun u => slice_contDiff_infty_snd hΦ u⟩

end Work.KinPSuperadd

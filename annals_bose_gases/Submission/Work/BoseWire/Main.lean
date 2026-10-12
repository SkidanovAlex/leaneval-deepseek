import ChallengeDeps
import Submission.Work.BoseFixKin.Handoff
import Submission.Work.BoseTop.Targets
import Submission.Work.BoseWire.Basic
import Submission.Work.BoseWire.SymTail.Assembly
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseWire/Main` — the wire: `LHYBoxBInput ⟹ HBoxGpTarget`

This module carries the area's main theorem,

`Work.BoseWire.HBoxGpTarget_of_LHYBoxBInput :`
`<challenge hypotheses on v> → LHYBoxBInput v → Work.BoseTop.HBoxGpTarget v`,

together with the two ingredients of its proof:

* `Work.BoseWire.symBoxReduction_of_radial` — the corpus's bosonic reduction
  (`Work.BoseTop.symBoxReduction`) from `0 ≤ v`, `MemLp v 1` and radiality;
* `Work.BoseWire.av_nonneg_of_LHYBoxBInput` — `0 ≤ a v` from the wire's input
  (the bundle contains a scattering solution, so
  `Submission.BoseGases.chosen_av_bounds_weak` applies).

## Why the reduction is taken from `Work.BoseWire.SymTail`

The corpus proves the bosonic reduction in the `BoseSym` chapter
(`Work.BoseSym.symBoxEnergy_le_boxEnergy_of_radial`, `Submission/Work/BoseSym/Main.lean`), but
`Work.BoseSym.Main` **cannot** be imported together with the `LHYBoxB` chain: the workspace
contains two incompatible declarations of the single name `Work.BoseSym.Form.qmp_pair_pi`
(`Submission/Work/BoseSym/Form/qmp_pair.lean`, the general form used by
`Work.BoseFixGlue.Pot` and hence by `Work.BoseFixKin`, and
`Submission/Work/BoseSym/Form/aemeasurable_Vpot.lean`, the `Fin N` form imported by
`Work.BoseSym.Main`), and Lean refuses to load both.  `Submission/Work/BoseWire/SymTail/`
therefore reproduces the *tail* of the `BoseSym` chapter (same proofs, local names) on top of
only the compatible leaves, and `symBoxReduction_of_radial` below is proved from that copy.  A
caller sees no difference: the statement is `Work.BoseTop.symBoxReduction v`.

The wire itself is the two-case argument the deliverable asks for:

1. `0 < a v`: `Work.BoseFixKin.HBoxGp_of_LHYBoxB` (the `hb`-free handoff of
   `Submission/Work/BoseFixKin/Handoff.lean`) converts the box theorem
   `LHYBoxB` into the pressure-level per-potential bound
   `Work.BoseTop.HBoxGp v η₀ C`, and the input's own `η₀`, `C` supply the
   numerical side conditions of `Work.BoseTop.HBoxGpTarget`;
2. otherwise `a v = 0` (`0 ≤ a v` came from step 0), and
   `Work.BoseTop.HBoxGpTarget_of_av_zero` gives the target without any box
   input at all.

Nothing else is assumed: no kinetic localisation constant, no `b`-domain
hypothesis, and no `ScatSol` witness beyond the one bundled in the input.
-/

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseWire

open _root_.BoseGases Submission.BoseGases
open Work.UBB Work.BoseBoxFix Work.BoseTop

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The bosonic reduction (`symBoxReduction`) from radiality -/

/-- **The corpus's bosonic reduction from radiality.**  For `0 ≤ v`,
`MemLp v 1` and radial `v`, the infimum of the Rayleigh quotient over the
symmetric (bosonic) trial states is at most the infimum over all trial states,
i.e. `Work.BoseTop.symBoxReduction v`.

Proved from this directory's clash-free copy of the assembled `BoseSym` chapter
(`Work.BoseWire.SymTail.symBoxEnergy_le_boxEnergy_of_radial`); see the module
comment for why `Work.BoseSym.Main` cannot be used directly here. -/
theorem symBoxReduction_of_radial {v : ℝ³ → ℝ} (hv : 0 ≤ v) (hv1 : MemLp v 1)
    (hrad : _root_.BoseGases.IsRadial v) : symBoxReduction v :=
  fun N L hL => Work.BoseWire.SymTail.symBoxEnergy_le_boxEnergy_of_radial hL hv hv1 hrad

/-! ## Nonnegativity of the scattering length -/

/-- **`0 ≤ a v` from the wire's input.**  The bundle `LHYBoxBInput v` contains a
scattering solution of `v`, so the corpus's `0 ≤ a v ≤ R` bound for the chosen
scattering solution (`Submission.BoseGases.chosen_av_bounds_weak`) applies.
This is the same fact as the corpus's `av_nonneg`, but available without
importing the challenge file. -/
theorem av_nonneg_of_LHYBoxBInput {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hv_radial : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R) (hIn : LHYBoxBInput v) :
    0 ≤ a v :=
  (chosen_av_bounds_weak (v := v) (R := R) hR hv_nonneg hv_radial hv_supp
    hIn.exists_scatSol).1

/-! ## The wire -/

/-- **The wire's main theorem**: under the challenge's hypotheses on `v`, the
single box input `LHYBoxBInput v` produces the pressure-level target
`Work.BoseTop.HBoxGpTarget v` — i.e. FS `thm:LHY-Background`, the exact
hypothesis of the proved `Work.BoseTop.hpres_of_HBoxGp` and hence of the whole
challenge statement.

The two branches are the ones of the deliverable: `0 < a v` (where the box
theorem is used, through the `hb`-free handoff `HBoxGp_of_LHYBoxB`), and
`a v = 0` (where the target holds unconditionally). -/
theorem HBoxGpTarget_of_LHYBoxBInput (v : ℝ³ → ℝ) (hv_nonneg : 0 ≤ v) (hv_radial : _root_.BoseGases.IsRadial v)
    (hv_memL1 : MemLp v 1) {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hIn : LHYBoxBInput v) : HBoxGpTarget v := by
  by_cases hav : 0 < a v
  · obtain ⟨h, η₀, C, hη₀, hη₀le, hC, hL⟩ := hIn
    exact ⟨η₀, C, hη₀, hη₀le, hC,
      Work.BoseFixKin.HBoxGp_of_LHYBoxB hv_nonneg hv_memL1
        (symBoxReduction_of_radial hv_nonneg hv_memL1 hv_radial) hR hv_supp hav
        hη₀ hη₀le hC hL⟩
  · have hav0 : a v = 0 :=
      le_antisymm (not_lt.mp hav) (av_nonneg_of_LHYBoxBInput hv_nonneg hv_radial hR hv_supp hIn)
    exact HBoxGpTarget_of_av_zero hv_nonneg hv_memL1 hav0

/-- The same wire, with the target `Work.BoseTop.HBoxGp` left unfolded: the box
input produces *some* admissible exponent and coefficient for the pressure-level
per-potential bound.  This is the form a caller wants when it has to *choose*
the parameters (e.g. to match the challenge's own `η = 1/2000`, `K = 1`). -/
theorem exists_HBoxGp_of_LHYBoxBInput (v : ℝ³ → ℝ) (hv_nonneg : 0 ≤ v) (hv_radial : _root_.BoseGases.IsRadial v)
    (hv_memL1 : MemLp v 1) {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (hIn : LHYBoxBInput v) :
    ∃ η₀ C : ℝ, 1 / 2000 < η₀ ∧ η₀ ≤ 1 / 2 ∧ 0 ≤ C ∧ HBoxGp v η₀ C :=
  HBoxGpTarget_of_LHYBoxBInput v hv_nonneg hv_radial hv_memL1 hR hv_supp hIn

end Work.BoseWire

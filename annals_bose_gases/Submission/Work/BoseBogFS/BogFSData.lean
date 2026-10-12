import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.BoseB6Est.Interface
import Submission.Work.BoseB6Est.fsRegime_fs
import Submission.Work.BoseB6Est.fsZeroPoint_le
import Submission.Work.BoseBogFS.Final
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.BogFSData` — the transfer of the B6Est estimates to the
abstract mode group

`Work.BoseB6Est.fsZeroPoint_le` and `Work.BoseB6Est.kappaSum_le` are stated on the **mesh-`n`
lattice** `modeIdx n = Fin 3 → Fin (gridD n)` in FS's scaled variables, while
`BogOpBoundFS` quantifies over an abstract mode group.  This module supplies exactly the
missing identification:

* `FsMatch F E ρ` — one `FsBogData n` together with a bijection `Mode ≃ modeIdx n` on which
  the *summands* agree pointwise (this is the "strengthen the interface with the
  mode-identification" repair of `BOSE_BOXFOCK_LEAD.md` §5.2 option (i)); the pointwise
  form is what makes the statement independent of the representative convention
  (`kmomLab`'s centred integers vs `latticeCenter`'s half-integers);
* `sum_zp_eq`, `sum_kap_eq` — the two sums are the B6Est sums;
* the two estimates `hZP`/`hKAP` of `bogOpBoundFS_of_estimates` then follow from
  `fsZeroPoint_le`, `lattice_sum_value`, `lhyValue_eight_pi` and `kappaSum_le`.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7 Work.BoseB6Est

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- `Work.BoseB6.lhySharp = Work.UBB.lhyC` (the two chapters write the same constant). -/
theorem lhySharp_eq_lhyC : Work.BoseB6.lhySharp = Work.UBB.lhyC := rfl

/-- `(1/2)·(2π)⁻³·lhyValue(8π) = 4π·lhyC`: FS's `lhyValue_eight_pi` in the chapter's
normalisation (the constant of `thm:BogHamDiag`'s zero-point term). -/
theorem half_lhyValue_eight_pi :
    (1 / 2) * ((2 * π) ^ 3)⁻¹ * Work.BoseB6.lhyValue (8 * π) = 4 * π * lhyC := by
  rw [Work.BoseB6.lhyValue_eight_pi, lhySharp_eq_lhyC]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

/-- **The FS data of one `KzDatum` at density `ρ`**: B6Est's mesh-`n` mode lattice together
with a bijection of the labels on which the summands of the zero-point sum and of the
`κ`-sum agree pointwise. -/
structure FsMatch (F : FockData Mode) (E : Q3Env Mode) (ρ gHat0 : ℝ) where
  n : ℕ
  D : FsBogData n
  e : Mode ≃ modeIdx n
  hρ : D.ρz = ρ
  ha : D.a = E.aScat
  hℓ : D.ℓ = E.ell
  hz : D.z = bogZ E ρ
  hμ : D.μ = E.mu
  /-- the diagonal kernel `𝒜` of the two mode systems agrees pointwise. -/
  hA : ∀ k : Mode, bogA E ρ k = fsA D.ρz D.a D.K D.εT D.c1 D.c2 (modePos n (e k))
  /-- the diagonal kernel `ℬ` of the two mode systems agrees pointwise. -/
  hB : ∀ k : Mode, bogB E ρ k = fsB D.ρz D.a D.K (modePos n (e k))
  /-- the linear kernel `𝒞` of the two mode systems agrees pointwise. -/
  hC : ∀ k : Mode, bogC E ρ k = fsC D.ℓ D.ρz D.μ D.a D.z D.χh (modePos n (e k))
  /-- `ĝω(0)`: the mass term of `lem:BogIntegral`. -/
  hGw : fsGω0 D.ρz D.a D.K = E.W1omega0
  /-- `ĝ(0)`: the `κ`-sum's coefficient. -/
  hG0 : fsG0 D.ρz D.a D.ℓ D.z D.chiM = gHat0

/-- The zero-point sum equals B6Est's `zpSum` under the identification. -/
theorem sum_zp_eq (F : FockData Mode) (E : Q3Env Mode) (ρ gHat0 : ℝ)
    (M : FsMatch F E ρ gHat0) :
    (∑ k : Mode, Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k))
      = zpSum M.n M.D.ρz M.D.a M.D.K M.D.εT M.D.c1 M.D.c2 := by
  rw [zpSum]
  rw [← Equiv.sum_comp M.e.symm
    (fun k : Mode => Work.BoseB6.bogZeroPoint (bogA E ρ k) (bogB E ρ k))]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [M.hA (M.e.symm k'), M.hB (M.e.symm k'), Equiv.apply_symm_apply M.e k']

/-- The `κ`-sum equals B6Est's `kappaSum` under the identification. -/
theorem sum_kap_eq (F : FockData Mode) (E : Q3Env Mode) (ρ gHat0 : ℝ)
    (M : FsMatch F E ρ gHat0) :
    (∑ k : Mode, Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k))
      = kappaSum M.n M.D.ρz M.D.a M.D.ℓ M.D.μ M.D.z M.D.K M.D.εT M.D.c1 M.D.c2 M.D.χh := by
  rw [kappaSum]
  rw [← Equiv.sum_comp M.e.symm
    (fun k : Mode => Work.BoseB6.bogKappaErr (bogA E ρ k) (bogB E ρ k) (bogC E ρ k))]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [M.hA (M.e.symm k'), M.hB (M.e.symm k'), M.hC (M.e.symm k'),
    Equiv.apply_symm_apply M.e k']

end Work.BoseBogFS

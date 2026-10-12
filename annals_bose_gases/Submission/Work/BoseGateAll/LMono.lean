import ChallengeDeps
import Submission.Work.BoseRowsL.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateAll.LMono` — moving the decay-free interface

`Work.BoseRowsL.HonestInterfaceL` is attached to a *given* small-parameter bundle
`hthr` and to a *given* cube-size function `Ng' ≥ hthr.Ng`.  A caller of the gate
(`Work.BoseGateAll.exists_honestGateFSAll_of_honestInterfaceL`) however must supply
the corrected row 3 at the *bundle's* cube size, and the row-3 work
(`Work.BoseRowQ2.RowQ2AllRegimeN_of_core`, fed by `RowQ2AllCore_holds`) produces it
at a cube size of its own choosing.  The two have to be brought together, and this
module supplies the tool:

* `Work.BoseGateFS.GateThresholds.promoteNg` (in `Interface.lean`) enlarges the
  bundle's `Ng` with its threshold unchanged;
* `Work.BoseRowsL.HonestInterfaceL.mono` (here) moves the interface to a bundle
  with a **smaller `εg`** and a **larger cube**, provided the interface's own `Ng'`
  is enlarged along with it.

Every field transports, and for the same reason: the antecedent `∀ μ, Ng μ ≤ (HM μ).N`
is *weaker* for a larger `Ng` and the antecedent `μ a³ ≤ εg` is *weaker* for a
smaller `εg`, so both moves weaken the interface, while the conclusions
(`bndW`, `lipW`, `tailL`, `tailC`, `fsp`, `fspKz`, `rkh`, `a16`) mention only
`ℓ`, `R`, `a v`, the honest family and the *intersected* tails, which shrink with
the cube.  `cutR` needs `uvRad` to be monotone in the cube size
(`uvRad_mono` below; `uvRad ℓ N = 2π(N/4)/ℓ`).

**Why the non-`L` interface cannot be moved this way.**  In
`Work.BoseRowsFS.HonestInterface` the fields `cut` and `tail` have conclusions
mentioning `uvRad (ellH v μ) (hthr.Ng μ)` at the bundle's **own** cube size, so
they do *not* transport when `hthr.Ng` changes: the row-3 cube size must be chosen
compatibly with the interface's *inhabitation* up front.  The `L` interface avoids
this by carrying its cube size `Ng'` as a field of its own.
-/

noncomputable section

open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseGateAll

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `uvRad ℓ N` is monotone in `N` (for `ℓ > 0`): `uvRad ℓ N = 2π(N/4)/ℓ`. -/
theorem uvRad_mono {ℓ : ℝ} (hℓ : 0 < ℓ) {N N' : ℕ} (hNN : N ≤ N') :
    uvRad ℓ N ≤ uvRad ℓ N' := by
  rw [uvRad, uvRad]
  have h1 : (N : ℝ) ≤ (N' : ℝ) := by exact_mod_cast hNN
  have hc : 0 < 2 * Real.pi / ℓ / 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h1 hc.le]

end Work.BoseGateAll

namespace Work.BoseRowsL

/-- **Moving the decay-free interface to a smaller threshold and a larger cube.**

From `H : HonestInterfaceL R hthr` we obtain `HonestInterfaceL R hthr'` for any
bundle `hthr'` with `hthr'.εg ≤ hthr.εg`, at any cube size `Ng''` dominating both
`hthr'.Ng` (its `Ng'_ge`) and the interface's own `H.Ng'` (`cutR`, `tailL`,
`tailC`).  This is the tool that lets the corrected row 3, produced at a cube size
of its own, be fed to the gate at the interface's threshold. -/
def HonestInterfaceL.mono {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {R : ℝ} {hthr : Work.BoseGateFS.GateThresholds v h fc fu R}
    (H : HonestInterfaceL R hthr)
    {hthr' : Work.BoseGateFS.GateThresholds v h fc fu R} (hεg : hthr'.εg ≤ hthr.εg)
    (Ng'' : ℝ → ℕ) (hNg'' : ∀ μ, hthr'.Ng μ ≤ Ng'' μ) (hNg' : ∀ μ, H.Ng' μ ≤ Ng'' μ) :
    HonestInterfaceL R hthr' where
  Cw := H.Cw
  Cw_nonneg := H.Cw_nonneg
  bndW := H.bndW
  lipW := H.lipW
  Ng' := Ng''
  Ng'_ge := hNg''
  cutR := fun μ hμ hε =>
    le_trans (H.cutR μ hμ (le_trans hε hεg))
      (by
        have := Work.BoseGateAll.uvRad_mono (Work.BoseBoxFock.ellH_pos v μ) (hNg' μ)
        linarith)
  tailL := fun μ hμ hε N hN S hS =>
    H.tailL μ hμ (le_trans hε hεg) N (le_trans (hNg' μ) hN) S hS
  tailC := fun μ hμ hε N hN =>
    H.tailC μ hμ (le_trans hε hεg) N (le_trans (hNg' μ) hN)
  fsp := fun HM μ hμ hε => H.fsp HM μ hμ (le_trans hε hεg)
  fspKz := fun HM μ ρ hμ hε => H.fspKz HM μ ρ hμ (le_trans hε hεg)
  rkh := fun HM μ hμ hε => H.rkh HM μ hμ (le_trans hε hεg)
  a16 := fun HM μ hμ hε => H.a16 HM μ hμ (le_trans hε hεg)

end Work.BoseRowsL

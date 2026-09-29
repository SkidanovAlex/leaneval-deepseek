import Mathlib
import Submission.Work.CNum.Fx
import Submission.Work.CNum.BoxSideDefs
import Submission.Work.CNum.SmallBox
import Submission.Work.CNum.NrmSpec
import Submission.Work.CNum.BoxSide
import Submission.Work.CNum.GridSmall
import Submission.Work.CNum.GridChord

/-!
# `Work.CNum.GridFacts` — the `CNum` certificate's side conditions at the boundary grid

The certificate of Theorem C evaluates `Gv`/`gv` (`Fx.lean`) on the `1024` arcs of the boundary
circle `{ψ_C(e^{iθ})}`.  This module collects, in one conjunction, all the side conditions that the
per-arc estimates assume:

* the enclosing ball `toPB I` really contains the box `I` (`Work.CNum.BoxSide.boxSide_pbBound`);
* every grid box `ptOf j` (`j ≤ 1024`) and the two cusp boxes satisfy the `BoxOK` side conditions
  of the `44`-term series bounds (`Work.CNum.BoxSide.boxSide_ptOf`, `boxSide_cuspA`, `boxSide_cuspB`);
* every one of those boxes is `Small` (`Work.CNum.GridSmall`), so the mantissa-level chord bound
  `distUp` (`Work.CNum.DistUpCore`) applies;
* the `5`-scaled adjacent `W`- and `V`-chord bounds at the `1024` grid arcs and at the four arcs
  meeting the two cusps (`Work.CNum.GridChord`), i.e. the hypothesis under which the chord growth
  estimate `Work.CNum.ChordSpec` controls the variation of `log ‖h‖` along each arc.

The last two items are pure kernel-evaluated integer certificates: every quantity involved
(`ptOf`, `toPB`, `absMax`, `distUp`, `dWup`, `dVup`, `nrmUp`, `nrmDn`) is a closed integer
expression, so `decide +kernel` discharges the finitely many instances without any extra axiom.
-/

namespace Work.CNum

open Work.ANum

theorem GridFacts :
    (∀ (I : Work.CNum.Cpx) (z : ℂ), I.Mem z → ‖z - Work.CNum.bpt (Work.CNum.toPB I)‖ ≤ Work.ANum.m2r (Work.CNum.toPB I).e)
    ∧ (∀ j : ℕ, j ≤ 1024 → Work.CNum.BoxOK (Work.CNum.ptOf j))
    ∧ Work.CNum.BoxOK Work.CNum.ptCuspA ∧ Work.CNum.BoxOK Work.CNum.ptCuspB
    ∧ (∀ j : ℕ, j ≤ 1024 → Work.CNum.Small (Work.CNum.ptOf j))
    ∧ Work.CNum.Small Work.CNum.ptCuspA ∧ Work.CNum.Small Work.CNum.ptCuspB
    ∧ (∀ k : ℕ, k ≤ 1023 → 5 * Work.CNum.dWup (Work.CNum.ptOf k) (Work.CNum.ptOf (k + 1)) ≤ Work.ANum.SC)
    ∧ (∀ k : ℕ, k ≤ 1023 → 5 * Work.CNum.dVup (Work.CNum.ptOf k) (Work.CNum.ptOf (k + 1)) ≤ Work.ANum.SC)
    ∧ 5 * Work.CNum.dWup (Work.CNum.ptOf 244) Work.CNum.ptCuspA ≤ Work.ANum.SC
    ∧ 5 * Work.CNum.dWup (Work.CNum.ptOf 780) Work.CNum.ptCuspB ≤ Work.ANum.SC
    ∧ 5 * Work.CNum.dVup (Work.CNum.ptOf 245) Work.CNum.ptCuspA ≤ Work.ANum.SC
    ∧ 5 * Work.CNum.dVup (Work.CNum.ptOf 779) Work.CNum.ptCuspB ≤ Work.ANum.SC :=
  ⟨BoxSide.1, BoxSide.2.1, BoxSide.2.2.1, BoxSide.2.2.2,
   GridSmall.1, GridSmall.2.1, GridSmall.2.2,
   GridChord.1, GridChord.2.1, GridChord.2.2.1, GridChord.2.2.2.1,
   GridChord.2.2.2.2.1, GridChord.2.2.2.2.2⟩

end Work.CNum

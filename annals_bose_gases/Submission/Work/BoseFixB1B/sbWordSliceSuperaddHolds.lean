import ChallengeDeps
import Submission.Work.BoseFixB1B.sbKin_slice_slotSplit
import Submission.Work.BoseFixB1S.sbWordSliceRegime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.sbWordSliceSuperaddHolds` — FS Step E at the sliding box, closed

The word-level grouping step of FS `thm:smallbox` (Step E, `final_v2.tex` 3960–4045) at the
*sliding* box B(u),

    sbWord h μ u Φ
      ≥ ∫_{w ∈ abox N₂ ℓ} sbWord h μ u (fun y ↦ Φ (merge(y,w)))
        + ∫_{y ∈ abox N₁ ℓ} sbWord h μ u (fun w ↦ Φ (merge(y,w))),      ℓ = sideAt μ (a v),

was proved in `Submission/Work/BoseFixB1S/sbWordSliceRegime.lean` **with its kinetic half as an
explicit hypothesis** `hKin : SlotSplit ℓ (fun N Ψ ↦ sbKin μ M u Ψ)`.  The kinetic half is now
proved (`Work.BoseFixB1B.sbKin_slice_slotSplit`: the sliding kinetic word `sbKin` is a sum of
one-slot forms, so it block-splits), so the capstone can be discharged.  This module does exactly
that, so that the grouping at the sliding box is available *unconditionally* (in the regime
`R ≤ ℓd/16`, `R ≤ ℓ·chiR0` of `Adm`, which is the standing regime of the whole a-priori chapter —
see `Work.BoseFixB1.regime_sideAt_ge`).

The two halves of the grouping, and where they are proved:

* **potential half** (`sbWord`'s `qLHSwordB` part): `sbPot_slice_superadd_regime`
  (`Submission/Work/BoseFixB1S/sbWordSliceRegime.lean`) — the cross-group pair density is `≥ 0`
  and is dropped; the abstract form (with the density integrabilities as hypotheses) is
  `Work.BoseFixB1B.qLHSword_slice_superadd` (`Submission/Work/BoseFixB1B/SliceSuperadd.lean`);
* **kinetic half** (the gap `cnPlusBoxInd` and the spectral slot `tBwordKinInd`):
  `Work.BoseFixB1B.sbKin_slice_slotSplit`, built from `Work.BoseFixB1B.cnPlusBoxInd_slice_split`
  (the one-slot box-projected excited count) and `Work.BoseFixB1B.tBdiagFormInd_slice_split_box`
  (the one-slot `p`-diagonal form, with the standing hypotheses on the box `A` and the window `χ`
  that make the box projection honest — see
  `FINDING_tBdiagFormInd_slice_split_missing_joint_integrability.md`).

**What this is for.**  With the grouping, the block decomposition bounds the small-box energy by
the slice energies and gives `e_B(N₁+N₂, μ) ≥ e_B(N₁, μ) + e_B(N₂, μ)`, hence FS's descent
`n = m·n' + n''` — the mechanism that makes `thm:smallbox` work at *all* densities (the
`n ≲ μ|B|` case is `Work.BoseFixB1B.sectorCountSmallboxBox`'s remaining input: the sliding-box
Bogoliubov port).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.UBB

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **FS Step E (grouping) at the sliding box, unconditionally.**  This is
`Work.BoseFixB1S.sbWord_slice_superadd_regime` with its kinetic hypothesis discharged by
`Work.BoseFixB1B.sbKin_slice_slotSplit`. -/
theorem sbWord_slice_superadd_regime_holds {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    (hav : 0 < _root_.BoseGases.a v) {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hR16 : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    (u : E3) {N₁ N₂ : ℕ}
    {Φ : Submission.BoseGases.X (N₁ + N₂) → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Work.BoseFixB1.sbWord h μ u Φ
      ≥ (∫ w in Submission.BoseGases.abox N₂ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            Work.BoseFixB1.sbWord h μ u
              (fun y => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w))))
        + (∫ y in Submission.BoseGases.abox N₁ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
            Work.BoseFixB1.sbWord h μ u
              (fun w => Φ (Submission.BoseGases.mergeBlock N₁ N₂ (y, w)))) :=
  Work.BoseFixB1S.sbWord_slice_superadd_regime h hv hv1 hvrad hR hv_supp hav hAdm hR16 hRχ u
    (Work.BoseFixB1B.sbKin_slice_slotSplit h hv hv1 hvrad hR hv_supp hav hAdm u) hΦ

end Work.BoseFixB1B

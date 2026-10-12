import ChallengeDeps
import Submission.Work.BoseB1Cube.sbWordCube_descent_twoBlockAtSizes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

/-- **FS Step E's iterated-block descent (the "grouping" step) for the single-cube-cutoff word
`sbWordCube`** — the cube twin of the PROVED `Work.BoseFixB1B.sbWord_descent_atSizes`
(`Submission/Work/BoseFixB1B/sbWord_descent_atSizes.lean`), which it reproduces *verbatim* with
`Work.BoseFixB1.sbWord ↦ Work.BoseFixB1B.sbWordCube`.

Mathematically: a state on `m·n' + n''` slots whose every one-slot-block slice obeys the per-size
bound `G₁·∫Ψ² ≤ sbWordCube` (block size `n'`) resp. `G₂·∫Ψ² ≤ sbWordCube` (block size `n''`)
obeys `(m·G₁ + G₂)·∫Φ² ≤ sbWordCube` on the whole state.  This is FS's `n = m n' + n''`
decomposition (`final_v2.tex` ll. 3990–4055, drop the *positive* inter-block interaction), the
step that creates the count window inside `thm:smallbox`.

WHY IT IS NEEDED, AND WHY IT IS ELEMENTARY.  The chapter's residual `CubePerBox` reduces (via the
dense band arm `CubeBandArmDensePos`, half `CubeBandArmDenseDeadRow`) to a **count-bounded**
per-box row plus exactly this grouping step; the frozen chapter's grouping is already PROVED
(`sbWord_descent_atSizes`, `sbWord_descent_twoBlockAtSizes`, `sbWord_descent_grouped`,
`sbWord_slice_superadd_regime_holds`), but the cube twin is NOT on disk.

TRAJECTORY (transcribe the frozen proofs):
* the word splits *window-freely*: `sbWordCube = sbKinCube + sbPot`, and `sbPot` is the SAME
  object as the frozen one (`Work.BoseFixB1.bqPotsplit`), so the potential half of the
  superadditivity is the PROVED `Work.BoseFixB1S.sbPot_slice_superadd_regime` *verbatim*;
* the kinetic half is a SUM OVER SLOTS of one-slot forms
  (`sbKinCube = bGapCoeff·cnPlusBoxInd + cubeSpectral`, both `Σᵢ`-forms), so it is *additive*
  (hence superadditive) over slot blocks for ANY window χ — the window only enters each summand;
  `Work.BoseFixB1S.sbKinSliceSplitW` and `Work.BoseFixB1S.slotSplitCnPlusBoxInd` are the
  slot-split tools.  The only genuinely new sub-result is the `chiSmallB` variant of the slot-swap
  used in `sbKinSliceSplitW` (there it is stated for `chiB`);
* then the two-block step, the `groupedIdx` induction on the right-nested presentation
  (`groupedIdx (M+1) n' n'' = n' + groupedIdx M n' n''` is DEFINITIONAL) and the final
  `(m·G₁ + G₂)` bookkeeping are *copies* of the frozen proof with the word name changed.
  `Work.BoseB1Cube.sbWordCube_sectorAdditive` (PROVED) is the cube sector analogue and may
  simplify the bookkeeping.

Do NOT weaken the statement; do NOT re-derive the frozen descent (import it and mirror it), and do
NOT use any *unconditional* per-box row (the per-size hypotheses `hB1`/`hB2` are the point: they
are state-*independent* bounds at two fixed sizes).  If a cube slot-swap result is needed and
missing, file it as a child rather than weakening this statement. -/
theorem sbWordCube_descent_atSizes {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hR16 : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) {n' n'' m : ℕ} (G1 G2 : ℝ)
    (hB1 : ∀ (Ψ : Submission.BoseGases.X n' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
      (∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox n' (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
        Ψ x ≠ 0 → ∀ i : Fin n', x i ∈ Submission.BoseGases.dlBox
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
      G1 * (∫ x in Submission.BoseGases.abox n' (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Ψ x) ^ 2) ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ)
    (hB2 : ∀ (Ψ : Submission.BoseGases.X n'' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
      (∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox n'' (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
        Ψ x ≠ 0 → ∀ i : Fin n'', x i ∈ Submission.BoseGases.dlBox
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
      G2 * (∫ x in Submission.BoseGases.abox n'' (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Ψ x) ^ 2) ≤ Work.BoseFixB1B.sbWordCube v h μ u Ψ)
    {Φ : Submission.BoseGases.X (m * n' + n'') → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hin : ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (Submission.BoseGases.abox (m * n' + n'') (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
      Φ x ≠ 0 → ∀ i : Fin (m * n' + n''), x i ∈ Submission.BoseGases.dlBox
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :
    ((m : ℝ) * G1 + G2) * (∫ x in Submission.BoseGases.abox (m * n' + n'')
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Φ x) ^ 2)
      ≤ Work.BoseFixB1B.sbWordCube v h μ u Φ := by
  have key : ∀ M (N : ℕ), N = Work.BoseFixB1B.groupedIdx M n' n'' →
      ∀ (Φ : Submission.BoseGases.X N → ℝ), ContDiff ℝ (⊤ : ℕ∞) Φ →
      (∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
        Φ x ≠ 0 → ∀ i : Fin N, x i ∈ Submission.BoseGases.dlBox
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
      ((M : ℝ) * G1 + G2) *
        (∫ x in Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (Φ x) ^ 2)
        ≤ Work.BoseFixB1B.sbWordCube v h μ u Φ := by
    intro M
    induction M with
    | zero =>
      intro N hN Φ hΦ hloc
      subst N
      have hb : G2 * (∫ x in Submission.BoseGases.abox n''
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Φ x) ^ 2)
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Φ := hB2 Φ hΦ hloc
      have hcoef : (((0 : ℕ) : ℝ) * G1 + G2) = G2 := by ring
      rw [hcoef]
      exact hb
    | succ M ih =>
      intro N hN Φ hΦ hin
      subst N
      change (((M + 1 : ℕ) : ℝ) * G1 + G2) *
          (∫ x in Submission.BoseGases.abox (n' + Work.BoseFixB1B.groupedIdx M n' n'')
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Φ x) ^ 2)
          ≤ Work.BoseFixB1B.sbWordCube v h μ u Φ
      have hstep := Work.BoseB1Cube.sbWordCube_descent_twoBlockAtSizes (v := v) h hv hv1 hvrad
        hR hv_supp hav hAdm hR16 hRχ u n' (Work.BoseFixB1B.groupedIdx M n' n'') G1
        ((M : ℝ) * G1 + G2) hB1
        (fun Ψ hΨ hloc => ih (Work.BoseFixB1B.groupedIdx M n' n'') rfl Ψ hΨ hloc) hΦ hin
      have hcoef : (((M + 1 : ℕ) : ℝ) * G1 + G2) = G1 + ((M : ℝ) * G1 + G2) := by
        push_cast; ring
      rw [hcoef]
      exact hstep
  have hN' : (m * n' + n'') = Work.BoseFixB1B.groupedIdx m n' n'' := by
    rw [Work.BoseFixB1B.groupedIdx_eq]
  exact key m (m * n' + n'') hN' Φ hΦ hin

end Work.BoseB1Cube

import ChallengeDeps
import Submission.Work.BoseFixB1B.sbWord_descent_grouped
import Submission.Work.BoseFixB1B.sbWord_descent_twoBlockAtSizes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

open MeasureTheory
open scoped Real Topology BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-!
# `Work.BoseFixB1B.sbWord_descent_atSizes` — FS Step E's descent at the *group sizes*

The iterated-block descent for the sliding-box word `sbWord` of FS `thm:smallbox`, in the form in
which the per-size lower bounds are available only at the two *group sizes* `n'` and `n''` of a
decomposition `N = m·n' + n''` of the particle number, rather than — as in
`Work.BoseFixB1B.sbWord_descent_grouped` — at every particle number.

The two ingredients are

* `Work.BoseFixB1B.sbWord_descent_twoBlockAtSizes` (the two-block descent at fixed block sizes
  `N1`, `N2`, whose proof is the proof of `sbWord_descent_twoBlock` transcribed to the at-sizes
  hypotheses), and
* the word-level grouping `Work.BoseFixB1B.sbWord_slice_superadd_regime_holds` (FS Step E) at the
  sliding box, which is used inside that two-block lemma.

The induction is carried out along the right-nested presentation `groupedIdx M n' n''` of the
particle number (its recursion `groupedIdx (M+1) n' n'' = n' + groupedIdx M n' n''` is
*definitional*, so that the block decomposition of the induction step syntactically matches
`mergeBlock`'s `N1 + N2`): peeling one block of `n'` coordinates at a time from an
`(m·n' + n'')`-particle state, each peeled block contributes `G1·∫Φ²` and the leftover block of
`n''` coordinates contributes `G2·∫Φ²`.  At every level of the induction the "second-block"
hypothesis is the *induction hypothesis itself* at the size `groupedIdx M n' n''` and the
"first-block" hypothesis is the given `hB1` at size `n'` — which is exactly why the at-sizes
hypotheses suffice.
-/

theorem sbWord_descent_atSizes {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
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
              (Ψ x) ^ 2) ≤ Work.BoseFixB1.sbWord h μ u Ψ)
    (hB2 : ∀ (Ψ : Submission.BoseGases.X n'' → ℝ), ContDiff ℝ (⊤ : ℕ∞) Ψ →
      (∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox n'' (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
        Ψ x ≠ 0 → ∀ i : Fin n'', x i ∈ Submission.BoseGases.dlBox
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
      G2 * (∫ x in Submission.BoseGases.abox n'' (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
              (Ψ x) ^ 2) ≤ Work.BoseFixB1.sbWord h μ u Ψ)
    {Φ : Submission.BoseGases.X (m * n' + n'') → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hin : ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (Submission.BoseGases.abox (m * n' + n'') (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
      Φ x ≠ 0 → ∀ i : Fin (m * n' + n''), x i ∈ Submission.BoseGases.dlBox
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :
    ((m : ℝ) * G1 + G2) * (∫ x in Submission.BoseGases.abox (m * n' + n'')
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Φ x) ^ 2)
      ≤ Work.BoseFixB1.sbWord h μ u Φ := by
  have key : ∀ M (N : ℕ), N = groupedIdx M n' n'' →
      ∀ (Φ : Submission.BoseGases.X N → ℝ), ContDiff ℝ (⊤ : ℕ∞) Φ →
      (∀ᵐ x ∂(MeasureTheory.volume.restrict
          (Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))),
        Φ x ≠ 0 → ∀ i : Fin N, x i ∈ Submission.BoseGases.dlBox
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) →
      ((M : ℝ) * G1 + G2) *
        (∫ x in Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (Φ x) ^ 2)
        ≤ Work.BoseFixB1.sbWord h μ u Φ := by
    intro M
    induction M with
    | zero =>
      intro N hN Φ hΦ hloc
      subst N
      have hb : G2 * (∫ x in Submission.BoseGases.abox n''
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Φ x) ^ 2)
          ≤ Work.BoseFixB1.sbWord h μ u Φ := hB2 Φ hΦ hloc
      have hcoef : (((0 : ℕ) : ℝ) * G1 + G2) = G2 := by ring
      rw [hcoef]
      exact hb
    | succ M ih =>
      intro N hN Φ hΦ hin
      subst N
      change (((M + 1 : ℕ) : ℝ) * G1 + G2) *
          (∫ x in Submission.BoseGases.abox (n' + groupedIdx M n' n'')
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Φ x) ^ 2)
          ≤ Work.BoseFixB1.sbWord h μ u Φ
      have hstep := sbWord_descent_twoBlockAtSizes (v := v) h hv hv1 hvrad hR hv_supp hav
        hAdm hR16 hRχ u n' (groupedIdx M n' n'') G1 ((M : ℝ) * G1 + G2) hB1
        (fun Ψ hΨ hloc => ih (groupedIdx M n' n'') rfl Ψ hΨ hloc) hΦ hin
      have hcoef : (((M + 1 : ℕ) : ℝ) * G1 + G2) = G1 + ((M : ℝ) * G1 + G2) := by
        push_cast; ring
      rw [hcoef]
      exact hstep
  have hN' : (m * n' + n'') = groupedIdx m n' n'' := by rw [groupedIdx_eq]
  exact key m (m * n' + n'') hN' Φ hΦ hin


end

end Work.BoseFixB1B

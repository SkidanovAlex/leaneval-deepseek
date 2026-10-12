import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.box_to_model_glue
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- The three-line arithmetic of the assembly (`BRIDGE_DESIGN.md` §4).  Let `w = wordB`,
`νB = normB`, `r = w/νB`, `νΨ = bomb Ψ Ψ`, `q = bomb Ψ (H2ndHon Ψ)`, `E` the total error
scale of the bridge, `Ē = errKafz v R μ C`.  Then

* `hW` : `w ≤ r·νB` (this is `IsLowB` once `r = ℓ³Θ` and `ℓ³Θ ≤ 0`),
* `hq` : `q ≤ w + E·νB` (this is BF3a + BF3b),
* `hν` : `νΨ ≤ νB` (the contraction of the compression),
* `hrĒ` : `r + Ē ≤ 0` (the a-priori threshold beats `errKafz`, `err_arith`),
* `hEE` : `E ≤ Ē` (`errB ≤ errKafz`, `err_arith`),

give `q ≤ (r + Ē)·νΨ`. -/
lemma assembly_arith {r νB νΨ q w E Ē : ℝ} (hνB0 : 0 ≤ νB) (hν : νΨ ≤ νB)
    (hrĒ : r + Ē ≤ 0) (hEE : E ≤ Ē) (hw : w ≤ r * νB) (hq : q ≤ w + E * νB) :
    q ≤ (r + Ē) * νΨ := by
  have h1 : q ≤ (r + E) * νB := by
    have h2 : w + E * νB ≤ r * νB + E * νB := by linarith
    have h3 : r * νB + E * νB = (r + E) * νB := by ring
    linarith
  have h4 : (r + E) * νB ≤ (r + Ē) * νB :=
    mul_le_mul_of_nonneg_right (by linarith) hνB0
  have h5 : (r + Ē) * νB ≤ (r + Ē) * νΨ := mul_le_mul_of_nonpos_left hν hrĒ
  linarith

/-- `IsLowB` in the quotient form used by `assembly_arith`:
`wordB/normB ≤ ℓ³Θ(a,J,μ)`. -/
lemma islowB_ratio_le {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {J μ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hJ : Work.BoseBoxFix.IsLowB v h J μ n Φ)
    (h0 : 0 < Work.BoseBoxFix.normB v μ n Φ) :
    Work.BoseBoxFix.wordB v h μ n Φ / Work.BoseBoxFix.normB v μ n Φ
      ≤ Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 * Work.UBB.Theta (BoseGases.a v) J μ := by
  rw [Work.BoseBoxFix.IsLowB] at hJ
  rw [div_le_iff₀ h0]
  exact hJ

theorem box_to_model (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ)
    (hB3 : Work.BoseBoxFix.NodeB3B v h R fc) :
    ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ HM : ∀ μ : ℝ, HonestModes v μ, (∀ μ, Nmin μ ≤ (HM μ).N) →
        ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
          J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
          ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
            (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
            0 < Work.BoseBoxFix.normB v μ n Φ →
            Work.BoseBoxFix.IsLowB v h J μ n Φ →
            Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
              (Φ : Submission.BoseGases.X n → ℝ) →
            ∃ Ψ : Work.BoseB4.RealFock (HM μ).m, Ψ ≠ 0 ∧
              ExcWindow (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v))
                (BoseGases.a v) μ) n Ψ ∧
              Work.BoseB4.bomb (HM μ).m Ψ (H2ndHon v h fc fu HM μ Ψ)
                ≤ (Work.BoseBoxFix.wordB v h μ n Φ / Work.BoseBoxFix.normB v μ n Φ
                    + Work.BoseFixR.errKafz v R μ C)
                    * Work.BoseB4.bomb (HM μ).m Ψ Ψ := by
  -- the assembly (`Submission/Work/BoseBoxFock/box_to_model_glue.lean`): the BF3c selection
  -- chain at the box restriction `Φ·1_abox` (`Submission/Work/MB/`), FS's row comparison
  -- `bf3a` and `err_arith`, and the single analytic input
  -- `Work.BoseBoxFock.FormW2B_holds` (FS `prop:Hamilton2ndQuant`'s row table).
  exact box_to_model_assembled v h hv hv1 hvrad hR hv_supp hav fc fu J hB3

end Work.BoseBoxFock

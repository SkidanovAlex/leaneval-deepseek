import ChallengeDeps
import Submission.Work.PCFU.chDkernel_le
import Submission.Work.PCFU.chDslot_le_of_kernel
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

theorem chDslot_le (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut) (J ε₀ : ℝ) :
    Work.BoseBoxFock.SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => Work.BoseBoxFock.PCFU.chDslot v h fc fu μ N i j Θ) := by
  have hred : ∀ (μ : ℝ), 0 < μ → ∀ (N n : ℕ), ∀ (i j : Fin n), i ≠ j →
      ∀ (Φ : Submission.BoseGases.X n → ℝ),
        MeasureTheory.IntegrableOn (fun x => (Φ x) ^ 2)
            (Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)) →
        ∀ {K : ℝ}, 0 ≤ K →
          (∀ z : EuclideanSpace ℝ (Fin 3), ‖(((Work.BoseK15.corpusBox.chiLam
                (Work.BoseBoxFock.ellH v μ) z : ℝ)) : ℂ)
              * (Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
                  - Work.BoseBoxFock.PCFU.chDC h (Work.BoseBoxFock.ellH v μ) z)‖ ≤ K) →
          ‖Work.BoseBoxFock.PCFU.chDslot v h fc fu μ N i j
              (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Φ)‖
            ≤ K * (Work.BoseBoxFock.ellH v μ) ^ 3 * Work.BoseBoxFix.normB v μ n Φ :=
    fun μ hμ N n i j hij Φ hΦ K hK hz =>
      Work.PCFU.chDslot_le_of_kernel hij hav hμ fc fu N hK hΦ hz
  by_cases hε₀ : 0 < ε₀
  · obtain ⟨K0, T, hK0, hk⟩ :=
      Work.PCFU.chDkernel_le (v := v) (h := h) hv hvrad hR hv_supp hav fu hε₀
    exact Work.BoseBoxFock.PCFU.chDslot_le_of_kernelBound v h hv hv1 hvrad hR hv_supp hav
      fc fu J ε₀ hK0 hred hk
  · have hε₀le : ε₀ ≤ 0 := le_of_not_gt hε₀
    refine Work.BoseBoxFock.PCFU.chDslot_le_of_kernelBound v h hv hv1 hvrad hR hv_supp hav
      fc fu J ε₀ (K0 := 1) (T := fun _ => 1) one_pos hred ?_
    intro μ hμ hAdm hRℓ h4R N hTN z
    exfalso
    have hμa : μ * (BoseGases.a v) ^ 3 ≤ ε₀ := hAdm.2.1
    have hpos : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
    linarith

end Work.BoseBoxFock.PCFU

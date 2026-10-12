import ChallengeDeps
import Submission.Work.BoseBoxFock.PCFU._cslot_asm
import Submission.Work.BoseBoxFock.PCFU.chCslot_kernelPair
import Submission.Work.BoseBoxFock.PCFU.chCslot_le_of_pairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

/-- The `(C)`-slot piece, assembled from the two halves `chCslot_le_of_pairing` (the reduction of
the slot to the χ-weighted *pairing* bound `ChKerPair` on the alias kernel `D = KfrU − ℓ³W₁`) and
`chCslot_kernelPair` (that pairing bound).  The *pointwise* form of the kernel estimate is false
(at a jump of `W₁` the mollification `uvSmear ⋆ W₁` does not converge to `W₁` uniformly), which is
why the pairing form is the correct one. -/
theorem chCslot_le (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut) (J ε₀ : ℝ) :
    Work.BoseBoxFock.SlotPiece v h fc fu R J ε₀
      (fun n μ N i j Θ => Work.BoseBoxFock.PCFU.chCslot v h fc fu μ N i j Θ) := by
  obtain ⟨C, hC, hAk⟩ := chCslot_le_of_pairing v h hv hv1 hvrad hR hv_supp hav fc fu
  obtain ⟨C', hC', hBk⟩ := chCslot_kernelPair v h hv hv1 hvrad hR hv_supp hav fu
  exact chCslot_le_of_children v h hv hv1 hvrad hR hv_supp hav fc fu J ε₀
    ⟨C, hC, hAk⟩ ⟨C', hC', hBk⟩

end Work.BoseBoxFock.PCFU

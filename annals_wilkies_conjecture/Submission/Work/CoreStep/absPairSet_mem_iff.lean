import Mathlib
import Submission.Work.WilE7.CoreStep.GermDefs
import Submission.Work.WilE7.fiberProduct_semiPf

namespace Work.CoreStep

theorem absPairSet_mem_iff {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (w : Fin (0 + Work.WilE7.CoreStep.pPair n m) → ℝ) :
    w ∈ (Work.WilE7.CoreStep.absPairSet T).set ↔
      Work.WilE7.CoreStep.absPtUp (WilkiesDesign.E.projFirst (n + (m + 1)) (n + (m + 1))
          (Work.WilE7.MainDesign.absPt w)) ∈ T.X.set ∧
      Work.WilE7.CoreStep.absPtUp (WilkiesDesign.E.projSnd (n + (m + 1)) (n + (m + 1))
          (Work.WilE7.MainDesign.absPt w)) ∈ T.X.set ∧
      WilkiesDesign.E.projFirst n (m + 1) (WilkiesDesign.E.projFirst (n + (m + 1)) (n + (m + 1))
          (Work.WilE7.MainDesign.absPt w)) =
        WilkiesDesign.E.projFirst n (m + 1) (WilkiesDesign.E.projSnd (n + (m + 1)) (n + (m + 1))
          (Work.WilE7.MainDesign.absPt w)) := by
  have hz : (fun i => w ((Work.WilE7.finEquiv
        (Nat.zero_add (Work.WilE7.CoreStep.pPair n m))).symm i))
      = Work.WilE7.MainDesign.absPt w := by
    funext i
    exact congrArg w (Fin.ext rfl)
  rw [Work.WilE7.CoreStep.absPairSet, Work.WilE7.sp_reindex_set]
  simp only [Set.mem_setOf_eq]
  rw [hz, Work.WilE7.fiberProdZ_set]
  simp only [Set.mem_setOf_eq]
  rw [Work.WilE7.CoreStep.mem_absReindex, Work.WilE7.CoreStep.mem_absReindex]

end Work.CoreStep

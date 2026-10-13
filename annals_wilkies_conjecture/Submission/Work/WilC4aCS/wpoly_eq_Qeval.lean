import Mathlib
import Submission.Work.WilC4aCS.Defs

namespace Work.WilC4aCS

theorem wpoly_eq_Qeval {n K : ℕ} (d : Fin K → ℕ)
    (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ) (x' : Fin n → ℝ) (z : ℝ) (i : Fin K) :
    WilkiesDesign.CG.C4a.wpoly (a i) (Fin.snoc x' z)
      = Work.WilC4aCS.Qeval d (Work.WilC4aCS.coefFun d a x') z i := by
  rw [WilkiesDesign.CG.C4a.wpoly, Work.WilC4aCS.Qeval, Fin.snoc_last, Fin.init_snoc]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Work.WilC4aCS.coefFun, Work.WilC4aCS.coefIdx, Equiv.symm_apply_apply]

end Work.WilC4aCS

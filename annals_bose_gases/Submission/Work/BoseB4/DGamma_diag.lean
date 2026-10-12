import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB4.DGamma
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB4

theorem DGamma_diag {m : ℕ} (T : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (lam : Fin m → ℝ)
    (h : ∀ i : Fin m, T (Work.BoseB4.evec m i) = lam i • Work.BoseB4.evec m i) :
    Work.BoseB4.dGamma m T = ∑ i : Fin m, lam i • Work.BoseB4.modeNumOp m i := by
  rw [dGamma]
  simp only [modeNumOp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  have hcoef : T (evec m y) y = lam y := by
    rw [h y]; simp [evec]
  rw [← hcoef]
  refine Finset.sum_eq_single y (fun b _ hb => ?_) (fun hy => absurd (Finset.mem_univ y) hy)
  rw [h y]
  simp [evec, hb]

end Work.BoseB4

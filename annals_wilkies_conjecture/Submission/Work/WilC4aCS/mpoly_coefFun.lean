import Mathlib
import Submission.Work.WilC4aCS.Defs

namespace Work.WilC4aCS

theorem mpoly_coefFun {n : ℕ} {l : ℕ} (d : Fin (l + 1) → ℕ)
    (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ) (γ : ℝ → Fin n → ℝ) (s z : ℝ) (i : Fin (l + 1)) :
    WilkiesDesign.CG.C4a.mpoly (fun (j : Fin (d i)) (_ : ℝ) => a i j (γ s)) s z
      = Work.WilC4aCS.Qeval d (Work.WilC4aCS.coefFun d a (γ s)) z i := by
  unfold WilkiesDesign.CG.C4a.mpoly Work.WilC4aCS.Qeval Work.WilC4aCS.coefFun Work.WilC4aCS.coefIdx
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Equiv.symm_apply_apply]

end Work.WilC4aCS

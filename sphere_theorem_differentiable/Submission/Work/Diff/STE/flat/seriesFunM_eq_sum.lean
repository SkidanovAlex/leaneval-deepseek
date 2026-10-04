import Mathlib
import Submission.Work.Diff.STE.flat.GalerkinDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

theorem seriesFunM_eq_sum {n N : ℕ} (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ Work.Diff.STE.Flat.box n N → c k = 0)
    (x : Fin n → ℝ) (i j : Fin n) :
    Work.Diff.STE.Flat.seriesFunM c x i j
      = ∑ m : Work.Diff.STE.Flat.box n N, c m.1 i j * Work.Diff.STE.fourierExp m.1 x := by
  rw [Work.Diff.STE.Flat.seriesFunM_apply, Work.Diff.STE.seriesFun]
  rw [tsum_eq_sum (s := Work.Diff.STE.Flat.box n N)
        (f := fun k => c k i j * Work.Diff.STE.fourierExp k x)
        (fun k hk => by simp [hc k hk])]
  exact (Finset.sum_attach (Work.Diff.STE.Flat.box n N)
    (fun m => c m i j * Work.Diff.STE.fourierExp m x)).symm

end Work.Diff.STE.flat

import Mathlib
import Submission.Work.WilE7.coreLT_succ.SwapEquiv0
import Submission.Work.CoreStep.StratReindexDefs

namespace Work.WilE7.coreLT_succ

open WilkiesDesign WilkiesDesign.E

theorem projTop_absPt_reindex {n m : ℕ} (Y : WilkiesDesign.E.SemiPf (0 + ((n + 1) + m))) :
    Work.WilE7.CoreStep.projTop n m ''
        (Work.WilE7.MainDesign.absPt ''
          (Work.WilE7.SemiPf.reindex (Work.WilE7.coreLT_succ.swapEquiv0 n m) Y).set)
      = WilkiesDesign.E.projFirst (n + 1) m ''
          (Work.WilE7.MainDesign.absPt '' Y.set) := by
  apply Set.Subset.antisymm
  · rintro x ⟨w', ⟨w, hw, rfl⟩, rfl⟩
    have hw' : (fun i : Fin (0 + ((n + 1) + m)) => w ((swapEquiv0 n m) i)) ∈ Y.set :=
      (Work.WilE7.sp_reindex_mem (swapEquiv0 n m) Y w).mp hw
    refine ⟨Work.WilE7.MainDesign.absPt
        (fun i : Fin (0 + ((n + 1) + m)) => w ((swapEquiv0 n m) i)),
      ⟨(fun i : Fin (0 + ((n + 1) + m)) => w ((swapEquiv0 n m) i)), hw', rfl⟩, ?_⟩
    have h1 : Work.WilE7.CoreStep.projTop n m (Work.WilE7.MainDesign.absPt w) =
        Work.WilE7.MainDesign.basePrLin (n + 1) m
          (fun i : Fin (0 + ((n + 1) + m)) => w ((swapEquiv0 n m) i)) := by
      have h := projTop_absPt_swapEquiv0 n m
        (fun i : Fin (0 + ((n + 1) + m)) => w ((swapEquiv0 n m) i))
      rwa [show (fun i : Fin (0 + (n + (m + 1))) =>
            (fun i : Fin (0 + ((n + 1) + m)) => w ((swapEquiv0 n m) i))
              ((swapEquiv0 n m).symm i)) = w from funext fun j => by simp] at h
    rw [projFirst_absPt_eq_basePrLin, h1]
  · rintro x ⟨u, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨Work.WilE7.MainDesign.absPt
        (fun j : Fin (0 + (n + (m + 1))) => z ((swapEquiv0 n m).symm j)),
      ⟨(fun j : Fin (0 + (n + (m + 1))) => z ((swapEquiv0 n m).symm j)), ?_, rfl⟩, ?_⟩
    · rw [Work.WilE7.sp_reindex_mem]
      rwa [show (fun i : Fin (0 + ((n + 1) + m)) =>
            (fun j : Fin (0 + (n + (m + 1))) => z ((swapEquiv0 n m).symm j))
              ((swapEquiv0 n m) i)) = z from funext fun i => by simp]
    · rw [projTop_absPt_swapEquiv0, projFirst_absPt_eq_basePrLin]

end Work.WilE7.coreLT_succ

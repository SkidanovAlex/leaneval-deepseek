import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.cut_defs
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLC6Core.mem_VThick_frontier_of_mem_of_not_mem
import Submission.Work.EKLC6Core.cutHUnipotent
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.atom_partSigma_finPart

namespace Work.EKLC6Core

open Work.EKLContract

theorem Uball_uminus_subset_shape_of_avoid {N : ℕ} (Q : Fin N → Set Work.EKLContract.X3)
    (hdisj : ∀ i j : Fin N, i ≠ j → Disjoint (Q i) (Q j))
    (t : Fin 3 → ℝ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    {y : Work.EKLContract.X3} {i : Fin N} (hy : y ∈ interior (Q i))
    (havoid : y ∉ Work.EKLC6Core.VThick (1000 * η) (⋃ j : Fin N, frontier (Q j)))
    (P : @Work.EKLContract.FinPart Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3)
    (k : Fin P.n) (hPk : P.parts k = interior (Q i)) :
    Work.EKLComp.Uball (Work.EKLC6Core.Uminus t) η ⊆
      Work.EKLContract.shape (Work.EKLContract.partSigma P)
        (Work.EKLC6Core.Uminus t) y := by
  intro g hg
  obtain ⟨hgU, hgV⟩ := hg
  have hyP : y ∈ P.parts k := by rw [hPk]; exact hy
  refine ⟨hgU, ?_⟩
  rw [atom_partSigma_finPart P hyP, hPk]
  by_contra hnot
  have huni : ∀ u ∈ Uminus t, ((u : Matrix (Fin 3) (Fin 3) ℝ) - 1) ^ 3 = 0 :=
    cutHUnipotent (uminus_isHoro t).2
  have hfr : y ∈ VThick (20 * η) (frontier (interior (Q i))) :=
    mem_VThick_frontier_of_mem_of_not_mem (U := Uminus t) huni isOpen_interior hη hη1 g
      hgU hgV (Or.inl ⟨hy, hnot⟩)
  apply havoid
  refine VThick_mono_right ?_ (1000 * η) (VThick_mono_left ?_ _ hfr)
  · exact le_trans frontier_interior_subset (Set.subset_iUnion (fun j : Fin N => frontier (Q j)) i)
  · linarith [hη.le]

end Work.EKLC6Core

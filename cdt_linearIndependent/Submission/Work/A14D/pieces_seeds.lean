import Mathlib
import Submission.Work.A14D.su_om1_pieces

/-!
# `Work.A14D.pieces_seeds`

The eight explicit points of `Submission.Work.A14D.su_om1_pieces` are seeds for the four
solutions of the linear ODE and for the agreement tests on the overlaps. This file records the
elementary location facts: each `pt*` lies in its piece and in `SU \ {2}`, and each `q**` lies in
the intersection of the two pieces it is named for, again inside `SU \ {2}`.
-/

namespace Work.A14D

/-- Every named seed point lies in the piece(s) it is named for, inside `SU \ {2}`. -/
theorem pieces_seeds :
    Work.A14D.ptU ∈ Work.A14D.pieceU ∩ (Work.A14D.SU \ ({2} : Set ℂ)) ∧
    Work.A14D.ptD ∈ Work.A14D.pieceD ∩ (Work.A14D.SU \ ({2} : Set ℂ)) ∧
    Work.A14D.pt1 ∈ Work.A14D.piece1 ∩ (Work.A14D.SU \ ({2} : Set ℂ)) ∧
    Work.A14D.pt2 ∈ Work.A14D.piece2 ∩ (Work.A14D.SU \ ({2} : Set ℂ)) ∧
    Work.A14D.qU1 ∈ Work.A14D.pieceU ∩ Work.A14D.piece1 ∩ (Work.A14D.SU \ ({2} : Set ℂ)) ∧
    Work.A14D.qD1 ∈ Work.A14D.pieceD ∩ Work.A14D.piece1 ∩ (Work.A14D.SU \ ({2} : Set ℂ)) ∧
    Work.A14D.qU2 ∈ Work.A14D.pieceU ∩ Work.A14D.piece2 ∩ (Work.A14D.SU \ ({2} : Set ℂ)) ∧
    Work.A14D.qD2 ∈ Work.A14D.pieceD ∩ Work.A14D.piece2 ∩ (Work.A14D.SU \ ({2} : Set ℂ)) := by
  simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    Work.A14D.pieceU, Work.A14D.pieceD, Work.A14D.piece1, Work.A14D.piece2, Work.A14D.SU,
    Work.A14D.ptU, Work.A14D.ptD, Work.A14D.pt1, Work.A14D.pt2,
    Work.A14D.qU1, Work.A14D.qD1, Work.A14D.qU2, Work.A14D.qD2, Complex.ext_iff]
  norm_num

end Work.A14D

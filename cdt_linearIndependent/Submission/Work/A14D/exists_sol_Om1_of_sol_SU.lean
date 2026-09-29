import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.om1_geometry
import Submission.Work.A14D.su_om1_pieces
import Submission.Work.C17g.linear_ode_convex
import Submission.Work.OdeCont.uniqueness
import Submission.Work.A14D.asm_om1_ext

namespace Work.A14D

theorem exists_sol_Om1_of_sol_SU {k : ℕ} (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ)
    (hA : ∀ i j, DifferentiableOn ℂ (fun z => A z i j) (Work.A14D.Om1 \ ({2} : Set ℂ)))
    (hb : ∀ i, DifferentiableOn ℂ (fun z => b z i) (Work.A14D.Om1 \ ({2} : Set ℂ)))
    {Y : ℂ → Fin k → ℂ} (hYd : DifferentiableOn ℂ Y (Work.A14D.SU \ ({2} : Set ℂ)))
    (hY : ∀ z ∈ Work.A14D.SU \ ({2} : Set ℂ),
      HasDerivAt Y (fun i => Finset.univ.sum (fun j => A z i j * Y z j) + b z i) z) :
    ∃ G : ℂ → Fin k → ℂ, DifferentiableOn ℂ G (Work.A14D.Om1 \ ({2} : Set ℂ)) ∧
      (∀ z ∈ Work.A14D.Om1 \ ({2} : Set ℂ),
        HasDerivAt G (fun i => Finset.univ.sum (fun j => A z i j * G z j) + b z i) z) ∧
      Set.EqOn G Y (Work.A14D.SU \ ({2} : Set ℂ)) :=
  Work.A14D.asm_exists_sol_Om1_of_sol_SU A b hA hb hYd hY

end Work.A14D

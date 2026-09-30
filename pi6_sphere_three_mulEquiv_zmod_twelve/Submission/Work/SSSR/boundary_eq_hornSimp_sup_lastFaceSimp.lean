import Mathlib
import Submission.Work.SSSR.serreE1PieceDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

namespace Work.SSSR

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
/-- The boundary `∂Δ[s]` is the union of the horn `Λ` (the faces `d_iΔ[s]` for `i < s`) with the
last face `d_sΔ[s]`. -/
theorem boundary_eq_hornSimp_sup_lastFaceSimp (s : ℕ) :
    SSet.boundary s = Work.SSSR.hornSimp s ⊔ Work.SSSR.lastFaceSimp s := by
  rw [SSet.boundary_eq_iSup, hornSimp, lastFaceSimp]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun i => ?_
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact le_sup_of_le_left
        (le_iSup (fun j : Fin s =>
          SSet.stdSimplex.face ({j.castSucc} : Finset (Fin (s + 1)))ᶜ) j)
    · exact le_sup_of_le_right le_rfl
  · refine sup_le ?_ ?_
    · exact iSup_le fun j =>
        le_iSup (fun i : Fin (s + 1) =>
          SSet.stdSimplex.face ({i} : Finset (Fin (s + 1)))ᶜ) j.castSucc
    · exact le_iSup (fun i : Fin (s + 1) =>
        SSet.stdSimplex.face ({i} : Finset (Fin (s + 1)))ᶜ) (Fin.last s)

end Work.SSSR

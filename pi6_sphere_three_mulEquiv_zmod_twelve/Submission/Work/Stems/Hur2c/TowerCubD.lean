import Submission.Work.Stems.Hur2c.DegenDefs
import Submission.Work.RatHurewicz.fillingFamilyConst

/-!
# The boundary of a tower filling

`Work.RatHurewicz.Tower` (from `fillingFamilyConst`) is the cubical filling family of Hutchings'
Hurewicz construction: `K.Kf m p` is an `(m+1)`-cube whose top face is `p`, whose bottom face is
the constant cube at `x₀`, and whose side faces are `K.Kf (m-1)` applied to the faces of `p`.

Here we record the resulting *chain-level* identity: the boundary of the filling of `p` is the
filling of the boundary of `p` plus the difference between `p` and the constant cube.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.Stems.Hur2c

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- **The boundary of a tower filling.** -/
theorem tower_cubD_identity {x₀ : X} {N : ℕ}
    (K : Work.RatHurewicz.Tower x₀ N) (m : ℕ) (hm : m + 1 ≤ N)
    (p : C(IC (m + 1), X)) :
    cubD (m + 1) X (Finsupp.single (K.Kf (m + 1) p) 1)
      = (∑ j : Fin (m + 1), (-1 : ℤ) ^ (j : ℕ) •
          (Finsupp.single (K.Kf m (faceCube j 0 p)) 1
            - Finsupp.single (K.Kf m (faceCube j 1 p)) 1))
        + (-1 : ℤ) ^ (m + 1) • (Finsupp.single (Work.RatHurewicz.cconst (m + 1) x₀) 1
            - Finsupp.single p 1) := by
  rw [cubD_single, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    simp only [faceCube]
    rw [(K.hβ m hm p j).1, (K.hβ m hm p j).2]
    rfl
  · simp only [faceCube, Fin.val_last]
    rw [(K.hα (m + 1) hm p).2, (K.hα (m + 1) hm p).1]

end

end Work.Stems.Hur2c

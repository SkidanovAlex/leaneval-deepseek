import Mathlib
import Submission.Work.WilE9.Sharp.AE.Basic
import Submission.Work.WilE9.Sharp.exSemiPf_base
import Submission.Work.WilE9.Sharp.AE.exStrat_mem

namespace Work.WilE9.Sharp.AE

/-- **Soundness of the component-restricted extended set.**  Every point of `exComp n m E q L` has
stratum coordinates in the prescribed component `connectedComponentIn E.X.set q` of the stratum's
set.

`exComp` is the union of the components of `(exSemiPf n m E L).set` through the points whose
stratum coordinates lie in `connectedComponentIn E.X.set q`.  For such a point `z`, the stratum
coordinates of the whole component (and in particular of `z` itself) lie in the component of
`exStrat w` for any `w` of the component (`exStrat_image_componentIn`), and that component is
`connectedComponentIn E.X.set q` because `exStrat w` lies in it (`connectedComponentIn_eq`). -/
theorem exStrat_mem_comp_of_mem_exComp {n m : ℕ} (E : Work.WilE9.Sharp.EffStratum n m)
    (q : Fin (n + (1 + m)) → ℝ) (L : List (Fin n))
    {z : Fin (Work.WilE9.Sharp.Next n m) → ℝ} (hz : z ∈ Work.WilE9.Sharp.exComp n m E q L) :
    Work.WilE9.Sharp.exStrat z ∈ connectedComponentIn E.X.set q := by
  simp only [Work.WilE9.Sharp.exComp, Set.mem_iUnion, Set.mem_ofPred_eq] at hz
  obtain ⟨w, ⟨hwset, hwcomp⟩, hwcc⟩ := hz
  have hzw : Work.WilE9.Sharp.exStrat z ∈
      connectedComponentIn E.X.set (Work.WilE9.Sharp.exStrat w) :=
    Work.WilE9.Sharp.exStrat_image_componentIn E L hwset ⟨z, hwcc, rfl⟩
  rw [connectedComponentIn_eq hwcomp]
  exact hzw

end Work.WilE9.Sharp.AE

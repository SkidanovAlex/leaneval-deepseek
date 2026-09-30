import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.NullBord.setup
import Submission.Work.ThomBordism.NullBord.enr
import Submission.Work.ThomBordism.NullBord.localNearest

namespace Work.ThomBordism

theorem homologyFiniteOfNullBordism {ι : Type} [Fintype ι] {F : ι → Work.ThomBordism.Man8}
    (W : Work.ThomBordism.NullBordismFamily ι F) (k : ℕ) :
    Module.Finite ℤ ((Work.Cohomology.chainC ℤ
      (TopCat.toSSet.obj (TopCat.of W.W))).homology k) := by
  obtain ⟨N, e, he, hemb, hinj⟩ := NullBord.exists_immersion_closedEmbedding (X := W.W)
  exact NullBord.homologyFinite_of_enr (X := W.W) hemb
    (NullBord.enrRetraction (X := W.W) hemb
      (fun x₀ => NullBord.localNearestUnique e he hinj x₀)) k

end Work.ThomBordism

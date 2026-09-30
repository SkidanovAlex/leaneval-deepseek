import Mathlib
import Submission.Work.Cohomology.cup1Cast
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

/-- `Fface`/`Gface` in degrees `(n+1, m)`, composed with the degree identification
`(n+1)+m-1 = n+m`, are the interval maps `Wmap`/`Ymap`. -/
theorem shmapFface (n m s : ℕ) (hs : s < m) (h : (n+1)+m-1 = n+m) :
    (CategoryTheory.CategoryStruct.comp (Work.Cohomology.Fface (n+1) m s (by omega))
        (Work.Cohomology.shmap ((n+1)+m-1) (n+m) h)
        = Work.Cohomology.Wmap n m s (by omega))
    ∧ (CategoryTheory.CategoryStruct.comp (Work.Cohomology.Gface (n+1) m s (by omega))
        (Work.Cohomology.shmap ((n+1)+m-1) (n+m) h)
        = Work.Cohomology.Ymap n m s (by omega)) := by
  constructor
  · refine ConcreteCategory.hom_ext _ _ (fun i => ?_)
    apply Fin.ext
    rw [CategoryTheory.comp_apply]
    simp only [Work.Cohomology.shmap_val, Work.Cohomology.Fface_val, Work.Cohomology.Wmap_val]
  · refine ConcreteCategory.hom_ext _ _ (fun j => ?_)
    apply Fin.ext
    rw [CategoryTheory.comp_apply]
    simp only [Work.Cohomology.shmap_val, Work.Cohomology.Gface_apply]
    rw [Work.Cohomology.Gfun_val_if, Work.Cohomology.Ymap_val_if]
    split_ifs <;> omega

theorem cup1ShiftedLeftR (R : Type) [CommRing R] (X : SSet) (n m : ℕ)
    (α : Work.Cohomology.Cochain R X n) (β : Work.Cohomology.Cochain R X m)
    (h1 : (n+1)+m-1 = n+m) (σ : X.obj (Opposite.op (SimplexCategory.mk (n+m)))) :
    Work.Cohomology.genEval R X
        (Work.Cohomology.cup1 R X (n+1) m (Work.Cohomology.cochainDiff R X α) β)
        (X.map (Work.Cohomology.shmap ((n+1)+m-1) (n+m) h1).op σ)
      = ∑ s : Fin m, ((-1:R)^(s.val*((n+1)+1)+((n+1)))) *
          Work.Cohomology.genEval R X (Work.Cohomology.cochainDiff R X α)
            (X.map (Work.Cohomology.Wmap n m s.val (by have := s.isLt; omega)).op σ) *
          Work.Cohomology.genEval R X β
            (X.map (Work.Cohomology.Ymap n m s.val (by have := s.isLt; omega)).op σ) := by
  rw [Work.Cohomology.genEval_cup1]
  refine Finset.sum_congr rfl fun s _ => ?_
  obtain ⟨hf, hg⟩ := shmapFface n m s.val s.isLt h1
  rw [Work.Cohomology.mop (Work.Cohomology.shmap ((n+1)+m-1) (n+m) h1)
        (Work.Cohomology.Fface (n+1) m s.val (by have := s.isLt; omega)) σ, hf,
      Work.Cohomology.mop (Work.Cohomology.shmap ((n+1)+m-1) (n+m) h1)
        (Work.Cohomology.Gface (n+1) m s.val (by have := s.isLt; omega)) σ, hg]

end

end Work.Pi6.SQM

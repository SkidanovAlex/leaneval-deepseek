import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank

universe u

namespace Work.ORHughesFree.NaturalExtension

open Work.ORHughesFree

/-- Transport of Sylvester rank functions along a ring isomorphism: if `e : A ≃+* B` and `rk` is a
Sylvester matrix rank function on `A`, then `M ↦ rk (M.map e.symm)` is a Sylvester matrix rank
function on `B`. -/
theorem sylvesterRank_exists_transport {A B : Type u} [Ring A] [Ring B] (e : A ≃+* B)
    (rk : Work.ORHughesFree.SylvesterRank A) :
    ∃ rkB : Work.ORHughesFree.SylvesterRank B, ∀ (n m : ℕ) (M : Matrix (Fin n) (Fin m) B),
      rkB.rk n m M = rk.rk n m (M.map ⇑e.symm) := by
  refine ⟨{ rk := fun n m M => rk.rk n m (M.map ⇑e.symm),
            rk_nonneg := fun n m M => rk.rk_nonneg n m _,
            rk_zero := fun n m => ?_,
            rk_one := ?_,
            rk_mul_le_left := fun X Y => ?_,
            rk_mul_le_right := fun X Y => ?_,
            rk_blockDiag := fun X Y => ?_,
            rk_blockUpper := fun X Y Z => ?_ }, fun n m M => rfl⟩
  · rw [show (0 : Matrix (Fin n) (Fin m) B).map ⇑e.symm = 0 from
      Matrix.map_zero ⇑e.symm (map_zero e.symm)]
    exact rk.rk_zero n m
  · rw [show (1 : Matrix (Fin 1) (Fin 1) B).map ⇑e.symm = 1 from
      Matrix.map_one ⇑e.symm (map_zero e.symm) (map_one e.symm)]
    exact rk.rk_one
  · rw [show (X * Y).map ⇑e.symm = X.map ⇑e.symm * Y.map ⇑e.symm from
      Matrix.map_mul (f := (e.symm : B →+* A))]
    exact rk.rk_mul_le_left _ _
  · rw [show (X * Y).map ⇑e.symm = X.map ⇑e.symm * Y.map ⇑e.symm from
      Matrix.map_mul (f := (e.symm : B →+* A))]
    exact rk.rk_mul_le_right _ _
  · rw [show (blockDiagFin X Y).map ⇑e.symm
        = blockDiagFin (X.map ⇑e.symm) (Y.map ⇑e.symm) from
      blockDiagFin_map (e.symm : B →+* A) X Y]
    exact rk.rk_blockDiag _ _
  · rw [show (blockUpperFin X Y Z).map ⇑e.symm
        = blockUpperFin (X.map ⇑e.symm) (Y.map ⇑e.symm) (Z.map ⇑e.symm) from
      blockUpperFin_map (e.symm : B →+* A) X Y Z]
    exact rk.rk_blockUpper _ _ _

end Work.ORHughesFree.NaturalExtension

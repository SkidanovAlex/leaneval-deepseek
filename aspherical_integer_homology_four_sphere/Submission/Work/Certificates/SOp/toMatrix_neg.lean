import Mathlib
import Submission.Work.Certificates.Sparse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Certificates.SOp

/-- `toFun` respects negation of a sparse vector: negating every coefficient negates the
represented function `Fin n → ℤ`. -/
private theorem toFun_map_neg {n : ℕ} (v : SVec n) :
    SVec.toFun (v.map (fun p => (p.1, -p.2))) = -SVec.toFun v := by
  funext i
  simp only [SVec.toFun, List.map_map, Pi.neg_apply]
  rw [List.map_congr_left (l := v)
      (g := fun p => -(if p.1 = i then p.2 else 0))
      (fun a _ => by by_cases h : a.1 = i <;> simp [h])]
  have h : (List.map (fun x => -x) (List.map (fun p => if p.1 = i then p.2 else 0) v))
      = List.map (fun p => -(if p.1 = i then p.2 else 0)) v := by
    rw [List.map_map]; rfl
  rw [← h]
  exact (List.sum_neg _).symm

/-- The matrix of the negation of a sparse operator is the negation of its matrix. -/
theorem toMatrix_neg {n m : ℕ} (A : SOp n m) : toMatrix (neg A) = -toMatrix A := by
  ext i j
  simp only [toMatrix, neg, Matrix.neg_apply, Pi.neg_apply, toFun_map_neg]

end Work.Certificates.SOp

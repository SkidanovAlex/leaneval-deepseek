import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Conic.mem_circle

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Conic

/-- The matrix `!![a, b; -b, a]` attached to a point of the conic, as an element of `SL(2,F)`.
Its determinant is `a² + b² = 1`. -/
private def conicToSL (F : Type*) [Field F] (p : F × F) (hp : p.1 ^ 2 + p.2 ^ 2 = 1) :
    Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![p.1, p.2; -p.2, p.1], by
    rw [Matrix.det_fin_two_of]
    linear_combination hp⟩

/-- `Nat.card (circle F)` is the number of points of the conic `a ^ 2 + b ^ 2 = 1`:
`mem_circle` identifies `circle F = C_{SL(2,F)}(z)` with the image of the injective map
`(a, b) ↦ !![a, b; -b, a]` from the conic. -/
theorem circle_ncard_conic (F : Type*) [Field F] :
    Nat.card (Work.L2F.circle F) = {p : F × F | p.1 ^ 2 + p.2 ^ 2 = 1}.ncard := by
  rw [← SetLike.coe_sort_coe]
  rw [Nat.card_coe_set_eq]
  refine (Set.ncard_congr (s := {p : F × F | p.1 ^ 2 + p.2 ^ 2 = 1})
    (t := (Work.L2F.circle F : Set (Matrix.SpecialLinearGroup (Fin 2) F)))
    (fun p hp => conicToSL F p hp) ?_ ?_ ?_).symm
  · -- the image lies in `circle F`
    intro p hp
    exact (mem_circle F _).mpr ⟨p.1, p.2, hp, rfl⟩
  · -- injectivity: the matrix determines `(a,b)`
    intro p q hp hq heq
    have hmat := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) F =>
      (x : Matrix (Fin 2) (Fin 2) F)) heq
    have h0 := congrFun (congrFun hmat 0) 0
    have h1 := congrFun (congrFun hmat 0) 1
    simp only [conicToSL, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.cons_val_one] at h0 h1
    exact Prod.ext h0 h1
  · -- surjectivity: `mem_circle` produces the preimage
    intro x hx
    obtain ⟨a, b, hab, hxeq⟩ := (mem_circle F x).mp hx
    refine ⟨(a, b), hab, ?_⟩
    apply Subtype.ext
    rw [hxeq]
    rfl

end Work.L2F.Conic

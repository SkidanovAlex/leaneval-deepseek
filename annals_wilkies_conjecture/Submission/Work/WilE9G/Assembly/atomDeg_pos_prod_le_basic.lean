import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE9G.Assembly.atomDeg_list_prod_le

namespace Work.WilE9G.Assembly

open WilkiesDesign.E

/-- The degree of a product of atoms is at most the sum of the atom degrees, with the `+1` slack
that `atomDeg = totalDegree + 1` carries. -/
private lemma atomDeg_list_prod_le_aux {k r : ℕ} (l : List (EAPoly k r)) :
    atomDeg l.prod ≤ (l.map atomDeg).sum + 1 := by
  induction l with
  | nil => simp [atomDeg]
  | cons a t ih =>
    have htd : (a * t.prod).totalDegree ≤ a.totalDegree + t.prod.totalDegree :=
      MvPolynomial.totalDegree_mul a t.prod
    have ih' : t.prod.totalDegree ≤ (t.map atomDeg).sum := by
      have h : t.prod.totalDegree + 1 ≤ (t.map atomDeg).sum + 1 := ih
      omega
    show (a * t.prod).totalDegree + 1 ≤ (a.totalDegree + 1) + ((t.map atomDeg).sum + 1)
    omega

theorem atomDeg_pos_prod_le_basic {k r : ℕ} (B : WilkiesDesign.E.Basic k r) :
    WilkiesDesign.E.atomDeg B.pos.prod ≤ B.deg + 1 := by
  have h₁ : atomDeg B.pos.prod ≤ (B.pos.map atomDeg).sum + 1 := atomDeg_list_prod_le_aux B.pos
  have h₂ : (B.pos.map atomDeg).sum ≤ B.deg := by
    show (B.pos.map atomDeg).sum ≤ ((B.eqs ++ B.pos).map atomDeg).sum
    rw [List.map_append, List.sum_append]
    exact Nat.le_add_left _ _
  omega

end Work.WilE9G.Assembly

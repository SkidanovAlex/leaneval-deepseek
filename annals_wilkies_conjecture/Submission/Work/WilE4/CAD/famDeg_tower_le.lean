import Mathlib
import Submission.Work.WilE4.CAD.Size
import Submission.Work.WilE4.CAD.Proj
import Submission.Work.WilE4.Tower

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial

/-- `famDeg` of a concatenation of lists: the degrees add. -/
theorem famDeg_flatMap {α : Type*} {m : ℕ} (l : List α)
    (f : α → List (MvPolynomial (Fin m) ℝ)) :
    famDeg (l.flatMap f) = (l.map fun a => famDeg (f a)).sum := by
  induction l with
  | nil => simp [famDeg]
  | cons a t ih =>
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
      rw [famDeg_append, ih]

/-- Iterated derivatives do not increase the atom degree. -/
theorem atomDegD_iterate_pderiv_le {m : ℕ} (P : MvPolynomial (Fin m) ℝ) (i : Fin m) (k : ℕ) :
    atomDegD ((MvPolynomial.pderiv i)^[k] P) ≤ atomDegD P := by
  have h := totalDegree_iterate_pderiv_le P i k
  simp only [atomDegD]
  omega

/-- The contribution of a single member `P` of a family to its derivative tower is at most the
square of the atom degree of `P`. -/
theorem famDeg_derivList_le {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℝ) :
    famDeg ((List.range (P.degreeOf (Fin.last m) + 1)).map
        fun k => ((MvPolynomial.pderiv (Fin.last m))^[k]) P) ≤ atomDegD P * atomDegD P := by
  rw [famDeg, List.map_map]
  have hd : P.degreeOf (Fin.last m) + 1 ≤ atomDegD P := by
    have h := MvPolynomial.degreeOf_le_totalDegree P (Fin.last m)
    simp only [atomDegD]
    omega
  calc (((List.range (P.degreeOf (Fin.last m) + 1)).map
        fun k => atomDegD (((MvPolynomial.pderiv (Fin.last m))^[k]) P))).sum
      ≤ ((List.range (P.degreeOf (Fin.last m) + 1)).map fun _ => atomDegD P).sum :=
        List.sum_le_sum fun k _ => atomDegD_iterate_pderiv_le P (Fin.last m) k
    _ = (P.degreeOf (Fin.last m) + 1) * atomDegD P := by
        simp [List.map_const', List.sum_replicate]
    _ ≤ atomDegD P * atomDegD P := Nat.mul_le_mul_right _ hd

theorem famDeg_tower_le {m : ℕ} {X : List (MvPolynomial (Fin (m + 1)) ℝ)} {D : ℕ}
    (hX : ∀ P ∈ X, P.totalDegree ≤ D) :
    Work.WilE4.CAD.famDeg (Work.WilE4.tower X) ≤ Work.WilE4.CAD.famDeg X * (D + 1) ^ 2 := by
  rw [Work.WilE4.tower, famDeg_flatMap]
  have h1 : ∀ P ∈ X, famDeg ((List.range (P.degreeOf (Fin.last m) + 1)).map
      fun k => ((MvPolynomial.pderiv (Fin.last m))^[k]) P) ≤ atomDegD P * atomDegD P :=
    fun P _ => famDeg_derivList_le P
  have hD1 : ∀ P ∈ X, atomDegD P ≤ (D + 1) ^ 2 := by
    intro P hP
    have h := hX P hP
    have : 1 ≤ D + 1 := by omega
    calc atomDegD P = P.totalDegree + 1 := rfl
      _ ≤ D + 1 := by omega
      _ = (D + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (D + 1) * (D + 1) := Nat.mul_le_mul_left _ this
      _ = (D + 1) ^ 2 := by ring
  have h2 : ∀ P ∈ X, atomDegD P * atomDegD P ≤ atomDegD P * (D + 1) ^ 2 :=
    fun P hP => Nat.mul_le_mul_left _ (hD1 P hP)
  calc (X.map fun P => famDeg ((List.range (P.degreeOf (Fin.last m) + 1)).map
        fun k => ((MvPolynomial.pderiv (Fin.last m))^[k]) P)).sum
      ≤ (X.map fun P => atomDegD P * atomDegD P).sum := List.sum_le_sum h1
    _ ≤ (X.map fun P => atomDegD P * (D + 1) ^ 2).sum := List.sum_le_sum h2
    _ = famDeg X * (D + 1) ^ 2 := by
        rw [famDeg, List.sum_map_mul_right]

end Work.WilE4.CAD

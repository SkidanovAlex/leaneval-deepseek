import Mathlib
import Submission.Work.Wilkies.E.Spec

namespace Work.WilE9G.Assembly

/-- `atomDeg` is sub-multiplicative on EA polynomials: the `+1` in `atomDeg Q = Q.totalDegree + 1`
absorbs the total-degree additivity of a product. -/
theorem atomDeg_mul_le {k r : ℕ} (a b : WilkiesDesign.E.EAPoly k r) :
    WilkiesDesign.E.atomDeg (a * b) ≤
      WilkiesDesign.E.atomDeg a + WilkiesDesign.E.atomDeg b := by
  have h := MvPolynomial.totalDegree_mul a b
  simp only [WilkiesDesign.E.atomDeg]
  omega

/-- The degree of a product of a list of EA polynomials is at most the sum of the degrees of the
factors, with one extra unit to pay for the constant term `1` of the empty product. -/
theorem atomDeg_list_prod_le {k r : ℕ} (l : List (WilkiesDesign.E.EAPoly k r)) :
    WilkiesDesign.E.atomDeg l.prod ≤ (l.map WilkiesDesign.E.atomDeg).sum + 1 := by
  induction l with
  | nil => simp [WilkiesDesign.E.atomDeg]
  | cons hd tl ih =>
    rw [List.prod_cons, List.map_cons, List.sum_cons]
    calc WilkiesDesign.E.atomDeg (hd * tl.prod)
        ≤ WilkiesDesign.E.atomDeg hd + WilkiesDesign.E.atomDeg tl.prod :=
          atomDeg_mul_le hd tl.prod
      _ ≤ WilkiesDesign.E.atomDeg hd + ((tl.map WilkiesDesign.E.atomDeg).sum + 1) :=
          Nat.add_le_add_left ih _
      _ = WilkiesDesign.E.atomDeg hd + (tl.map WilkiesDesign.E.atomDeg).sum + 1 := by
          rw [Nat.add_assoc]

end Work.WilE9G.Assembly

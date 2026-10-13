import Mathlib
import Submission.Work.WilE5.Cells

namespace Work.WilE5.Cells

open WilkiesDesign WilkiesDesign.E

variable {k r : ℕ}

/-- Adding a constant does not increase the total degree. -/
lemma totalDegree_add_C_le (f : EAPoly k r) (ε : ℝ) :
    (f + MvPolynomial.C ε).totalDegree ≤ f.totalDegree :=
  (MvPolynomial.totalDegree_add _ _).trans (by simp)

/-- Subtracting a constant does not increase the total degree. -/
lemma totalDegree_sub_C_le (f : EAPoly k r) (ε : ℝ) :
    (f - MvPolynomial.C ε).totalDegree ≤ f.totalDegree := by
  rw [sub_eq_add_neg, ← map_neg]
  exact totalDegree_add_C_le f (-ε)

/-- The degree of the atom `(f + ε)²(f - ε)²` is at most four times the degree of `f`; this is the
elementary estimate behind Khovanskii's bound on the number of sign conditions of the perturbed
atoms. -/
lemma atomDeg_sq_sq_le (f : EAPoly k r) (ε : ℝ) :
    atomDeg ((f + MvPolynomial.C ε) ^ 2 * (f - MvPolynomial.C ε) ^ 2) ≤ 4 * atomDeg f := by
  have h1 : ((f + MvPolynomial.C ε) ^ 2).totalDegree ≤ 2 * f.totalDegree :=
    (MvPolynomial.totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2 (totalDegree_add_C_le f ε))
  have h2 : ((f - MvPolynomial.C ε) ^ 2).totalDegree ≤ 2 * f.totalDegree :=
    (MvPolynomial.totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2 (totalDegree_sub_C_le f ε))
  have h3 : ((f + MvPolynomial.C ε) ^ 2 * (f - MvPolynomial.C ε) ^ 2).totalDegree ≤
      4 * f.totalDegree := by
    calc ((f + MvPolynomial.C ε) ^ 2 * (f - MvPolynomial.C ε) ^ 2).totalDegree
        ≤ ((f + MvPolynomial.C ε) ^ 2).totalDegree +
            ((f - MvPolynomial.C ε) ^ 2).totalDegree := MvPolynomial.totalDegree_mul _ _
      _ ≤ 2 * f.totalDegree + 2 * f.totalDegree := add_le_add h1 h2
      _ = 4 * f.totalDegree := by ring
  simp only [atomDeg]
  omega

theorem khovPosDeg {k : ℕ} (X : WilkiesDesign.E.SemiPf k) (ε : ℝ) :
    ((Work.WilE5.atomsOf X).map (fun f =>
        WilkiesDesign.E.atomDeg ((f + MvPolynomial.C ε) ^ 2 * (f - MvPolynomial.C ε) ^ 2))).sum ≤
      4 * ((Work.WilE5.atomsOf X).map WilkiesDesign.E.atomDeg).sum := by
  calc ((Work.WilE5.atomsOf X).map (fun f =>
          WilkiesDesign.E.atomDeg ((f + MvPolynomial.C ε) ^ 2 * (f - MvPolynomial.C ε) ^ 2))).sum
      ≤ ((Work.WilE5.atomsOf X).map (fun f => 4 * WilkiesDesign.E.atomDeg f)).sum :=
        List.sum_le_sum fun f _ => atomDeg_sq_sq_le f ε
    _ = 4 * ((Work.WilE5.atomsOf X).map WilkiesDesign.E.atomDeg).sum :=
        List.sum_map_mul_left _ _ 4

end Work.WilE5.Cells

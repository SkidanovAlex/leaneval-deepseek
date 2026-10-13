import Mathlib
import Submission.Work.WilE3.Frame.CutSys

namespace Work.WilE3.Frame

/-- Each summand of `cutPoly` — a constant times `(X i - C (x i))` — has total degree `≤ 1`. -/
private lemma totalDegree_cutPoly_term {k r j : ℕ} (ι : Fin j → Fin k)
    (μ : Work.WilE3.Frame.U k ι → ℝ) (x : Fin k → ℝ) (i : U k ι) :
    (MvPolynomial.C (μ i) *
        (MvPolynomial.X (Sum.inl i.1) - MvPolynomial.C (x i.1)) :
      WilkiesDesign.E.EAPoly k r).totalDegree ≤ 1 := by
  have hC : (MvPolynomial.C (μ i) : WilkiesDesign.E.EAPoly k r).totalDegree ≤ 0 :=
    le_of_eq (MvPolynomial.totalDegree_C _)
  have hX : (MvPolynomial.X (Sum.inl i.1) - MvPolynomial.C (x i.1) :
      WilkiesDesign.E.EAPoly k r).totalDegree ≤ 1 := by
    refine (MvPolynomial.totalDegree_sub_C_le _ _).trans ?_
    rw [MvPolynomial.totalDegree_X]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  omega

theorem atomDeg_cutPoly_le {k r j : ℕ} (ι : Fin j → Fin k)
    (μ : Work.WilE3.Frame.U k ι → ℝ) (x : Fin k → ℝ) :
    WilkiesDesign.E.atomDeg (Work.WilE3.Frame.cutPoly (r := r) ι μ x) ≤ 2 := by
  have h : (Work.WilE3.Frame.cutPoly (r := r) ι μ x).totalDegree ≤ 1 := by
    rw [Work.WilE3.Frame.cutPoly]
    exact MvPolynomial.totalDegree_finsetSum_le
      (fun i _ => totalDegree_cutPoly_term ι μ x i)
  simp only [WilkiesDesign.E.atomDeg]
  omega

end Work.WilE3.Frame

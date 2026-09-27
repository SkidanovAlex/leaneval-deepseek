import Mathlib
import Submission.Work.Cohomology.SubdivisionSpace

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

/-- Pushing a chain of `Δ^k` forward along the map of the `i`-th face of a simplex `σ` of degree
`k+1` is the same as pushing it forward along `σ` after the `i`-th face inclusion.

(Generalises `Submission.Cohomology.pushChain_homOfSimplex_delta`, which only covers chains in
degree `k`; the identity itself holds in every degree.) -/
lemma pushChain_homOfSimplex_face {X : TopCat.{0}} {k : ℕ} (i : Fin (k+2))
    (σ : (TopCat.toSSet.obj X).obj (op ⦋k+1⦌)) (m : ℕ)
    (x : Submission.Cohomology.SChain
      (TopCat.toSSet.obj (Submission.Cohomology.stdTopSimplex k)) ℚ m) :
    Submission.Cohomology.pushChain
        (Submission.Cohomology.homOfSimplex ((TopCat.toSSet.obj X).δ i σ)) m x
      = Submission.Cohomology.pushChain (Submission.Cohomology.homOfSimplex σ) m
          (Submission.Cohomology.pushChain (Submission.Cohomology.faceInclHom i) m x) := by
  rw [Submission.Cohomology.homOfSimplex_delta, Submission.Cohomology.pushChain_comp]

theorem uFun_eq_tFun_sbdry (X : TopCat.{0}) (n : ℕ)
    (c : Submission.Cohomology.SChain (TopCat.toSSet.obj X) ℚ (n+1)) :
    Submission.Cohomology.uFun X (n+1) c
      = Submission.Cohomology.tFun X n
          (Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single σ r =>
      rw [Submission.Cohomology.uFun_single, Submission.Cohomology.sbdry_single, map_sum]
      simp only [Submission.Cohomology.tFun_single]
      rw [Submission.Cohomology.uUniv_succ, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [pushChain_homOfSimplex_face, map_smul]
      rw [← smul_assoc]
      congr 1
      rw [zsmul_eq_mul]
      push_cast
      ring

end Work.Cohomology

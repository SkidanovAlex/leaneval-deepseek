import Mathlib
import Submission.Work.Cohomology.SubdivisionSpace
import Submission.Work.Cohomology.uFun_eq_tFun_sbdry

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

/-- Pushing the identity chain of `Δⁿ` forward along the map of a simplex `σ` gives the simplex
`σ` itself. -/
lemma pushChain_homOfSimplex_idUniv {X : TopCat.{0}} (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op ⦋n⦌)) :
    Submission.Cohomology.pushChain (Submission.Cohomology.homOfSimplex σ) n
      (Submission.Cohomology.idUniv n) = Finsupp.single σ 1 := by
  simp [Submission.Cohomology.idUniv, Submission.Cohomology.toSingChain,
    Submission.Cohomology.toSingChainLM]

theorem tFun_homotopy (X : TopCat.{0}) (n : ℕ)
    (c : Submission.Cohomology.SChain (TopCat.toSSet.obj X) ℚ (n+1)) :
    Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ (n+1)
        (Submission.Cohomology.tFun X (n+1) c)
      + Submission.Cohomology.tFun X n
          (Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ n c)
      = c - Submission.Cohomology.sdFun X (n+1) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      have key : Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ (n+1)
            (Submission.Cohomology.tFun X (n+1) (a+b))
          + Submission.Cohomology.tFun X n
              (Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ n (a+b))
          = (Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ (n+1)
                (Submission.Cohomology.tFun X (n+1) a)
              + Submission.Cohomology.tFun X n
                  (Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ n a))
            + (Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ (n+1)
                (Submission.Cohomology.tFun X (n+1) b)
              + Submission.Cohomology.tFun X n
                  (Submission.Cohomology.sbdry (TopCat.toSSet.obj X) ℚ n b)) := by
        rw [map_add, map_add, map_add, map_add]; abel
      rw [key, ha, hb, map_add]
      abel
  | single σ r =>
      rw [← Work.Cohomology.uFun_eq_tFun_sbdry]
      simp only [Submission.Cohomology.tFun_single, Submission.Cohomology.uFun_single,
        Submission.Cohomology.sdFun_single, map_smul, ← Submission.Cohomology.pushChain_sbdry,
        Submission.Cohomology.sbdry_tUniv, map_sub, pushChain_homOfSimplex_idUniv, smul_sub,
        smul_sub]
      have hsm : r • (Finsupp.single σ (1:ℚ)) = Finsupp.single σ r := by
        rw [Finsupp.smul_single]; simp
      rw [hsm]
      abel

end Work.Cohomology

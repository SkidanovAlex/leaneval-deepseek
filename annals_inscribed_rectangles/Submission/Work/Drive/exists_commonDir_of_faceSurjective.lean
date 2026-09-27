import Mathlib
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.TParity.ChartDeriv
import Submission.Work.Drive.TParity.finite_bK3

namespace Work.Drive

/-- **The transversal common direction of the triple intersection, from the face-restricted surjectivity of the charted difference map.**

`Work.Drive.TParity.faceHyp` — one of the two inputs of the manifold triple-parity engine — requires, at every boundary triple point, a *common direction* of the three derivatives whose coordinate in the face direction is non-zero (`TripleCommonDir … v ∧ v k i ≠ 0`); that is the direction in which the triple intersection crosses the face of the box.  The engine's own proof derives the *face-restricted surjectivity* from it (`Work.Drive.TParity.chartDiff3_domRestrict_surjective`).  This statement is the converse, which is what a *parametric-Sard* argument needs, since what such an argument controls directly is the surjectivity of the derivative and of its restriction to the face hyperplane.

Concretely: let `D` be three smooth `3`-chains in a smooth `4`-manifold, `x : Amb 8` a triple meeting point in the chart region of a chart `p`, and `(k, i)` a block coordinate with the charted difference map `chartDiff3 p D` surjective at `x` and its restriction to the coordinate hyperplane `{w | w (bIdx k i) = 0}` surjective as well.  Then there is a common direction `v` of the three intrinsic derivatives with `(v k) i ≠ 0`.

Note that the hypothesis `hT` is redundant (the face-restricted surjectivity already forces `T` onto, since `T`'s image contains `T (H)`), but it is kept because it is the form in which the parametric-Sard conclusion is available; `hm` is required by `Work.Drive.TParity.tan3_eq_zero_iff`.

Proof route (as reconstructed by the reviewers).  Put `T := fderiv ℝ (chartDiff3 p D) x`.  `hface` is the hypothesis of `Work.Drive.surjective_domRestrict_iff_cofactorVec_ne_zero`, giving `cofactorVec T (bIdx k i) ≠ 0`; `cofactorVec_mem_ker` gives `T (cofactorVec T) = 0`; `hasFDerivAt_chartDiff3` with `pUpCLM_eq_zero_iff` converts this into `tan3 p D x (cofactorVec T) = 0`, and `tan3_eq_zero_iff` yields `TripleCommonDir (md3 D 0 x) (md3 D 1 x) (md3 D 2 x) (fun k => bPartC k (cofactorVec T))` with `(v k) i = cofactorVec T (bIdx k i) ≠ 0` by `bPartC_apply` and `mk3_bIdx`. -/
theorem exists_commonDir_of_faceSurjective {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (p : M) (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    {x : EuclideanSpace ℝ (Fin 9)} (hx : x ∈ Work.Drive.TParity.region3 p D)
    (hm : Work.Drive.TParity.meet3 D x)
    {k : Fin 3} {i : Fin 3}
    (hT : Function.Surjective (fderiv ℝ (Work.Drive.TParity.chartDiff3 p D) x))
    (hface : Function.Surjective (fun w : {w : EuclideanSpace ℝ (Fin 9) //
        w (Work.Drive.bIdx k i) = 0} =>
      fderiv ℝ (Work.Drive.TParity.chartDiff3 p D) x (w : EuclideanSpace ℝ (Fin 9)))) :
    ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
      Work.Drive.TripleCommonDir (Work.Drive.TParity.md3 D 0 x)
        (Work.Drive.TParity.md3 D 1 x) (Work.Drive.TParity.md3 D 2 x) v ∧ (v k) i ≠ 0 := by
  set T := fderiv ℝ (Work.Drive.TParity.chartDiff3 p D) x with hTdef
  have hcof : Work.Drive.cofactorVec T (Work.Drive.bIdx k i) ≠ 0 :=
    (Work.Drive.surjective_domRestrict_iff_cofactorVec_ne_zero T hT (Work.Drive.bIdx k i)).mp hface
  have hfd : T = Work.Drive.TParity.pUpCLM.comp (Work.Drive.TParity.tan3 p D x) := by
    rw [hTdef]
    exact (Work.Drive.TParity.hasFDerivAt_chartDiff3 p D hD hx).fderiv
  have h1 : T (Work.Drive.cofactorVec T) =
      Work.Drive.TParity.pUpCLM
        (Work.Drive.TParity.tan3 p D x (Work.Drive.cofactorVec T)) := by
    have h := congrArg
      (fun S : Work.Drive.Amb 8 →L[ℝ] Work.Drive.Tgt 8 => S (Work.Drive.cofactorVec T)) hfd
    simpa using h
  have hker : T (Work.Drive.cofactorVec T) = 0 := Work.Drive.cofactorVec_mem_ker T
  have htan : Work.Drive.TParity.tan3 p D x (Work.Drive.cofactorVec T) = 0 :=
    (Work.Drive.TParity.pUpCLM_eq_zero_iff _).mp (h1 ▸ hker)
  refine ⟨fun k => Work.Drive.TParity.bPartC k (Work.Drive.cofactorVec T), ?_, ?_⟩
  · exact (Work.Drive.TParity.tan3_eq_zero_iff p D hx hm (Work.Drive.cofactorVec T)).mp htan
  · rw [Work.Drive.TParity.bPartC_apply]
    exact hcof

end Work.Drive

import Mathlib
import Submission.Work.WilE7.FrontierCS.analyticOnNhd_jacDet

namespace Work.WilE7.FrontierCS

theorem analyticAt_sqSum_detSq {j : ℕ} {g : (Fin j → ℝ) → (Fin j → ℝ)}
    (hg : AnalyticOnNhd ℝ g Set.univ) :
    AnalyticAt ℝ (fun e => ∑ i, (g e i) ^ 2) 0 ∧
      AnalyticAt ℝ (fun e : Fin j → ℝ =>
        ((Matrix.of fun (a l : Fin j) => fderiv ℝ g e (Pi.single l 1) a).det) ^ 2) 0 := by
  refine ⟨?_, ?_⟩
  · -- `∑ i, (g e i)^2` is the polynomial map `y ↦ ∑ i, (y i)^2` composed with `g`.
    have hg0 : AnalyticAt ℝ g 0 := hg 0 (Set.mem_univ 0)
    have hpoly : ∀ c : Fin j → ℝ, AnalyticAt ℝ (fun y : Fin j → ℝ => ∑ i, (y i) ^ 2) c := by
      intro c
      have hcoord : ∀ i : Fin j, AnalyticAt ℝ (fun y : Fin j → ℝ => (y i) ^ 2) c := by
        intro i
        have h : AnalyticAt ℝ (fun y : Fin j → ℝ => y i) c := by
          have h1 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin j => ℝ) i).analyticAt c
          have heq : (fun y : Fin j → ℝ => y i)
              = ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin j => ℝ) i) := by
            funext y; exact (ContinuousLinearMap.proj_apply i y).symm
          rw [heq]; exact h1
        exact h.pow 2
      have hsum : AnalyticAt ℝ (∑ i : Fin j, fun y : Fin j → ℝ => (y i) ^ 2) c := by
        apply Finset.analyticAt_sum (𝕜 := ℝ) (Finset.univ : Finset (Fin j))
        intro i _
        exact hcoord i
      convert hsum using 2 with y
      rw [Finset.sum_apply]
    have hcomp : AnalyticAt ℝ ((fun y : Fin j → ℝ => ∑ i, (y i) ^ 2) ∘ g) 0 :=
      (hpoly (g 0)).comp hg0
    simpa [Function.comp_def] using hcomp
  · -- The Jacobian determinant is analytic, hence so is its square.
    have hjac : AnalyticAt ℝ
        (fun e => (Matrix.of fun (a l : Fin j) => fderiv ℝ g e (Pi.single l 1) a).det) 0 :=
      analyticOnNhd_jacDet hg 0 (Set.mem_univ 0)
    exact hjac.pow 2

end Work.WilE7.FrontierCS

import Mathlib

namespace Work.Drive

/-- **The range of the derivative of a loop reparametrised by a surjective linear map.** -/
theorem range_mfderiv_comp_surjective_linear {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {n : ℕ} (f : ℝ → M)
    (hf : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (hL : Function.Surjective L)
    (u : EuclideanSpace ℝ (Fin n)) :
    LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (fun x => f (L x)) u).toLinearMap =
      LinearMap.range (mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) f (L u)).toLinearMap := by
  -- the chain rule: `mfderiv (f ∘ L) u = mfderiv f (L u) ∘ mfderiv L u`
  have hL' : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ ℝ) L u :=
    (ContinuousLinearMap.hasMFDerivAt L).mdifferentiableAt
  have hf' : MDifferentiableAt (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) f (L u) :=
    hf.mdifferentiableAt (by simp)
  have hcomp : mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (fun x => f (L x)) u =
      (mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) f (L u)).comp
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ ℝ) L u) := by
    simpa [Function.comp_def] using (mfderiv_comp (f := L) (g := f) u hf' hL')
  -- `mfderiv L u = L` is onto, so composing with it does not change the range
  have hsurj : LinearMap.range (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ ℝ) L u).toLinearMap = ⊤ := by
    rw [show mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ ℝ) L u = L from
      HasMFDerivAt.mfderiv (ContinuousLinearMap.hasMFDerivAt L)]
    exact LinearMap.range_eq_top.mpr hL
  rw [hcomp, ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp, hsurj,
    Submodule.map_top]

end Work.Drive

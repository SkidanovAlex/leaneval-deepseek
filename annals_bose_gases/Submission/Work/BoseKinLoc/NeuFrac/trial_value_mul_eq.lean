import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseKinLoc.NeuFrac

/-- **`Work.BoseKinLoc.NeuFrac.trial_value_mul_eq`**

The Neumann-resolvent fraction `neuFrac` (FS `eq:DefT`, first term) is insensitive to
multiplying the trial function by a factor `η` which is *locally* equal to `1` at every
point of the box.

The hypothesis `hη` says that for every `z` in the closed ball of radius `R` the function
`η` agrees with `1` in a neighbourhood of `z`; since the box `Λ(u)` is contained in that
ball (`hbox`) and the ball is compact, finitely many of those neighbourhoods cover the
box, so `η = 1` **pointwise on the box** (not merely almost everywhere).  Consequently
`η z * θ z = θ z` on the box and, `η` being locally `1` at every point of the box,
`fderiv ℝ (fun z => η z * θ z) z = fderiv ℝ θ z` there; both integrals and the
derivative sum therefore agree. -/
lemma trial_value_mul_eq {ℓ a2 R : ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    {ψ θ η : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hbox : Work.BoseKinLoc.lamBox ℓ u ⊆ Metric.closedBall 0 R)
    (hη : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R → η =ᶠ[nhds z] 1) :
    (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2)
        - 2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, ψ z * (η z * θ z))
        + a2 * ((∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ u,
                  (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) => η z * θ z) z
                    (Submission.BoseGases.kcStdBasis k)) ^ 2)
                + a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (η z * θ z) ^ 2))
      = (∫ z in Work.BoseKinLoc.lamBox ℓ u, (ψ z) ^ 2)
        - 2 * a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, ψ z * θ z)
        + a2 * ((∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ u,
                  (fderiv ℝ θ z (Submission.BoseGases.kcStdBasis k)) ^ 2)
                + a2 * (∫ z in Work.BoseKinLoc.lamBox ℓ u, (θ z) ^ 2)) := by
  classical
  -- the moving box is closed, hence measurable
  have hmeas : MeasurableSet (Work.BoseKinLoc.lamBox ℓ u) := by
    have hcl : IsClosed (Work.BoseKinLoc.lamBox ℓ u) := by
      show IsClosed (Work.BSKinetic.bsBox ℓ u)
      rw [Work.BSKinetic.bsBox]
      exact (Submission.BoseGases.acube_isClosed ℓ).preimage (by fun_prop)
    exact hcl.measurableSet
  -- points of the box lie in the closed ball of radius `R`
  have hbox' : ∀ z ∈ Work.BoseKinLoc.lamBox ℓ u, ‖z‖ ≤ R := by
    intro z hz
    have := hbox hz
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  -- `η = 1` pointwise on the box (compactness: finitely many local neighbourhoods)
  have hηbox : ∀ z ∈ Work.BoseKinLoc.lamBox ℓ u, η z = 1 := by
    have hU : ∀ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R,
        {y : EuclideanSpace ℝ (Fin 3) | η y = 1} ∈ nhds x := by
      intro x hx
      have hxR : ‖x‖ ≤ R := by
        rw [Metric.mem_closedBall, dist_zero_right] at hx
        exact hx
      exact hη x hxR
    obtain ⟨t, -, hcov⟩ :=
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 3)) R).elim_nhds_subcover
        (fun _ => {y : EuclideanSpace ℝ (Fin 3) | η y = 1}) hU
    intro z hz
    have h1 := hcov (hbox hz)
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at h1
    obtain ⟨x, -, hxz⟩ := h1
    exact hxz
  -- `η` is locally `1` at each point of the box, so it is invisible to the derivative
  have hfd : ∀ z ∈ Work.BoseKinLoc.lamBox ℓ u, ∀ k : Fin 3,
      (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) => η z * θ z) z)
        (Submission.BoseGases.kcStdBasis k)
      = fderiv ℝ θ z (Submission.BoseGases.kcStdBasis k) := by
    intro z hz k
    have h1 : (fun w : EuclideanSpace ℝ (Fin 3) => η w * θ w) =ᶠ[nhds z] θ := by
      have h2 : (fun w : EuclideanSpace ℝ (Fin 3) => η w * θ w) =ᶠ[nhds z]
          (fun w : EuclideanSpace ℝ (Fin 3) => (1 : ℝ) * θ w) :=
        (hη z (hbox' z hz)).mul (Filter.EventuallyEq.refl (nhds z) θ)
      have h3 : (fun w : EuclideanSpace ℝ (Fin 3) => (1 : ℝ) * θ w) = θ := by
        funext w
        rw [one_mul]
      rwa [h3] at h2
    rw [h1.fderiv_eq]
  -- the three integrands agree on the box
  have hI1 : (∫ z in Work.BoseKinLoc.lamBox ℓ u, ψ z * (η z * θ z))
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u, ψ z * θ z := by
    refine MeasureTheory.setIntegral_congr_fun hmeas ?_
    intro z hz
    simp only [hηbox z hz, one_mul]
  have hI2 : (∫ z in Work.BoseKinLoc.lamBox ℓ u, (η z * θ z) ^ 2)
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u, (θ z) ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun hmeas ?_
    intro z hz
    simp only [hηbox z hz, one_mul]
  have hI3 : ∀ k : Fin 3, (∫ z in Work.BoseKinLoc.lamBox ℓ u,
        (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) => η z * θ z) z
          (Submission.BoseGases.kcStdBasis k)) ^ 2)
      = ∫ z in Work.BoseKinLoc.lamBox ℓ u,
          (fderiv ℝ θ z (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
    intro k
    refine MeasureTheory.setIntegral_congr_fun hmeas ?_
    intro z hz
    simp only [hfd z hz k]
  have hsum : (∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ u,
        (fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 3) => η z * θ z) z
          (Submission.BoseGases.kcStdBasis k)) ^ 2)
      = ∑ k : Fin 3, ∫ z in Work.BoseKinLoc.lamBox ℓ u,
          (fderiv ℝ θ z (Submission.BoseGases.kcStdBasis k)) ^ 2 :=
    Finset.sum_congr rfl (fun k _ => hI3 k)
  rw [hI1, hI2, hsum]

end Work.BoseKinLoc.NeuFrac

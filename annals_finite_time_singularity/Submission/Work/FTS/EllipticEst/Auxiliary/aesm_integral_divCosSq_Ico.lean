import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Auxiliary

/-- **A.e.-strong measurability of the angular slice integral of `(Ψ/cos θ)²`.**

For `Ψ` smooth on a neighbourhood of the closed quadrant, the function
`z ↦ ∫_{θ ∈ (0,π/2)} (Ψ z θ / cos θ)²` is a.e.-strongly measurable for the measure
`volume.restrict (Icc 0 R)`.

Route.  The integrand `K p = (Ψ p.1 p.2 / Real.cos p.2)^2` is continuous on the open set
`V = Ioi (-1) ×ˢ Ioo (-1) (π/2)` (there `cos p.2 ≠ 0`, and `V ⊆ U` where `hsm` gives continuity
of `p ↦ Ψ p.1 p.2`; use `hsm.continuousOn.mono` + `ContinuousOn.div`/`.pow`), and the box
`S := Set.Icc 0 R ×ˢ Set.Ico 0 (π/2)` is contained in `V`.  Hence
`ContinuousOn.aestronglyMeasurable` gives `AEStronglyMeasurable K ((volume.prod volume).restrict S)`,
and `Measure.prod_restrict` identifies this with
`(volume.restrict (Icc 0 R)).prod (volume.restrict (Ico 0 (π/2)))`.  Then
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'` yields the claim. -/
theorem aesm_integral_divCosSq_Ico (Ψ : ℝ → ℝ → ℝ)
    (hsm : Work.Spaces.SmoothNbhd Ψ) (R : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Set.Ico 0 (Real.pi / 2), (Ψ z θ / Real.cos θ) ^ 2)
      (MeasureTheory.volume.restrict (Set.Icc 0 R)) := by
  set s : Set (ℝ × ℝ) := Set.Icc 0 R ×ˢ Set.Ico 0 (Real.pi / 2) with hs
  -- the box `S` is a measurable set
  have hsmeas : MeasurableSet s := measurableSet_Icc.prod measurableSet_Ico
  -- `S` lies in the open set on which `hsm` provides smoothness
  have hsub : s ⊆ Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1) := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    simp only [Set.mem_Icc, Set.mem_Ico] at hz hθ
    constructor
    · show (-1 : ℝ) < z
      linarith [hz.1]
    · show θ ∈ Set.Ioo (-1) (Real.pi / 2 + 1)
      constructor
      · linarith [hθ.1, Real.pi_pos]
      · linarith [hθ.2, Real.pi_pos]
  -- `cos` does not vanish on `S`
  have hcos : ∀ p ∈ s, Real.cos p.2 ≠ 0 := by
    rintro ⟨z, θ⟩ ⟨hz, hθ⟩
    simp only [Set.mem_Ico] at hθ
    exact ne_of_gt
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  -- so the integrand is continuous on `S`
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (Ψ p.1 p.2 / Real.cos p.2) ^ 2) s :=
    ((hsm.continuousOn.mono hsub).div
      ((Real.continuous_cos.comp continuous_snd).continuousOn) hcos).pow 2
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Ψ p.1 p.2 / Real.cos p.2) ^ 2)
      ((MeasureTheory.volume.prod MeasureTheory.volume).restrict s) :=
    hcont.aestronglyMeasurable hsmeas
  rw [hs] at h1
  -- identify the product measure on the box with the product of the restricted measures
  rw [show (MeasureTheory.volume.prod MeasureTheory.volume).restrict
        (Set.Icc 0 R ×ˢ Set.Ico 0 (Real.pi / 2))
      = (MeasureTheory.volume.restrict (Set.Icc 0 R)).prod
        (MeasureTheory.volume.restrict (Set.Ico 0 (Real.pi / 2)))
      from (MeasureTheory.Measure.prod_restrict _ _).symm] at h1
  exact h1.integral_prod_right'

end Work.FTS.EllipticEst.Auxiliary

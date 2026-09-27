import Mathlib
import Submission.Work.Drive.sepFamDefs

/-!
# The loop family of the separated germ route is *jointly* `C^∞`

`Work.Drive.SepLoopSmoothJoint` is the loop-side counterpart of `Work.Drive.SepChainSmoothJoint`
(`Submission/Work/Drive/sepContMDiffFams.lean`): the loop family of the five-box family of
`Work.Drive.sep_fam_regular`,

`sepLoopFam Ξ Q A B τ₁ = chartLoopFam (sepQfam Ξ Q A B τ₁)`,

is `C^∞` *jointly* in the shift `τ₁` and the loop parameter `p`.

In coordinates the family is

`(τ, p) ↦ Ξ (sepPathL A B (p 0) + τ) (Q (exp (π * (p 1 : ℂ) * I)))`,

i.e. the composite of the jointly smooth chart perturbation `ChartPert.2.1`, the affine loop path
`sepPathL` (smooth in the loop parameter `p 0`), the smooth disk presentation `Q` and the exponential
parametrisation of the core loop.  Both variables enter through maps that are `C^∞` on the *flat*
parameter space `EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2)`
(`sepJointLoopSmoothFlat`), and the product model `(𝓡 m).prod (𝓡 2)` of the statement is exchanged
with the flat one by `modelWithCornersSelf_prod` / `chartedSpaceSelf_prod` — exactly the pattern of
`sepJointChainSmooth`.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 2000000

variable {m : ℕ}

/-- **The loop family is jointly `C^∞`**, in the flattened form of the parameter space
`ℝᵐ × ℝ² = 𝓘(ℝ, ℝᵐ × ℝ²)`. -/
theorem sepJointLoopSmoothFlat
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (hΞ : ChartPert Q m Ξ) (hQ : IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        sepLoopFam Ξ Q A B q.1 q.2) := by
  have hQsm : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) Ctop Q := hQ
  -- the loop parameter enters the chart perturbation along the straight path `sepPathL`
  have hpath : ContDiff ℝ Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        sepPathL A B (q.2 0) + q.1) := by
    unfold sepPathL
    fun_prop
  have h1 : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2))) (𝓡 m) Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        sepPathL A B (q.2 0) + q.1) := contMDiff_iff_contDiff.mpr hpath
  -- the core loop of the chart
  have hexp : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2))) (𝓘(ℝ, ℂ))
      Ctop
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
        Complex.exp (Real.pi * ((q.2 1 : ℝ) : ℂ) * Complex.I)) := by
    have hlin : ContDiff ℝ Ctop
        (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) =>
          Real.pi * ((q.2 1 : ℝ) : ℂ) * Complex.I) := by
      have h1 : ContDiff ℝ Ctop
          (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 2) => ((q.2 1 : ℝ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (by fun_prop)
      exact (contDiff_const.mul h1).mul contDiff_const
    exact Complex.contDiff_exp.contMDiff.comp (contMDiff_iff_contDiff.mpr hlin)
  have hmain := hΞ.2.1.comp (h1.prodMk (hQsm.comp hexp))
  refine hmain.congr fun q => ?_
  simp only [Function.comp_def, sepLoopFam, chartLoopFam, sepQfam, coreLoop]

/-- **The loop family is jointly `C^∞` in the shift and the loop parameter.**  The statement is the
definition `Work.Drive.SepLoopSmoothJoint` (whose product model `(𝓡 m).prod (𝓡 2)` is exchanged
with the flattened one by `modelWithCornersSelf_prod`). -/
theorem sepLoopSmoothJoint {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace) (hΞ : Work.Drive.ChartPert Q m Ξ)
    (hQ : Work.Drive.IsSmoothChart Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    Work.Drive.SepLoopSmoothJoint Ξ Q A B := by
  rw [SepLoopSmoothJoint]
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact sepJointLoopSmoothFlat Ξ Q hΞ hQ A B

end

end Work.Drive

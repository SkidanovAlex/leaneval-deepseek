/-
Copyright: work module for the Elgindi finite-time singularity project.

# Self-adjointness of the curl on `ℝ³`

`Work.FTS.BSSwirl.integral_vorticity_eq`:

  `∫ x, ⟪∇×V x, Ψ x⟫ = ∫ x, ⟪V x, ∇×Ψ x⟫`

for every `C¹` vector field `V : ℝ³ → ℝ³` and every smooth compactly supported field `Ψ`.

This is the classical integration-by-parts identity for the curl, obtained here as follows.  With
`G := V × Ψ` (the cross product of the two fields) one has the *pointwise* Weyl identity

  `⟪∇×V x, Ψ x⟫ - ⟪V x, ∇×Ψ x⟫ = div G x`,

whose proof is the triple-product identity `⟪a × b, c⟫ = ⟪a, b × c⟫` applied to the coordinate
expansions `∇×u = ∑ i, eᵢ × ∂ᵢu` and `div u = ∑ i, ⟪eᵢ, ∂ᵢu⟫` of `Work.FTS.BSSwirl.CrossAux`
together with the product rule for the `fderiv` of a cross product.  Since `Ψ` is compactly
supported, so is `G`, whence `∫ div G = 0` by the divergence theorem on `ℝ³`
(`Work.FTS.BSSwirl.integral_div_eq_zero_compact`), and the claim follows.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.BSSwirl.Defs
import Submission.Work.FTS.BSSwirl.CrossAux
import Submission.Work.FTS.BSSwirl.integral_div_eq_zero_compact

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 2000000

open FiniteTimeSingularity MeasureTheory
open scoped Matrix Topology

namespace Work.FTS.BSSwirl

noncomputable section

/-- **The pointwise Weyl identity for the curl.**  For fields `V, Ψ` differentiable at `x`,

  `⟪∇×V x, Ψ x⟫ - ⟪V x, ∇×Ψ x⟫ = div (V × Ψ) x`.

Concretely, `∇×V = ∑ i, eᵢ × ∂ᵢV` and `div (V × Ψ) = ∑ i, ⟪eᵢ, ∂ᵢV × Ψ + V × ∂ᵢΨ⟫`, and the
scalar triple product identity identifies the two sums term by term. -/
theorem inner_vorticity_sub_eq_div {V Ψ : R3 → R3} {x : R3}
    (hV : DifferentiableAt ℝ V x) (hΨ : DifferentiableAt ℝ Ψ x) :
    inner ℝ (vorticity V x) (Ψ x) - inner ℝ (V x) (vorticity Ψ x)
      = div (fun y => crossR3 (V y) (Ψ y)) x := by
  have hFD := hasFDerivAt_crossR3 hV.hasFDerivAt hΨ.hasFDerivAt
  have hsum : ∀ i : Fin 3,
      inner ℝ (crossR3 (e i) (fderiv ℝ V x (e i))) (Ψ x)
          - inner ℝ (V x) (crossR3 (e i) (fderiv ℝ Ψ x (e i)))
        = inner ℝ (e i) (((crossBilin.flip (Ψ x)).comp (fderiv ℝ V x)
            + (crossBilin (V x)).comp (fderiv ℝ Ψ x)) (e i)) := by
    intro i
    have h1 : inner ℝ (crossR3 (e i) (fderiv ℝ V x (e i))) (Ψ x)
        = inner ℝ (e i) (crossR3 (fderiv ℝ V x (e i)) (Ψ x)) :=
      inner_crossR3_cyclic₁ _ _ _
    have h2 : - inner ℝ (V x) (crossR3 (e i) (fderiv ℝ Ψ x (e i)))
        = inner ℝ (e i) (crossR3 (V x) (fderiv ℝ Ψ x (e i))) := by
      have hA : - inner ℝ (V x) (crossR3 (e i) (fderiv ℝ Ψ x (e i)))
          = inner ℝ (V x) (crossR3 (fderiv ℝ Ψ x (e i)) (e i)) := by
        simp only [← inner_neg_right, neg_crossR3]
      have hB : inner ℝ (e i) (crossR3 (V x) (fderiv ℝ Ψ x (e i)))
          = inner ℝ (V x) (crossR3 (fderiv ℝ Ψ x (e i)) (e i)) :=
        inner_crossR3_cyclic₂ _ _ _
      rw [hA, hB]
    rw [sub_eq_add_neg, h1, h2, ← inner_add_right]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, crossBilin_apply]
  simp only [div_eq_sum_inner, vorticity_eq_sum_crossR3, hFD.fderiv]
  rw [sum_inner, inner_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => hsum i

theorem integral_vorticity_eq {V : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3}
    (hV : ContDiff ℝ 1 V)
    {Ψ : Work.FTS.BSSwirl.R3 → Work.FTS.BSSwirl.R3} (hΨ : ∀ n : ℕ, ContDiff ℝ n Ψ)
    (hΨc : HasCompactSupport Ψ) :
    ∫ x, inner ℝ (FiniteTimeSingularity.vorticity V x) (Ψ x)
      = ∫ x, inner ℝ (V x) (FiniteTimeSingularity.vorticity Ψ x) := by
  obtain ⟨hVd, hΨd⟩ : Differentiable ℝ V ∧ Differentiable ℝ Ψ :=
    ⟨hV.differentiable one_ne_zero, (hΨ 1).differentiable one_ne_zero⟩
  -- the field `G = V × Ψ` is `C¹` with compact support
  have hGc1 : ContDiff ℝ 1 (fun y => crossR3 (V y) (Ψ y)) := contDiff_crossR3 hV (hΨ 1)
  have hGcs : HasCompactSupport (fun y => crossR3 (V y) (Ψ y)) := by
    refine HasCompactSupport.of_support_subset_isCompact hΨc ?_
    intro x hx
    rw [Function.mem_support] at hx
    exact subset_tsupport _ (by
      rw [Function.mem_support]
      intro h0
      exact hx (by simp [h0]))
  have hdiv0 : ∫ x, div (fun y => crossR3 (V y) (Ψ y)) x = 0 :=
    integral_div_eq_zero_compact hGc1 hGcs
  -- the pointwise identity
  have hpt : ∀ x, inner ℝ (vorticity V x) (Ψ x) - inner ℝ (V x) (vorticity Ψ x)
      = div (fun y => crossR3 (V y) (Ψ y)) x :=
    fun x => inner_vorticity_sub_eq_div (hVd x) (hΨd x)
  -- the curl of `Ψ` is compactly supported
  have hvort_cs : HasCompactSupport (vorticity Ψ) := by
    refine HasCompactSupport.of_support_subset_isCompact hΨc ?_
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hcon
    refine hx ?_
    have h0 : Ψ =ᶠ[𝓝 x] 0 := by
      filter_upwards [(isClosed_tsupport Ψ).isOpen_compl.mem_nhds hcon] with z hz
      exact image_eq_zero_of_notMem_tsupport hz
    have hd : fderiv ℝ Ψ x = 0 := by rw [h0.fderiv_eq]; simp
    rw [vorticity_eq_sum_crossR3]
    simp [hd]
  -- integrability of both sides
  have hint1 : Integrable (fun x => inner ℝ (vorticity V x) (Ψ x)) :=
    (continuous_inner.comp ((continuous_vorticity hV).prodMk
      (hΨ 0).continuous)).integrable_of_hasCompactSupport (by
        refine HasCompactSupport.of_support_subset_isCompact hΨc ?_
        intro x hx
        rw [Function.mem_support] at hx
        exact subset_tsupport _ (by
          rw [Function.mem_support]
          intro h0
          exact hx (by simp [h0])))
  have hint2 : Integrable (fun x => inner ℝ (V x) (vorticity Ψ x)) :=
    (continuous_inner.comp (hV.continuous.prodMk
      (continuous_vorticity (hΨ 1)))).integrable_of_hasCompactSupport (by
        refine HasCompactSupport.of_support_subset_isCompact hvort_cs ?_
        intro x hx
        rw [Function.mem_support] at hx
        exact subset_tsupport _ (by
          rw [Function.mem_support]
          intro h0
          exact hx (by simp [h0])))
  have hzero : (∫ x, (inner ℝ (vorticity V x) (Ψ x) - inner ℝ (V x) (vorticity Ψ x))) = 0 := by
    rw [show (fun x => inner ℝ (vorticity V x) (Ψ x) - inner ℝ (V x) (vorticity Ψ x))
        = fun x => div (fun y => crossR3 (V y) (Ψ y)) x from funext hpt]
    exact hdiv0
  rw [integral_sub hint1 hint2] at hzero
  linarith

end

end Work.FTS.BSSwirl

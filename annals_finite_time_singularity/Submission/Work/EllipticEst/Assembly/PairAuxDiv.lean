/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise divergence identity of the `bslOp` pairing

With `β = (5-α)/α`,
`A = α²z^{β+2}cos θ(∂_zφ·Φ - ∂_zΦ·φ)` and `B = z^β cos θ(∂_θφ·Φ - ∂_θΦ·φ)` one has

  `z^β cos θ·(LΦ·φ - Φ·Lφ) = ∂_z A + ∂_θ B`,   `L = bslOp α`,

i.e. the weight `z^β cos θ` puts `L` into divergence form.  Proved by direct computation of the
two one-variable derivatives (product rule) together with the exponent identity
`α²(β+2) = α(5+α)` and `z^{β+2} = z^β z²`, `z^{β+1} = z^β z`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.Defs
import Submission.Work.EllipticEst.Assembly.PairDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Assembly

set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem pairDivIdentityAux {α : ℝ} (hα : 0 < α) {Φ φ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hΦz : HasDerivAt (fun z' => Φ z' θ) (Work.Spaces.pz Φ z θ) z)
    (hΦzz : HasDerivAt (fun z' => Work.Spaces.pz Φ z' θ) (Work.Spaces.pzIter 2 Φ z θ) z)
    (hφz : HasDerivAt (fun z' => φ z' θ) (Work.Spaces.pz φ z θ) z)
    (hφzz : HasDerivAt (fun z' => Work.Spaces.pz φ z' θ) (Work.Spaces.pzIter 2 φ z θ) z)
    (hΦt : HasDerivAt (fun θ' => Φ z θ') (Work.Spaces.pth Φ z θ) θ)
    (hΦtt : HasDerivAt (fun θ' => Work.Spaces.pth Φ z θ') (Work.Spaces.pthIter 2 Φ z θ) θ)
    (hφt : HasDerivAt (fun θ' => φ z θ') (Work.Spaces.pth φ z θ) θ)
    (hφtt : HasDerivAt (fun θ' => Work.Spaces.pth φ z θ') (Work.Spaces.pthIter 2 φ z θ) θ) :
    Work.EllipticEst.Assembly.pairWeight α (z, θ)
        * (Work.Elliptic.bslOp α Φ z θ * φ z θ - Φ z θ * Work.Elliptic.bslOp α φ z θ)
      = deriv (fun z' => Work.EllipticEst.Assembly.pairRad α Φ φ (z', θ)) z
        + deriv (fun θ' => Work.EllipticEst.Assembly.pairAng α Φ φ (z, θ')) θ := by
  have hcos : Real.cos θ ≠ 0 := by
    refine ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩)
    · linarith [Real.pi_pos, hθ.1]
    · linarith [Real.pi_pos, hθ.2]
  -- ### the derivative in `z`
  have hz1 : HasDerivAt (fun z' : ℝ => z' ^ (pairBeta α + 2))
      ((pairBeta α + 2) * z ^ (pairBeta α + 2 - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hz))
  have hz2 : HasDerivAt (fun z' : ℝ => Work.Spaces.pz φ z' θ * Φ z' θ
      - Work.Spaces.pz Φ z' θ * φ z' θ)
      ((Work.Spaces.pzIter 2 φ z θ * Φ z θ + Work.Spaces.pz φ z θ * Work.Spaces.pz Φ z θ)
        - (Work.Spaces.pzIter 2 Φ z θ * φ z θ
            + Work.Spaces.pz Φ z θ * Work.Spaces.pz φ z θ)) z :=
    (hφzz.mul hΦz).sub (hΦzz.mul hφz)
  have hz3 : HasDerivAt (fun z' : ℝ => Work.EllipticEst.Assembly.pairRad α Φ φ (z', θ))
      (α ^ 2 * (pairBeta α + 2) * z ^ (pairBeta α + 2 - 1) * Real.cos θ
          * (Work.Spaces.pz φ z θ * Φ z θ - Work.Spaces.pz Φ z θ * φ z θ)
        + (α ^ 2 * z ^ (pairBeta α + 2) * Real.cos θ)
          * ((Work.Spaces.pzIter 2 φ z θ * Φ z θ
                + Work.Spaces.pz φ z θ * Work.Spaces.pz Φ z θ)
            - (Work.Spaces.pzIter 2 Φ z θ * φ z θ
                + Work.Spaces.pz Φ z θ * Work.Spaces.pz φ z θ))) z :=
    (((hz1.const_mul (α ^ 2)).mul (hasDerivAt_const z (Real.cos θ))).mul hz2).congr_deriv (by
      simp only [Pi.mul_apply]
      ring)
  -- ### the derivative in `θ`
  have ht1 : HasDerivAt (fun θ' : ℝ => Real.cos θ') (-Real.sin θ) θ := Real.hasDerivAt_cos θ
  have ht2 : HasDerivAt (fun θ' : ℝ => Work.Spaces.pth φ z θ' * Φ z θ'
      - Work.Spaces.pth Φ z θ' * φ z θ')
      ((Work.Spaces.pthIter 2 φ z θ * Φ z θ + Work.Spaces.pth φ z θ * Work.Spaces.pth Φ z θ)
        - (Work.Spaces.pthIter 2 Φ z θ * φ z θ
            + Work.Spaces.pth Φ z θ * Work.Spaces.pth φ z θ)) θ :=
    (hφtt.mul hΦt).sub (hΦtt.mul hφt)
  have ht3 : HasDerivAt (fun θ' : ℝ => Work.EllipticEst.Assembly.pairAng α Φ φ (z, θ'))
      (z ^ pairBeta α * (-Real.sin θ)
          * (Work.Spaces.pth φ z θ * Φ z θ - Work.Spaces.pth Φ z θ * φ z θ)
        + (z ^ pairBeta α * Real.cos θ)
          * ((Work.Spaces.pthIter 2 φ z θ * Φ z θ
                + Work.Spaces.pth φ z θ * Work.Spaces.pth Φ z θ)
            - (Work.Spaces.pthIter 2 Φ z θ * φ z θ
                + Work.Spaces.pth Φ z θ * Work.Spaces.pth φ z θ))) θ :=
    (((hasDerivAt_const θ (z ^ pairBeta α)).mul ht1).mul ht2).congr_deriv (by
      simp only [Pi.mul_apply]
      ring)
  -- ### the two `pth (tan · ·)` terms
  have htanΦ : Work.Spaces.pth (fun z θ' => Real.tan θ' * Φ z θ') z θ
      = (1 / Real.cos θ ^ 2) * Φ z θ + Real.tan θ * Work.Spaces.pth Φ z θ := by
    have h5 : HasDerivAt (fun θ' : ℝ => Real.tan θ' * Φ z θ')
        ((1 / Real.cos θ ^ 2) * Φ z θ + Real.tan θ * Work.Spaces.pth Φ z θ) θ :=
      ((Real.hasDerivAt_tan hcos).mul hΦt).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun θ' => rfl))
    simpa only [Work.Spaces.pth] using h5.deriv
  have htanφ : Work.Spaces.pth (fun z θ' => Real.tan θ' * φ z θ') z θ
      = (1 / Real.cos θ ^ 2) * φ z θ + Real.tan θ * Work.Spaces.pth φ z θ := by
    have h5 : HasDerivAt (fun θ' : ℝ => Real.tan θ' * φ z θ')
        ((1 / Real.cos θ ^ 2) * φ z θ + Real.tan θ * Work.Spaces.pth φ z θ) θ :=
      ((Real.hasDerivAt_tan hcos).mul hφt).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun θ' => rfl))
    simpa only [Work.Spaces.pth] using h5.deriv
  have hLΦ : Work.Elliptic.bslOp α Φ z θ
      = -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 Φ z θ
        - (α * (5 + α) * z) * Work.Spaces.pz Φ z θ
        + (-(Work.Spaces.pthIter 2 Φ z θ)
            + ((1 / Real.cos θ ^ 2) * Φ z θ + Real.tan θ * Work.Spaces.pth Φ z θ)
            - 6 * Φ z θ) := by
    simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero, htanΦ]
  have hLφ : Work.Elliptic.bslOp α φ z θ
      = -(α ^ 2 * z ^ 2) * Work.Spaces.pzIter 2 φ z θ
        - (α * (5 + α) * z) * Work.Spaces.pz φ z θ
        + (-(Work.Spaces.pthIter 2 φ z θ)
            + ((1 / Real.cos θ ^ 2) * φ z θ + Real.tan θ * Work.Spaces.pth φ z θ)
            - 6 * φ z θ) := by
    simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero, htanφ]
  have hzA : z ^ (pairBeta α + 2) = z ^ pairBeta α * z ^ 2 := by
    rw [Real.rpow_add hz, Real.rpow_two]
  have hzB : z ^ (pairBeta α + 2 - 1) = z ^ pairBeta α * z := by
    rw [show pairBeta α + 2 - 1 = pairBeta α + 1 from by ring, Real.rpow_add hz, Real.rpow_one]
  rw [hz3.deriv, ht3.deriv, hLΦ, hLφ]
  simp only [Work.EllipticEst.Assembly.pairWeight_apply]
  rw [hzA, hzB, sq_mul_pairBeta_add_two (ne_of_gt hα), Real.tan_eq_sin_div_cos θ]
  field_simp
  ring

end Work.EllipticEst.Assembly

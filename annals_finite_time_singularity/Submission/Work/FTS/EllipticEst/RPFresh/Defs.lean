/-
Copyright: work module for the Elgindi finite-time singularity project.

# The angular weight `σ θ = sin(2θ)^{-η}` of the mixed Agmon finiteness lemma

Vocabulary for `Work.FTS.EllipticEst.RPFresh.MixedAGN_finite`: the weight `σ = sin(2θ)^{-η}`
appearing in the weighted angular integrals of §'Elliptic Regularity Estimates', its positivity
on `Iθ` and its logarithmic derivative `σ' = -2η cot(2θ) σ` on `(0,π/2)`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.RPFresh

open MeasureTheory Set intervalIntegral
open scoped Real Topology

set_option autoImplicit false

/-- The angular weight `σ θ = sin(2θ)^{-η}` (`η = 99/100`); definitionally `thEta`. -/
noncomputable def sg (θ : ℝ) : ℝ := (Real.sin (2*θ))^(-(Work.Spaces.eta))

theorem sg_def (θ : ℝ) : sg θ = (Real.sin (2*θ))^(-(Work.Spaces.eta)) := rfl

theorem sg_eq_thEta (θ : ℝ) : sg θ = Work.FTS.EllipticEst.thEta θ := rfl

theorem sin_two_nonneg_of_mem_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2*θ) := by
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem sg_nonneg {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ sg θ :=
  Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ hθ) _

/-- `σ θ > 0` on the open interval `(0,π/2)`. -/
theorem sg_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi/2)) : 0 < sg θ :=
  Real.rpow_pos_of_pos
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])) _

/-- The logarithmic derivative of the weight: `σ' = -2η cot(2θ) σ`. -/
theorem hasDerivAt_sg {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi/2)) :
    HasDerivAt sg (-(2*Work.Spaces.eta) * (Real.cot (2*θ) * sg θ)) θ := by
  have hsin : (0:ℝ) < Real.sin (2*θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hs2 : HasDerivAt (fun θ' : ℝ => Real.sin (2*θ')) (2*Real.cos (2*θ)) θ := by
    have h : HasDerivAt (fun θ' : ℝ => 2*θ') 2 θ := by
      simpa using (hasDerivAt_id θ).const_mul (2:ℝ)
    simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_sin (2*θ)).comp θ h
  have hbase : HasDerivAt (fun θ' : ℝ => (Real.sin (2*θ'))^(-(Work.Spaces.eta)))
      (-(Work.Spaces.eta) * (Real.sin (2*θ))^(-(Work.Spaces.eta)-1) * (2*Real.cos (2*θ))) θ := by
    have h := (Real.hasDerivAt_rpow_const (x := Real.sin (2*θ)) (p := -(Work.Spaces.eta))
      (Or.inl hsin.ne')).comp θ hs2
    simpa [Function.comp_def] using h
  have hderiv_eq : -(Work.Spaces.eta) * (Real.sin (2*θ))^(-(Work.Spaces.eta)-1) * (2*Real.cos (2*θ))
      = -(2*Work.Spaces.eta) * (Real.cot (2*θ) * sg θ) := by
    rw [sg_def, Real.cot_eq_cos_div_sin, div_eq_mul_inv]
    have key : (Real.sin (2*θ))^(-(Work.Spaces.eta)-1)
        = (Real.sin (2*θ))^(-(Work.Spaces.eta)) * (Real.sin (2*θ))⁻¹ := by
      rw [← Real.rpow_neg_one (Real.sin (2*θ)), ← Real.rpow_add hsin]
      ring_nf
    rw [key]; ring
  rw [hderiv_eq] at hbase
  exact hbase

end Work.FTS.EllipticEst.RPFresh

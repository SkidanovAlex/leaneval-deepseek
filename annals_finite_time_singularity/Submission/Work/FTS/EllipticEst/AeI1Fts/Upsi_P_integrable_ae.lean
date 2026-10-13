import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.N_bound
import Submission.Work.FTS.EllipticEst.AeI1Fts.Upsi_P_ae_Aux
import Submission.Work.FTS.EllipticEst.AeI1Fts.aesm_deriv_U_mul_psi
import Submission.Work.FTS.EllipticEst.AeI1Fts.Upsi_P_ae_value_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeI1Fts

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 1600000

theorem Upsi_P_integrable_ae (α : ℝ) (u : ℝ → ℝ → ℝ) (χ ψ : ℝ → ℝ)
    (hS : Work.FTS.EllipticEst.SmoothOpen u)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u))
    (hV : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ)
    (hZ : MeasureTheory.IntegrableOn
      (fun z => z ^ 2 * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iz)
    (hχm : Measurable χ) (hχnn : ∀ z ∈ Work.Spaces.Iz, 0 ≤ χ z)
    (hχ : ∃ C : ℝ, ∀ z ∈ Work.Spaces.Iz, χ z * (1 + z) ^ 4 ≤ C * z ^ 4)
    (hψcd : ContDiff ℝ 2 ψ)
    (hψ : ∃ C : ℝ, ∀ θ, (ψ θ) ^ 2 ≤ C) (hψ' : ∃ C : ℝ, ∀ θ, (deriv ψ θ) ^ 2 ≤ C) :
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * χ z
        * ∫ θ in Work.Spaces.Iθ,
            (deriv (fun θ' => Work.FTS.EllipticEst.AeI1Fts.U u z θ' * ψ θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      Work.Spaces.Iz := by
  obtain ⟨Cψ, hCψ⟩ := hψ
  obtain ⟨Cψ', hCψ'⟩ := hψ'
  obtain ⟨Cχ, hCχ⟩ := hχ
  have hCψ0 : 0 ≤ Cψ := le_trans (sq_nonneg (ψ 0)) (hCψ 0)
  have hCψ'0 : 0 ≤ Cψ' := le_trans (sq_nonneg (deriv ψ 0)) (hCψ' 0)
  have hCχ0 : 0 ≤ Cχ := by
    have h1 := hCχ 1 (by norm_num [Work.Spaces.Iz])
    have h2 := hχnn 1 (by norm_num [Work.Spaces.Iz])
    nlinarith
  -- the two delegated ingredients
  have hB := aesm_deriv_U_mul_psi u ψ hS hψcd
  have hC := Upsi_P_ae_value_bound α u χ ψ Cχ Cψ Cψ' hS hψcd hU hV hχnn hCχ hCψ hCψ'
    hCχ0 hCψ0 hCψ'0
  -- integrability of the dominating function
  have hU' : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.AeI1Fts.U u) := hU
  have hMint : MeasureTheory.Integrable
      (fun z => 2 * Cψ * Cχ * (z ^ 2 * ∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pz (Work.Spaces.pth u) z θ) ^ 2
                * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + 2 * Cψ' * Cχ * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.AeI1Fts.U u) z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (hZ.const_mul _).add (hU'.2.const_mul _)
  -- measurability of the target
  have hmarg : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        (deriv (fun θ' => Work.FTS.EllipticEst.AeI1Fts.U u z θ' * ψ θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    hB.integral_prod_right' (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
  have hwχm : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2 * χ z) := by
    have heq : (fun z : ℝ => (Work.Spaces.w z) ^ 2 * χ z)
        = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 * χ z := by
      funext z; simp only [Work.Spaces.w]
    rw [heq]; fun_prop
  have hφmeas : MeasureTheory.AEStronglyMeasurable
      (fun z => (Work.Spaces.w z) ^ 2 * χ z
        * ∫ θ in Work.Spaces.Iθ,
            (deriv (fun θ' => Work.FTS.EllipticEst.AeI1Fts.U u z θ' * ψ θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (hwχm.aestronglyMeasurable).mul hmarg
  rw [MeasureTheory.IntegrableOn]
  refine MeasureTheory.Integrable.mono' hMint hφmeas ?_
  filter_upwards [hC, MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hCz hz
  have hJnn : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (deriv (fun θ' => Work.FTS.EllipticEst.AeI1Fts.U u z θ' * ψ θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
      mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (Work.FTS.EllipticEst.AngSecond.sin_two_nonneg hθ) _))
  have hφnn : 0 ≤ (Work.Spaces.w z) ^ 2 * χ z
        * ∫ θ in Work.Spaces.Iθ,
            (deriv (fun θ' => Work.FTS.EllipticEst.AeI1Fts.U u z θ' * ψ θ') θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (hχnn z hz)) hJnn
  rw [Real.norm_of_nonneg hφnn]
  exact hCz

end Work.FTS.EllipticEst.AeI1Fts

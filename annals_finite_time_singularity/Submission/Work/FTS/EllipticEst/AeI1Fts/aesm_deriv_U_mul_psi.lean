import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.AeI1Fts.Upsi_P_ae_Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Joint (a.e.) strong measurability of `(∂_θ(U u · ψ))^2 sin(2θ)^{-η}`

For a datum `u` of class `SmoothOpen` (i.e. `C^∞` on the open quadrant `(0,∞) × (0,π/2)`)
and a `C²` function `ψ`, the function

  `p ↦ (deriv (fun θ' => U u p.1 θ' * ψ θ') p.2)^2 * sin(2 p.2)^{-η}`

is almost everywhere strongly measurable for the product of the restrictions of Lebesgue
measure to `Iz = [0,∞)` and `Iθ = [0,π/2]`.

The proof is a reduction to the open quadrant: `Iz ×ˢ Iθ` agrees a.e. with the open quadrant
`Q0`, on which the product rule `deriv_U_mul_eq` computes the derivative as the *continuous*
function `V u · ψ + U u · ∂ψ`; the uncurried expression is continuous on `Q0`
(`U` and `V` are uncurried `pz`-derivatives of a `SmoothOpen` datum, and `ψ`, `deriv ψ`,
`sin(2·)^{-η}` are continuous there), so `Work.Spaces.aesm_of_continuousOn_Qd` applies.
-/

namespace Work.FTS.EllipticEst.AeI1Fts

theorem aesm_deriv_U_mul_psi (u : ℝ → ℝ → ℝ) (ψ : ℝ → ℝ)
    (hS : Work.FTS.EllipticEst.SmoothOpen u) (hψcd : ContDiff ℝ 2 ψ) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        (deriv (fun θ' => Work.FTS.EllipticEst.AeI1Fts.U u p.1 θ' * ψ θ') p.2) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- The product-rule value of the derivative, as a function of `p : ℝ × ℝ`.
  have hgc : ContinuousOn (fun p : ℝ × ℝ =>
        (Work.FTS.EllipticEst.AeI1Fts.V u p.1 p.2 * ψ p.2
          + Work.FTS.EllipticEst.AeI1Fts.U u p.1 p.2 * deriv ψ p.2) ^ 2
          * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) Work.FTS.EllipticEst.Q0 := by
    have hUc : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeI1Fts.U u p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      have h := (hS.pz).continuousOn
      have hfun : (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeI1Fts.U u p.1 p.2)
          = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz u) p := rfl
      rw [hfun]
      exact continuous_fst.continuousOn.mul h
    have hVc : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeI1Fts.V u p.1 p.2)
        Work.FTS.EllipticEst.Q0 := by
      have h := (hS.pth).pz.continuousOn
      have hfun : (fun p : ℝ × ℝ => Work.FTS.EllipticEst.AeI1Fts.V u p.1 p.2)
          = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz (Work.Spaces.pth u)) p :=
        rfl
      rw [hfun]
      exact continuous_fst.continuousOn.mul h
    have hψc : ContinuousOn (fun p : ℝ × ℝ => ψ p.2) Work.FTS.EllipticEst.Q0 :=
      (hψcd.continuous.comp continuous_snd).continuousOn
    have hψ'c : ContinuousOn (fun p : ℝ × ℝ => deriv ψ p.2) Work.FTS.EllipticEst.Q0 :=
      ((hψcd.continuous_deriv (by norm_num)).comp continuous_snd).continuousOn
    have hsinbase : Continuous (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
      Real.continuous_sin.comp (continuous_const.mul continuous_snd)
    have hsin : ContinuousOn (fun p : ℝ × ℝ =>
        (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta))) Work.FTS.EllipticEst.Q0 :=
      hsinbase.continuousOn.rpow_const
        (fun p hp => Or.inl (by
          obtain ⟨-, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
          exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
            (by linarith [Real.pi_pos]))))
    exact ((hVc.mul hψc).add (hUc.mul hψ'c)).pow 2 |>.mul hsin
  have hgaesm := Work.Spaces.aesm_of_continuousOn_Qd _ hgc
  refine MeasureTheory.AEStronglyMeasurable.congr hgaesm ?_
  -- The product measure sees `Iz ×ˢ Iθ` as the open quadrant.
  have hUm : MeasurableSet Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  have hz : Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) :=
    MeasureTheory.Ioi_ae_eq_Ici.symm
  have hθ : Work.Spaces.Iθ =ᵐ[MeasureTheory.volume] Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    MeasureTheory.Ioo_ae_eq_Icc.symm
  have hprod : (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)) =ᵐ[MeasureTheory.volume.prod
      MeasureTheory.volume] Work.FTS.EllipticEst.Q0 :=
    MeasureTheory.Measure.set_prod_ae_eq hz hθ
  rw [MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.Measure.restrict_congr_set hprod]
  filter_upwards [MeasureTheory.ae_restrict_mem hUm] with p hp
  obtain ⟨hzpos, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  rw [deriv_U_mul_eq hS hψcd hzpos ⟨hθ0, hθ1⟩]

end Work.FTS.EllipticEst.AeI1Fts

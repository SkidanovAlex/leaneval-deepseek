import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integration by parts on `ℝ` with one exceptional point

`Work.FTS.PressureOn.offPlanes.ibp_except_zero`: if `Ψ` is differentiable everywhere with derivative
`Ψp`, `G` is differentiable everywhere except at `0` with derivative `Gp` there, both are continuous,
the products `Ψ * Gp` and `G * Ψp` are integrable and `G * Ψ` vanishes at `±∞`, then

  `∫ t, Ψ t * Gp t = - ∫ t, Ψp t * G t`.

The proof splits `ℝ = (-∞,0] ∪ (0,∞)` and applies the half-line integration by parts
`MeasureTheory.integral_Iic_mul_deriv_eq_deriv_mul` and
`MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul`; the two boundary terms at `0` cancel by
continuity.
-/

open MeasureTheory Filter Topology

namespace Work.FTS.PressureOn.offPlanes

theorem ibp_except_zero {G Gp Ψ Ψp : ℝ → ℝ}
    (hΨd : ∀ t, HasDerivAt Ψ (Ψp t) t)
    (hGd : ∀ t, t ≠ 0 → HasDerivAt G (Gp t) t)
    (hGc : Continuous G) (hΨc : Continuous Ψ)
    (hΨGp : Integrable (fun t => Ψ t * Gp t))
    (hΨpG : Integrable (fun t => Ψp t * G t))
    (hbot : Tendsto (fun t => Ψ t * G t) atBot (𝓝 0))
    (htop : Tendsto (fun t => Ψ t * G t) atTop (𝓝 0)) :
    ∫ t, Ψ t * Gp t = -∫ t, Ψp t * G t := by
  have hzeroR : Tendsto (fun t => Ψ t * G t) (𝓝[>] (0 : ℝ)) (𝓝 (Ψ 0 * G 0)) :=
    (hΨc.mul hGc).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hzeroL : Tendsto (fun t => Ψ t * G t) (𝓝[<] (0 : ℝ)) (𝓝 (Ψ 0 * G 0)) :=
    (hΨc.mul hGc).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hR : ∫ t in Set.Ioi (0 : ℝ), Ψ t * Gp t = 0 - (Ψ 0 * G 0) - ∫ t in Set.Ioi (0:ℝ), Ψp t * G t := by
    apply integral_Ioi_mul_deriv_eq_deriv_mul (a := 0) (a' := Ψ 0 * G 0) (b' := 0)
    · exact fun x _ => hΨd x
    · exact fun x hx => hGd x (ne_of_gt hx)
    · exact hΨGp.integrableOn
    · exact hΨpG.integrableOn
    · exact hzeroR
    · exact htop
  have hL : ∫ t in Set.Iic (0 : ℝ), Ψ t * Gp t = (Ψ 0 * G 0) - 0 - ∫ t in Set.Iic (0:ℝ), Ψp t * G t := by
    apply integral_Iic_mul_deriv_eq_deriv_mul (a := 0) (a' := Ψ 0 * G 0) (b' := 0)
    · exact fun x _ => hΨd x
    · exact fun x hx => hGd x (ne_of_lt hx)
    · exact hΨGp.integrableOn
    · exact hΨpG.integrableOn
    · exact hzeroL
    · exact hbot
  have hsplit : ∫ t, Ψ t * Gp t = (∫ t in Set.Iic 0, Ψ t * Gp t) + ∫ t in Set.Ioi 0, Ψ t * Gp t := by
    rw [← integral_add_compl measurableSet_Iic hΨGp, Set.compl_Iic]
  have hsplit2 : ∫ t, Ψp t * G t = (∫ t in Set.Iic 0, Ψp t * G t) + ∫ t in Set.Ioi 0, Ψp t * G t := by
    rw [← integral_add_compl measurableSet_Iic hΨpG, Set.compl_Iic]
  rw [hsplit, hL, hR, hsplit2]
  ring

end Work.FTS.PressureOn.offPlanes

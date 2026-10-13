/-
# The compact-support coercivity of `𝓛 - (3/(1+z))D_θ`

This file collects the additivity of `wip` and the coercivity estimate

  `(1/2 - 3α/10) · wip ρ v v ≤ wip ρ (Aop v) v`,  `ρ = thetaW α`,

for functions `v` on which the two integration-by-parts of the paper are valid: the
`z`-integration by parts behind `wip_L_self` (here `IBP v`) and the `θ`-integration by
parts of the transport term (the `hvan`/`hvan2` vanishing conditions at the angular
boundary).  It is the estimate applied to the cut-off functions in `theta_coercive`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Coercivity.thetaAux
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.wip_L_self
import Submission.Work.Coercivity.wip_eq_integral_prod
import Submission.Work.Coercivity.wip_TrV_ge

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- The transport term `-(3/(1+z)) D_θ v` of `Aop`. -/
def TrV (v : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun z θ => -(3 / (1 + z)) * Spaces.Dth v z θ

theorem wip_add_left {ρ g h k : ℝ → ℝ → ℝ}
    (hg : IntegrableOn (Function.uncurry (fun z θ => g z θ * k z θ * ρ z θ)) (Spaces.Iz ×ˢ Spaces.Iθ))
    (hh : IntegrableOn (Function.uncurry (fun z θ => h z θ * k z θ * ρ z θ)) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    wip ρ (fun z θ => g z θ + h z θ) k = wip ρ g k + wip ρ h k := by
  have hvol : MeasureTheory.volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ)
      = (MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ) := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  have hG : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => g p.1 p.2 * k p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)) := by
    rw [← hvol]; exact hg
  have hH : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => h p.1 p.2 * k p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)) := by
    rw [← hvol]; exact hh
  have hGH : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (g p.1 p.2 + h p.1 p.2) * k p.1 p.2 * ρ p.1 p.2)
      ((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)) := by
    refine (hG.add hH).congr ?_
    filter_upwards with p
    simp only [Pi.add_apply]
    ring
  have hGHo : IntegrableOn
      (Function.uncurry (fun z θ => (g z θ + h z θ) * k z θ * ρ z θ)) (Spaces.Iz ×ˢ Spaces.Iθ) := by
    unfold MeasureTheory.IntegrableOn
    rw [hvol]; exact hGH
  rw [wip_eq_integral_prod ρ (fun z θ => g z θ + h z θ) k hGHo,
      wip_eq_integral_prod ρ g k hg, wip_eq_integral_prod ρ h k hh,
      ← MeasureTheory.integral_add hG hH]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with p
  ring

theorem wip_Aop_ge (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (v : ℝ → ℝ → ℝ) (hv : IBP v)
    (hvan : ∀ z, 0 < z → Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α - 1)) * (v z θ) ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hvan2 : ∀ z, 0 < z → Filter.Tendsto (fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α - 1)) * (v z θ) ^ 2) (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds 0))
    (hint_v : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => (v z θ) ^ 2 * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))) (Spaces.Iz ×ˢ Spaces.Iθ))
    (hint_L : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => L v z θ * v z θ * Spaces.w z ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α)))) (Spaces.Iz ×ˢ Spaces.Iθ))
    (hint_T : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => thetaW α z θ * (Spaces.Dth v z θ) * v z θ / (1 + z))) (Spaces.Iz ×ˢ Spaces.Iθ)) :
    (1 / 2 - 3 * α / 10) * wip (thetaW α) v v ≤ wip (thetaW α) (Aop v) v := by
  have hL := wip_L_self v hv (fun θ => (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) hint_v hint_L
  have hint2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => thetaW α z θ * (v z θ) ^ 2)) (Spaces.Iz ×ˢ Spaces.Iθ) :=
    hint_v.congr (Filter.Eventually.of_forall fun p => by
      obtain ⟨a, b⟩ := p
      simp only [Function.uncurry, thetaW]; ring)
  have hT := wip_TrV_ge α hα hα1 v hv.smooth hvan hvan2 hint_T hint2
  have hint_L' : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => L v z θ * v z θ * thetaW α z θ)) (Spaces.Iz ×ˢ Spaces.Iθ) :=
    hint_L.congr (Filter.Eventually.of_forall fun p => by
      obtain ⟨a, b⟩ := p
      simp only [Function.uncurry, thetaW]; ring)
  have hh : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ => TrV v z θ * v z θ * thetaW α z θ)) (Spaces.Iz ×ˢ Spaces.Iθ) := by
    refine (hint_T.const_mul (-3)).congr ?_
    filter_upwards with p
    obtain ⟨a, b⟩ := p
    simp only [Function.uncurry, TrV]
    ring
  have hlin := wip_add_left (ρ := thetaW α) (g := L v) (h := TrV v) (k := v) hint_L' hh
  have hAop : Aop v = fun z θ => L v z θ + TrV v z θ := by
    funext z θ; simp only [Aop, TrV]; ring
  have hL' : wip (thetaW α) (L v) v = 1 / 2 * wip (thetaW α) v v := hL
  have hT' : -(3 * α / 10) * wip (thetaW α) v v ≤ wip (thetaW α) (TrV v) v := hT
  rw [hAop, hlin, hL']
  nlinarith [hT']

end Work.Coercivity

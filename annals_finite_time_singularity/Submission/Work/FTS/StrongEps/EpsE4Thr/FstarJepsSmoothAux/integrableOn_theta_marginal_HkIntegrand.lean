import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

open MeasureTheory Set Filter
open scoped Real Topology

set_option maxHeartbeats 800000
-- `hcd : c ≤ d` is only an (unused) hypothesis of the statement; `c ≤ d` guarantees that the
-- interval `Icc c d` below is the one meant, but the argument only needs `0 < c`.
set_option linter.unusedVariables false

/-- **Integrability of the angular marginal of the `ℋ^1`-integrand.**  For `W` smooth on the
open quadrant and honest in `ℋ^1`, and for `0 < c ≤ d`, the function
`θ ↦ ∫_{c}^{d} HkIntegrand α 1 W z θ dz` is integrable on `(0,π/2)`.

The proof is Tonelli for nonnegative functions together with the finiteness of the *iterated*
integral supplied by `HkMem`:

* the uncurried integrand `p ↦ HkIntegrand α 1 W p.1 p.2` is continuous on the open quadrant
  (`SmoothOpen.continuousOn_HkIntegrand`), hence a.e. strongly measurable for the product of the
  restrictions of Lebesgue measure to `Iz` and `Iθ` (`aesm_of_continuousOn_Qd`);
* Tonelli turns the double integral over `Iz ×ˢ Iθ` of `ofReal` of the integrand into the
  iterated integral of `ofReal`s; the inner integrals are the `ofReal`s of the honest integrals
  because each angular slice is integrable (`HkMem.1`), and the outer one is the `ofReal` of
  `HkSq α 1 W` because the radial marginal is integrable (`HkMem.2`);
* the rectangle `Icc c d ×ˢ Ioo 0 (π/2)` sits inside `Iz ×ˢ Iθ` (as `0 < c`), so the measure
  `(volume.restrict (Icc c d)).prod (volume.restrict (Ioo 0 (π/2)))` is at most
  `(volume.restrict Iz).prod (volume.restrict Iθ)` (`Measure.prod_mono`), and the ℓ-integral of
  the nonnegative integrand over the small rectangle is finite (`lintegral_mono'`);
* this gives `HasFiniteIntegral`, hence `Integrable`, of the uncurried integrand on the rectangle
  (unfolding `HasFiniteIntegral` and rewriting `‖·‖ₑ = ofReal (·)` with `lintegral_congr`), and
  `Integrable.integral_prod_right` integrates out `z`. -/
theorem integrableOn_theta_marginal_HkIntegrand {α : ℝ} {W : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen W) (hmem : Work.Spaces.HkMem α 1 W)
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    MeasureTheory.IntegrableOn
      (fun θ : ℝ => ∫ z in Set.Icc c d, Work.Spaces.HkIntegrand α 1 W z θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hIz : MeasurableSet Work.Spaces.Iz := measurableSet_Ici
  have hIθ : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hrect : MeasurableSet (Set.Icc c d ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    measurableSet_Icc.prod measurableSet_Ioo
  have hsub : Set.Icc c d ×ˢ Set.Ioo 0 (Real.pi / 2) ⊆ Work.FTS.EllipticEst.Q0 := by
    intro p hp
    obtain ⟨h1, h2⟩ := Set.mem_prod.mp hp
    exact ⟨lt_of_lt_of_le hc (Set.mem_Icc.mp h1).1, h2⟩
  -- the uncurried integrand is continuous on the closed rectangle
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 1 W p.1 p.2)
      (Set.Icc c d ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (hsm.continuousOn_HkIntegrand α 1).mono hsub
  -- a.e. strong measurability of the integrand for the product measure on the rectangle
  have hAEs : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 1 W p.1 p.2)
      ((volume.restrict (Set.Icc c d)).prod (volume.restrict (Set.Ioo 0 (Real.pi / 2)))) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hcont.aestronglyMeasurable hrect
  -- a.e. measurability of `ofReal` of the integrand over the full quadrant
  have hAEMbig : AEMeasurable
      (Function.uncurry (fun z θ : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α 1 W z θ)))
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (Work.Spaces.aesm_of_continuousOn_Qd
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 1 W p.1 p.2)
      (hsm.continuousOn_HkIntegrand α 1)).aemeasurable.ennreal_ofReal
  -- Tonelli: the double ℓ-integral over the quadrant is the `ofReal` of `HkSq α 1 W`
  have hbig : ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 1 W p.1 p.2)
        ∂((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ))
      = ENNReal.ofReal (Work.Spaces.HkSq α 1 W) := by
    rw [← MeasureTheory.lintegral_lintegral (μ := volume.restrict Work.Spaces.Iz)
      (ν := volume.restrict Work.Spaces.Iθ) hAEMbig]
    rw [MeasureTheory.lintegral_congr_ae (MeasureTheory.ae_restrict_of_forall_mem hIz
      (fun z hz => (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 z hz)
        (Filter.Eventually.of_forall fun θ =>
          Work.Spaces.HkIntegrand_nonneg α 1 W z θ)).symm))]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2
      (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 1 W z θ)]
    rfl
  -- the rectangle is contained in the quadrant
  have hAB : Set.Icc c d ⊆ Work.Spaces.Iz :=
    fun x hx => le_trans hc.le (Set.mem_Icc.mp hx).1
  have hBθ : Set.Ioo 0 (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun x hx => ⟨hx.1.le, hx.2.le⟩
  -- the rectangle measure is dominated by the quadrant measure
  have hmono : (volume.restrict (Set.Icc c d)).prod (volume.restrict (Set.Ioo 0 (Real.pi / 2)))
      ≤ (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
    MeasureTheory.Measure.prod_mono
      (MeasureTheory.Measure.restrict_mono hAB le_rfl)
      (MeasureTheory.Measure.restrict_mono hBθ le_rfl)
  -- the ℓ-integral of `ofReal` of the integrand over the rectangle is finite
  have hsmall : ∫⁻ p, ENNReal.ofReal (Work.Spaces.HkIntegrand α 1 W p.1 p.2)
        ∂((volume.restrict (Set.Icc c d)).prod (volume.restrict (Set.Ioo 0 (Real.pi / 2))))
      ≤ ENNReal.ofReal (Work.Spaces.HkSq α 1 W) :=
    le_trans (MeasureTheory.lintegral_mono' hmono le_rfl) hbig.le
  have hfin : MeasureTheory.HasFiniteIntegral
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 1 W p.1 p.2)
      ((volume.restrict (Set.Icc c d)).prod (volume.restrict (Set.Ioo 0 (Real.pi / 2)))) := by
    show ∫⁻ p, ‖Work.Spaces.HkIntegrand α 1 W p.1 p.2‖ₑ
      ∂((volume.restrict (Set.Icc c d)).prod (volume.restrict (Set.Ioo 0 (Real.pi / 2)))) < ⊤
    rw [MeasureTheory.lintegral_congr (g := fun p : ℝ × ℝ =>
      ENNReal.ofReal (Work.Spaces.HkIntegrand α 1 W p.1 p.2))
      (fun p => by
        rw [Real.enorm_eq_ofReal_abs,
          abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α 1 W p.1 p.2)])]
    exact lt_of_le_of_lt hsmall ENNReal.ofReal_lt_top
  have hInt : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 1 W p.1 p.2)
      ((volume.restrict (Set.Icc c d)).prod (volume.restrict (Set.Ioo 0 (Real.pi / 2)))) :=
    ⟨hAEs, hfin⟩
  exact MeasureTheory.Integrable.integral_prod_right hInt

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

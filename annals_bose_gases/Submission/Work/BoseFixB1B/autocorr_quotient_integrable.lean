import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.pairMassB_defs
import Submission.Work.BoseFixB3.CS.Pieces.convScale_ge_of_norm_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.autocorr_quotient_integrable`

The `L¹`-integrability of the **one-body pair mass density** of the sliding box `B(u)`:

    z ↦ (g₀(z) / ((χ_M⋆χ_M)(z/(ℓd))·(χ⋆χ)(z/ℓ))) · A(z) ,   A(z) = ∫_x χ_{B(u)}(x)·χ_{B(u)}(x−z) ,

where `g₀ = v(1−w₀)` is the chosen scattering numerator (`Submission.ScatKernelChosen.g0`) and
`χ_{B(u)}` is the sliding cutoff (`Submission.BoseGases.chiSmallB`).  This is exactly the
`z`-integrand produced by the Fubini/change-of-variables form
`Work.BoseFixB1.wSmallPair_integral_eq_autocorr` of the localised one-body kernel
`Work.BoseFixB1.w1MassB`, so the lemma is the missing integrability side condition of that
identity at a *general* box parameter `u` (the existing corpus proof of the `u = 0` instance —
`Work.BoseFixB1S.w1MassB_zero_ge` — has the `u = 0`-specialised private helpers duplicated below
at general `u`).

## The mathematics

Two facts do all the work.

* **Support.**  `supp g₀ ⊆ ball 0 R` (`g₀ = v(1−w₀)` and `supp v ⊆ ball 0 R`), so the quotient is
  only evaluated at `‖z‖ ≤ R ≤ ℓd/16` and `‖z‖ ≤ R ≤ ℓ/16`; there the two renormalisation
  denominators are bounded below by the *positive* constants `smallConvLower M` and `c₀`
  (`Work.SmallBoxSliding.conv3Small_coord_lower` resp.
  `Work.BoseFixB3.CS.Pieces.convScale_ge_of_norm_le`).  Hence

      |g₀(z) / ((χ_M⋆χ_M)(z/(ℓd))·(χ⋆χ)(z/ℓ))| ≤ ‖g₀(z)‖ / (smallConvLower M · c₀)

  for **every** `z` (the trivial case `g₀(z) = 0` included).

* **Autocorrelation bound.**  Cauchy–Schwarz (`2ab ≤ a² + b²`) and translation invariance of
  Lebesgue measure give `0 ≤ A(z) ≤ ∫ χ_{B(u)}² = chiMass M ℓ d u` — a bound *uniform in `z`*
  (and depending on `u` only through the fixed constant `chiMass M ℓ d u`).

Multiplying the two bounds dominates the target integrand by the integrable function
`(chiMass M ℓ d u / (smallConvLower M · c₀))·‖g₀‖`; a.e. strong measurability is the product of
`g₀ / (continuous denominator)` with the autocorrelation (an integral in `x` of a continuous
function of `(z, x)`).
-/

namespace Work.BoseFixB1B

open MeasureTheory Metric
open scoped Real Topology

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ### The two elementary inputs -/

/-- The sliding autocorrelation is nonnegative (the integrand is a product of two nonnegative
factors). -/
private lemma autocorr_nonneg_u {M : ℕ} (ℓ d : ℝ) (u z : E3) :
    0 ≤ Work.BoseFixB1.autocorr (M := M) ℓ d u z := by
  rw [Work.BoseFixB1.autocorr_apply]
  exact integral_nonneg fun x => mul_nonneg
    (Submission.BoseGases.chiSmallB_nonneg M ℓ d u x)
    (Submission.BoseGases.chiSmallB_nonneg M ℓ d u (x - z))

/-- The square of the sliding cutoff is integrable. -/
private lemma chiSmallB_sq_integrable_u {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u : E3) :
    Integrable (fun x : E3 => (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2) volume :=
  ((Submission.BoseGases.chiSmallB_continuous hM hℓ hd u).memLp_of_hasCompactSupport
    (Submission.BoseGases.chiSmallB_hasCompactSupport hM hℓ u)).integrable_sq

/-- **Cauchy–Schwarz for the sliding autocorrelation**: `A(z) ≤ chiMass`, uniformly in the lag
`z` (and depending on the box parameter `u` only through the constant `chiMass M ℓ d u`). -/
private lemma autocorr_le_chiMass_u {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u z : E3) :
    Work.BoseFixB1.autocorr (M := M) ℓ d u z ≤ Work.SmallBoxSliding.chiMass M ℓ d u := by
  rw [Work.BoseFixB1.autocorr_apply, Work.SmallBoxSliding.chiMass_def]
  have hint := chiSmallB_sq_integrable_u hM hℓ hd u
  have hshift : Integrable
      (fun x : E3 => (Submission.BoseGases.chiSmallB M ℓ d u (x - z)) ^ 2) volume :=
    hint.comp_sub_right z
  have hmain := integral_mono_of_nonneg
    (f := fun x : E3 => Submission.BoseGases.chiSmallB M ℓ d u x
      * Submission.BoseGases.chiSmallB M ℓ d u (x - z))
    (g := fun x : E3 => (1 / 2) * (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2
      + (1 / 2) * (Submission.BoseGases.chiSmallB M ℓ d u (x - z)) ^ 2)
    (Filter.Eventually.of_forall fun x => mul_nonneg
      (Submission.BoseGases.chiSmallB_nonneg M ℓ d u x)
      (Submission.BoseGases.chiSmallB_nonneg M ℓ d u (x - z)))
    ((hint.const_mul (1 / 2)).add (hshift.const_mul (1 / 2)))
    (Filter.Eventually.of_forall fun x => by
      nlinarith [sq_nonneg (Submission.BoseGases.chiSmallB M ℓ d u x
        - Submission.BoseGases.chiSmallB M ℓ d u (x - z))])
  have hval : (∫ x : E3, ((1 / 2) * (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2
      + (1 / 2) * (Submission.BoseGases.chiSmallB M ℓ d u (x - z)) ^ 2))
      = ∫ x : E3, (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2 := by
    rw [integral_add (hint.const_mul (1 / 2)) (hshift.const_mul (1 / 2)), integral_const_mul,
      integral_const_mul,
      integral_sub_right_eq_self (fun y : E3 => (Submission.BoseGases.chiSmallB M ℓ d u y) ^ 2) z]
    ring
  rw [hval] at hmain
  exact hmain

/-! ### The target -/

theorem autocorr_quotient_integrable {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR1 : R ≤ ℓ * d / 16) (hR2 : R ≤ ℓ / 16) (u : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
        (Submission.BoseGases.g0 v h z
            / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
                * Submission.BoseGases.convScale ℓ z))
          * Work.BoseFixB1.autocorr (M := M) ℓ d u z) MeasureTheory.volume := by
  classical
  have hL : 0 < ℓ * d := mul_pos hℓ hd
  obtain ⟨c₀, hc₀pos, hc₀⟩ := Work.BoseFixB3.CS.Pieces.convScale_ge_of_norm_le
  have hG0 : Integrable (Submission.BoseGases.g0 v h) volume :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  -- ## a.e. strong measurability of the integrand
  have hcsm : Continuous
      (fun z : E3 => Submission.BoseGases.convScaleSmall M (ℓ * d) z) := by
    unfold Submission.BoseGases.convScaleSmall
    exact (Submission.BoseGases.conv3Small_continuous hM).comp (by fun_prop)
  have hden : AEMeasurable (fun z : E3 => Submission.BoseGases.convScaleSmall M (ℓ * d) z
      * Submission.BoseGases.convScale ℓ z) volume :=
    (hcsm.mul (Submission.BoseGases.convScale_continuous ℓ)).aemeasurable
  have hquot : AEMeasurable (fun z : E3 => Submission.BoseGases.g0 v h z
      / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
          * Submission.BoseGases.convScale ℓ z)) volume :=
    hG0.aemeasurable.div hden
  have hauto : AEMeasurable (fun z : E3 => Work.BoseFixB1.autocorr (M := M) ℓ d u z) volume := by
    have hcont : Continuous (fun x : E3 => Submission.BoseGases.chiSmallB M ℓ d u x) :=
      Submission.BoseGases.chiSmallB_continuous hM hℓ hd u
    have hc : Continuous (fun p : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d u p.2
        * Submission.BoseGases.chiSmallB M ℓ d u (p.2 - p.1)) :=
      (hcont.comp continuous_snd).mul (hcont.comp (continuous_snd.sub continuous_fst))
    simpa only [Work.BoseFixB1.autocorr_apply] using
      hc.aestronglyMeasurable.integral_prod_right'.aemeasurable
  have haesm : AEStronglyMeasurable (fun z : E3 =>
      (Submission.BoseGases.g0 v h z
          / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
              * Submission.BoseGases.convScale ℓ z))
        * Work.BoseFixB1.autocorr (M := M) ℓ d u z) volume :=
    (hquot.mul hauto).aestronglyMeasurable
  -- ## the dominating integrable function
  have hbound : Integrable (fun z : E3 =>
      (Work.SmallBoxSliding.chiMass M ℓ d u
          / (Work.SmallBoxSliding.smallConvLower M * c₀)) * ‖Submission.BoseGases.g0 v h z‖)
      volume :=
    hG0.norm.const_mul _
  refine hbound.mono' haesm ?_
  filter_upwards with z
  by_cases hz0 : Submission.BoseGases.g0 v h z = 0
  · rw [hz0]
    simp
  · have hzR : ‖z‖ < R :=
      lt_of_not_ge (fun hge => hz0 (Submission.BoseGases.g0_zero_of_norm_ge hv_supp hge h))
    have hz1 : ‖z‖ ≤ ℓ * d / 16 := le_trans hzR.le hR1
    have hz2 : ‖z‖ ≤ ℓ / 16 := le_trans hzR.le hR2
    have hs1 : ‖(ℓ * d)⁻¹ • z‖ ≤ 1 / 16 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
      calc (ℓ * d)⁻¹ * ‖z‖ ≤ (ℓ * d)⁻¹ * (ℓ * d / 16) :=
            mul_le_mul_of_nonneg_left hz1 (inv_pos.mpr hL).le
        _ = 1 / 16 := by field_simp
    have hκlow : Work.SmallBoxSliding.smallConvLower M
        ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) z := by
      have hcoord : ∀ j : Fin 3, |((ℓ * d)⁻¹ • z).ofLp j| ≤ 1 / 16 := fun j =>
        le_trans (Submission.BoseGases.coord_abs_le_norm _ j) hs1
      simpa [Submission.BoseGases.convScaleSmall] using
        Work.SmallBoxSliding.conv3Small_coord_lower hM ((ℓ * d)⁻¹ • z) hcoord
    have hs2 : ‖z‖ ≤ ℓ / 8 := by linarith
    have hcvlow : c₀ ≤ Submission.BoseGases.convScale ℓ z := hc₀ ℓ hℓ z hs2
    have hK : 0 < Work.SmallBoxSliding.smallConvLower M * c₀ :=
      mul_pos (Work.SmallBoxSliding.smallConvLower_pos M) hc₀pos
    have hDlow : Work.SmallBoxSliding.smallConvLower M * c₀
        ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) z
          * Submission.BoseGases.convScale ℓ z :=
      mul_le_mul hκlow hcvlow hc₀pos.le
        (le_trans (Work.SmallBoxSliding.smallConvLower_pos M).le hκlow)
    have hDnn : 0 ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) z
        * Submission.BoseGases.convScale ℓ z := le_trans hK.le hDlow
    have hden' : Work.SmallBoxSliding.smallConvLower M * c₀
        ≤ ‖Submission.BoseGases.convScaleSmall M (ℓ * d) z
            * Submission.BoseGases.convScale ℓ z‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hDnn]; exact hDlow
    have hquot' : ‖Submission.BoseGases.g0 v h z
          / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
              * Submission.BoseGases.convScale ℓ z)‖
        ≤ ‖Submission.BoseGases.g0 v h z‖ / (Work.SmallBoxSliding.smallConvLower M * c₀) := by
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) hK hden'
    have hAle := autocorr_le_chiMass_u hM hℓ hd u z
    have hAnn := autocorr_nonneg_u (M := M) ℓ d u z
    have hAd : ‖Work.BoseFixB1.autocorr (M := M) ℓ d u z‖
        ≤ Work.SmallBoxSliding.chiMass M ℓ d u := by
      rw [Real.norm_eq_abs, abs_of_nonneg hAnn]; exact hAle
    calc ‖(Submission.BoseGases.g0 v h z
            / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
                * Submission.BoseGases.convScale ℓ z))
          * Work.BoseFixB1.autocorr (M := M) ℓ d u z‖
        = ‖Submission.BoseGases.g0 v h z
            / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
                * Submission.BoseGases.convScale ℓ z)‖
          * ‖Work.BoseFixB1.autocorr (M := M) ℓ d u z‖ := norm_mul _ _
      _ ≤ (‖Submission.BoseGases.g0 v h z‖
            / (Work.SmallBoxSliding.smallConvLower M * c₀))
          * Work.SmallBoxSliding.chiMass M ℓ d u :=
          mul_le_mul hquot' hAd (norm_nonneg _) (div_nonneg (norm_nonneg _) hK.le)
      _ = (Work.SmallBoxSliding.chiMass M ℓ d u
            / (Work.SmallBoxSliding.smallConvLower M * c₀))
          * ‖Submission.BoseGases.g0 v h z‖ := by ring

end Work.BoseFixB1B

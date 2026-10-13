/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/ClassCHon/SliceMassUpgrade` — the every-`z` slice honesty from the *outer* bounds one
`D_z`-order up

The elliptic node `EllNode7` demands the **every-`z`** honesty `Work.Spaces.HkMem α k (slot)`
of the second-order slots of the solution.  This module supplies the missing transfer in the
direction that the workspace's a.e./integrated estimates actually provide:

  > `HkMem α 0 f`  ⟸  the *outer* `∫⁻`-bounds of `HkIntegrand α 0 f`
  >                    and of `HkIntegrand α 0 (z ∂_z f)`  (plus measurability and smoothness).

The point is that the `∫⁻`-form of the weighted mass of a slice is controlled *upward* in `z`
by the mass at a nearby `z₁` plus the *locally integrable* `D_z`-sector density, so a
single-`z` blow-up of the slice mass is impossible as soon as the `D_z`-density is finite
a.e. :

  `M(z₂) ≤ 2 M(z₁) + ofReal (2 (z₂ - z₁) / z₁²) · ∫⁻_z ∫⁻_θ ofReal (σ θ (z ∂_z f)²)`   (`sliceMass_lintegral_up`),

where `M(z) = ∫⁻_θ ofReal (σ θ f(z,θ)²)` and `σ = sin(2θ)^{-η}`.  Taking `z₁` in a full-measure
set of finiteness (which the outer bound `∫⁻_z M(z) < ⊤` supplies) upgrades a.e. finiteness to
**everywhere** finiteness (`sliceMass_ae_finite_upgrade`).

The proof of the up-estimate is the fundamental theorem of calculus on the slice
(`F z₂ θ = F z₁ θ + ∫_{z₁}^{z₂} ∂_zF s θ ds`), AM–GM and Cauchy–Schwarz in the `s`-variable
(`ofReal_sliceMass_pointwise`), monotonicity and Tonelli (`∫⁻`), and the elementary comparison
`(z₁²)⁻¹ ∫⁻_θ ofReal (σ θ (∂_z f)²) ≤ ∫⁻_θ ofReal (σ θ (z ∂_z f)²) / z²` on `z ≥ z₁`
(`sliceMass_dz_comparison`).

## Relation to the node

This is the missing link between the workspace's *integrated* (`∫⁻`) elliptic estimates and
the node's *everywhere*-`z` honesty; the machine-checked counterexample
(`ClassC/HonestCut/NOTES_family_profile_honest_COUNTEREXAMPLE.md`) that killed the
class-based route fails exactly the slice conjunct at a single `z₀`, and it does so *without*
the `D_z`-density one order up, which is why it is not a counterexample to these statements.

The main consumer interface is `HkMem_zero_of_outer`: `HkMem α 0 F` from the outer bounds of
`HkIntegrand α 0 F` and `HkIntegrand α 0 (D_z F)`, together with the a.e. measurabilities.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.ofReal_intervalIntegral_eq_lintegral
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade.ofReal_sliceMass_pointwise
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade.sliceMass_dz_comparison
import Submission.Work.FTS.ClassCHon.SliceMassUpgrade.sliceMass_ae_finite_upgrade
import Submission.Work.FTS.ClassC.HonestCut.HkMemAe_of_lintegral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology ENNReal

namespace Work.FTS.ClassCHon.SliceMassUpgrade

/-- **The up-estimate**: the `∫⁻`-mass of the `σ`-weighted slice at a larger `z₂` is bounded by
twice the mass at `z₁` plus the `∂_z`-sector term (whose global integral is the `D_z`-density).
No finiteness of the slice masses is assumed: the fundamental theorem of calculus on the slice,
AM–GM and Cauchy–Schwarz give the bound in the `⊤`-safe world of `ℝ≥0∞`. -/
theorem sliceMass_lintegral_up {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hmeas : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta p.2 * (Work.Spaces.pz F p.1 p.2) ^ 2))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))))
    {z₁ z₂ : ℝ} (hz₁ : 0 < z₁) (hz₁₂ : z₁ ≤ z₂) :
    (∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (F z₂ θ) ^ 2))
      ≤ 2 * (∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (F z₁ θ) ^ 2))
        + ENNReal.ofReal (2 * (z₂ - z₁) / z₁ ^ 2)
          * (∫⁻ s in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
              ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (s * Work.Spaces.pz F s θ) ^ 2)) := by
  have hσnn : ∀ θ ∈ Set.Ioo 0 (π / 2), 0 ≤ Work.FTS.EllipticEst.sEta θ := by
    intro θ hθ
    rw [Work.FTS.EllipticEst.sEta]
    exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _
  have hz1ne : ENNReal.ofReal (z₁ ^ 2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero]; linarith [sq_pos_of_pos hz₁]
  have hσcont : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
      (Set.Ioo 0 (π / 2)) := by
    rw [show Work.FTS.EllipticEst.sEta
        = fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) from rfl]
    refine ContinuousOn.rpow_const ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · intro x hx
      left
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1])
        (by linarith [hx.2, Real.pi_pos]))
  have haesm1 : AEMeasurable (fun θ : ℝ => ENNReal.ofReal 2 *
      ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (F z₁ θ) ^ 2))
      (volume.restrict (Set.Ioo 0 (π / 2))) := by
    have hc : ContinuousOn (fun θ : ℝ =>
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (F z₁ θ) ^ 2)) (Set.Ioo 0 (π / 2)) :=
      ENNReal.continuous_ofReal.comp_continuousOn
        (hσcont.mul ((hF.curry_θ hz₁).continuousOn.pow 2))
    exact (hc.aemeasurable measurableSet_Ioo).const_mul _
  have hAEM : AEMeasurable (Function.uncurry (fun s θ : ℝ =>
      ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (Work.Spaces.pz F s θ) ^ 2)))
      ((volume.restrict (Set.Ioo z₁ z₂)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) := by
    have hle : (volume.restrict (Set.Ioo z₁ z₂)).prod (volume.restrict (Set.Ioo 0 (π / 2)))
        ≤ (volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2))) := by
      rw [Measure.prod_restrict, Measure.prod_restrict]
      refine Measure.restrict_mono ?_ le_rfl
      exact Set.prod_mono (fun x hx => lt_of_lt_of_le hz₁ (le_of_lt hx.1)) (subset_refl _)
    exact AEMeasurable.mono_measure hmeas hle
  -- (1) pointwise bound under the lintegral
  have hstep1 : (∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (F z₂ θ) ^ 2))
      ≤ ∫⁻ θ in Set.Ioo 0 (π / 2),
          (ENNReal.ofReal 2 * ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (F z₁ θ) ^ 2)
            + ENNReal.ofReal 2 * (ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ)
              * (ENNReal.ofReal (z₂ - z₁)
                * ∫⁻ s in Set.Ioo z₁ z₂,
                    ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)))) := by
    refine lintegral_mono_ae ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall fun θ hθ => by
      simpa only [mul_assoc] using ofReal_sliceMass_pointwise hF hz₁ hz₁₂ hθ
  -- (2) split and pull out the constants of both summands
  have hsplit : (∫⁻ θ in Set.Ioo 0 (π / 2),
          (ENNReal.ofReal 2 * ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (F z₁ θ) ^ 2)
            + ENNReal.ofReal 2 * (ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ)
              * (ENNReal.ofReal (z₂ - z₁)
                * ∫⁻ s in Set.Ioo z₁ z₂,
                    ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)))))
      = ENNReal.ofReal 2 * (∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (F z₁ θ) ^ 2))
        + (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal 2
            * (ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ)
              * (ENNReal.ofReal (z₂ - z₁)
                * ∫⁻ s in Set.Ioo z₁ z₂,
                    ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)))) := by
    rw [lintegral_add_left' haesm1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  -- (3) the second summand: normalise, pull the constants, pull `ofReal ∘ σ` inside
  have hsecond : (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal 2
        * (ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ)
          * (ENNReal.ofReal (z₂ - z₁)
            * ∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))))
      = ENNReal.ofReal 2 * (ENNReal.ofReal (z₂ - z₁)
          * (∫⁻ θ in Set.Ioo 0 (π / 2), ∫⁻ s in Set.Ioo z₁ z₂,
              ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ
                * (Work.Spaces.pz F s θ) ^ 2))) := by
    rw [show (fun θ : ℝ => ENNReal.ofReal 2
          * (ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ)
            * (ENNReal.ofReal (z₂ - z₁)
              * ∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))))
        = fun θ : ℝ => ENNReal.ofReal 2 * (ENNReal.ofReal (z₂ - z₁)
            * (ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ)
              * (∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))))
        from by funext θ; ring]
    have hinner : (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ)
          * (∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2)))
        = (∫⁻ θ in Set.Ioo 0 (π / 2), ∫⁻ s in Set.Ioo z₁ z₂,
            ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ
              * (Work.Spaces.pz F s θ) ^ 2)) := by
      refine lintegral_congr_ae ?_
      show ∀ᵐ θ ∂(volume.restrict (Set.Ioo 0 (π / 2))),
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ)
            * (∫⁻ s in Set.Ioo z₁ z₂, ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))
          = ∫⁻ s in Set.Ioo z₁ z₂,
              ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (Work.Spaces.pz F s θ) ^ 2)
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun θ hθ => ?_
      rw [(lintegral_const_mul' (ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ))
        (fun s : ℝ => ENNReal.ofReal ((Work.Spaces.pz F s θ) ^ 2))
        ENNReal.ofReal_ne_top).symm]
      exact lintegral_congr_ae (Filter.Eventually.of_forall fun s =>
        (ENNReal.ofReal_mul (hσnn θ hθ)).symm)
    rw [lintegral_const_mul' (ENNReal.ofReal 2) _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' (ENNReal.ofReal (z₂ - z₁)) _ ENNReal.ofReal_ne_top, hinner]
  -- (4) Tonelli
  have hthird : (∫⁻ s in Set.Ioo z₁ z₂, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (Work.Spaces.pz F s θ) ^ 2))
      = (∫⁻ θ in Set.Ioo 0 (π / 2), ∫⁻ s in Set.Ioo z₁ z₂,
          ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (Work.Spaces.pz F s θ) ^ 2)) :=
    lintegral_lintegral_swap (μ := volume.restrict (Set.Ioo z₁ z₂))
      (ν := volume.restrict (Set.Ioo 0 (π / 2))) hAEM
  -- (5) bound by the `D_z`-mass
  have hbound : (∫⁻ s in Set.Ioo z₁ z₂, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (Work.Spaces.pz F s θ) ^ 2))
      ≤ (ENNReal.ofReal (z₁ ^ 2))⁻¹
        * (∫⁻ s in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
            ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ
              * (s * Work.Spaces.pz F s θ) ^ 2)) := by
    have h1 : (∫⁻ s in Set.Ioo z₁ z₂, ∫⁻ θ in Set.Ioo 0 (π / 2),
          ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (Work.Spaces.pz F s θ) ^ 2))
        ≤ ∫⁻ s in Set.Ioo z₁ z₂, (ENNReal.ofReal (z₁ ^ 2))⁻¹
            * (∫⁻ θ in Set.Ioo 0 (π / 2), ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ
                * (s * Work.Spaces.pz F s θ) ^ 2)) := by
      refine lintegral_mono_ae ?_
      rw [ae_restrict_iff' measurableSet_Ioo]
      exact Filter.Eventually.of_forall fun s hs => sliceMass_dz_comparison hz₁ (le_of_lt hs.1)
    refine le_trans h1 ?_
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hz1ne)]
    exact mul_le_mul_right (lintegral_mono_set (fun x hx => lt_of_lt_of_le hz₁ (le_of_lt hx.1))) _
  have hconv : (2 : ℝ≥0∞) * (ENNReal.ofReal (z₂ - z₁)
        * ((ENNReal.ofReal (z₁ ^ 2))⁻¹
          * (∫⁻ s in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
              ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ
                * (s * Work.Spaces.pz F s θ) ^ 2))))
      = ENNReal.ofReal (2 * (z₂ - z₁) / z₁ ^ 2)
        * (∫⁻ s in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
            ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ
              * (s * Work.Spaces.pz F s θ) ^ 2)) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity : (0:ℝ) < z₁ ^ 2),
      ENNReal.div_eq_inv_mul, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      show ENNReal.ofReal (2:ℝ) = (2 : ℝ≥0∞) from by norm_num]
    ring
  refine le_trans hstep1 ?_
  rw [hsplit, hsecond, ← hthird]
  rw [show ENNReal.ofReal (2:ℝ) = (2 : ℝ≥0∞) from by norm_num]
  refine add_le_add le_rfl ?_
  calc (2 : ℝ≥0∞) * (ENNReal.ofReal (z₂ - z₁)
        * (∫⁻ s in Set.Ioo z₁ z₂, ∫⁻ θ in Set.Ioo 0 (π / 2),
            ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ
              * (Work.Spaces.pz F s θ) ^ 2)))
      ≤ (2 : ℝ≥0∞) * (ENNReal.ofReal (z₂ - z₁)
          * ((ENNReal.ofReal (z₁ ^ 2))⁻¹
            * (∫⁻ s in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
                ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ
                  * (s * Work.Spaces.pz F s θ) ^ 2)))) :=
        mul_le_mul_right (mul_le_mul_right hbound (ENNReal.ofReal (z₂ - z₁))) (2 : ℝ≥0∞)
    _ = ENNReal.ofReal (2 * (z₂ - z₁) / z₁ ^ 2)
          * (∫⁻ s in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
              ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ
                * (s * Work.Spaces.pz F s θ) ^ 2)) := hconv



/-! ## The every-`z` finiteness -/

/-- A point of the interval `(a,b)` on which an a.e. finite function is finite (any non-degenerate
interval has positive measure). -/
lemma exists_lt_top_of_ae_lt_top {M : ℝ → ENNReal} {a b : ℝ} (hab : a < b)
    (h : ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)), M t < ⊤) :
    ∃ t ∈ Set.Ioo a b, M t < ⊤ := by
  by_contra hcon
  push_neg at hcon
  have hsub : Set.Ioo a b ⊆ {t : ℝ | ¬ M t < ⊤} := fun t ht => not_lt.mpr (hcon t ht)
  have h0 : (volume.restrict (Set.Ioo a b)) {t : ℝ | ¬ M t < ⊤} = 0 := MeasureTheory.ae_iff.mp h
  have hle : (volume.restrict (Set.Ioo a b)) (Set.Ioo a b)
      ≤ (volume.restrict (Set.Ioo a b)) {t : ℝ | ¬ M t < ⊤} := MeasureTheory.measure_mono hsub
  rw [h0] at hle
  have hvol : (volume.restrict (Set.Ioo a b)) (Set.Ioo a b) = ENNReal.ofReal (b - a) := by
    rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_self, Real.volume_Ioo]
  rw [hvol] at hle
  exact absurd hle (not_le.mpr (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)))

/-- **Everywhere finiteness of the `σ`-weighted slice mass from the two outer bounds.** -/
theorem sliceMass_lintegral_lt_top_of_outer {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hmeas : AEMeasurable (fun p : ℝ × ℝ =>
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta p.2 * (Work.Spaces.pz F p.1 p.2) ^ 2))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioo 0 (π / 2)))))
    (hmeasmine : AEMeasurable (fun z => ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (F z θ) ^ 2))
      (volume.restrict (Set.Ioi 0)))
    (houter0 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (F z θ) ^ 2)) < ⊤)
    (houter1 : (∫⁻ z in Set.Ioi 0, ∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz F z θ) ^ 2)) < ⊤) :
    ∀ z ∈ Set.Ioi 0,
      (∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (F z θ) ^ 2)) < ⊤ := by
  intro z hz
  -- a.e. finiteness on `(z/2, z)`
  have haefin : ∀ᵐ t ∂(volume.restrict (Set.Ioi 0)),
      (∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (F t θ) ^ 2)) < ⊤ :=
    MeasureTheory.ae_lt_top' hmeasmine (ne_of_lt houter0)
  have hzpos : 0 < z := Set.mem_Ioi.mp hz
  have hpos : 0 < z / 2 := by linarith
  have hlt : z / 2 < z := by linarith
  have hae0 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioi (0 : ℝ) →
      (∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (F t θ) ^ 2)) < ⊤ :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mp haefin
  have hae_sub : ∀ᵐ t ∂(volume.restrict (Set.Ioo (z / 2) z)),
      (∫⁻ θ in Set.Ioo 0 (π / 2),
        ENNReal.ofReal (Work.FTS.EllipticEst.sEta θ * (F t θ) ^ 2)) < ⊤ := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hae0] with t ht htm
    exact ht (lt_of_lt_of_le hpos (le_of_lt htm.1))
  obtain ⟨z₁, hz₁mem, hz₁fin⟩ := exists_lt_top_of_ae_lt_top hlt hae_sub
  have hz₁pos : 0 < z₁ := by linarith [hz₁mem.1]
  have hz₁le : z₁ ≤ z := le_of_lt hz₁mem.2
  refine lt_of_le_of_lt (sliceMass_lintegral_up hF hmeas hz₁pos hz₁le) ?_
  refine ENNReal.add_lt_top.mpr ⟨?_, ?_⟩
  · exact ENNReal.mul_lt_top (by norm_num) hz₁fin
  · refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top houter1

end Work.FTS.ClassCHon.SliceMassUpgrade

import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.SmallBoxSliding.abs_wSmall1Pair_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Real

namespace Work.BoseFixB1

open MeasureTheory
open Submission.BoseGases

/-- **Uniform fibre bound of the localised one-body kernel over the big box.**

Integrating the pointwise domination `Work.SmallBoxSliding.abs_wSmall1Pair_le` in the `y`-variable
over `acube ℓ`, bounding the `z`-dependent cutoff factor `χ_M((ℓd)⁻¹•z − u)` by its global
absolute bound `chiSmallDecay M` (`chiSmall_decay_coord_le_decay`), and using the `g₀`-mass
`∫|g₀| = 8π·(a v)` (`g0_abs_integral`) together with
`∫_{acube ℓ} |g₀(z−y)| dy ≤ ∫|g₀|` (translation invariance and `acube ℓ ⊆ univ`), yields the
stated bound, uniformly in the configuration point `z` and in `u ∈ G`:
`|∫_{acube ℓ} w_{1,B(u)}(z,y) dy| ≤ (χ·D_M)·(2(χ·D_M)/smallConvLower M·8π a v)`. -/
theorem wSmall1Pair_fibre_abs_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ,
      _root_.BoseGases.IsRadial w ∧ _root_.BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3)) :
    ∀ z : EuclideanSpace ℝ (Fin 3),
      |∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g0 v h) z y| ≤
        (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * ((2 * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
              / Work.SmallBoxSliding.smallConvLower M) * (8 * π * _root_.BoseGases.a v)) := by
  intro z
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hD0 : 0 ≤ chiSupAbs * chiSmallDecay M :=
    mul_nonneg chiSupAbs_nonneg (chiSmallDecay_nonneg M)
  have hK0 : 0 ≤ 2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M :=
    div_nonneg (mul_nonneg (by norm_num) hD0) (le_of_lt hSpos)
  have hchi : chiSmall M ((ℓ * d)⁻¹ • z - u) ≤ chiSmallDecay M :=
    le_trans (le_abs_self _) (chiSmall_decay_coord_le_decay hM _)
  have hA : chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • z - u) ≤ chiSupAbs * chiSmallDecay M :=
    mul_le_mul_of_nonneg_left hchi chiSupAbs_nonneg
  -- pointwise domination, with the `z`-dependent cutoff factor replaced by its sup
  have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
      |wSmallPair M ℓ d u (g0 v h) z y| ≤
        (chiSupAbs * chiSmallDecay M)
          * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * |g0 v h (z - y)|) := by
    intro y
    have h1 : |wSmallPair M ℓ d u (g0 v h) z y| ≤
        chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • z - u)
          * (2 * (chiSupAbs * chiSmallDecay M) * |g0 v h (z - y)|)
          / Work.SmallBoxSliding.smallConvLower M := by
      have h0 := Work.SmallBoxSliding.abs_wSmall1Pair_le (M := M) (ℓ := ℓ) (d := d)
        hv_supp hR0 h hM hℓ hd hR hRχ u z y
      simpa only [wSmall1Pair] using h0
    have h2 : chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • z - u)
          * (2 * (chiSupAbs * chiSmallDecay M) * |g0 v h (z - y)|)
          / Work.SmallBoxSliding.smallConvLower M ≤
        (chiSupAbs * chiSmallDecay M)
          * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * |g0 v h (z - y)|) := by
      rw [show chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • z - u)
            * (2 * (chiSupAbs * chiSmallDecay M) * |g0 v h (z - y)|)
            / Work.SmallBoxSliding.smallConvLower M
          = (chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • z - u))
            * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
              * |g0 v h (z - y)|) by ring]
      exact mul_le_mul_of_nonneg_right hA
        (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hD0) (le_of_lt hSpos)) (abs_nonneg _))
    exact le_trans h1 h2
  -- integrability of the dominating function
  have hg0int : Integrable (fun y : EuclideanSpace ℝ (Fin 3) => |g0 v h (z - y)|) := by
    simpa only [Real.norm_eq_abs] using (g0_integrable hR0 hv_supp h).abs.comp_sub_left z
  have hGint_vol : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      (chiSupAbs * chiSmallDecay M)
        * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
          * |g0 v h (z - y)|)) :=
    (hg0int.const_mul
        (2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)).const_mul
      (chiSupAbs * chiSmallDecay M)
  have hGint : Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      (chiSupAbs * chiSmallDecay M)
        * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
          * |g0 v h (z - y)|))
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)) :=
    hGint_vol.mono_measure Measure.restrict_le_self
  have hstep1 : |∫ y in acube ℓ, wSmallPair M ℓ d u (g0 v h) z y| ≤
      ∫ y, ‖wSmallPair M ℓ d u (g0 v h) z y‖
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)) := by
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ))
        (fun y : EuclideanSpace ℝ (Fin 3) => wSmallPair M ℓ d u (g0 v h) z y)
  have hstep2 : (∫ y, ‖wSmallPair M ℓ d u (g0 v h) z y‖
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ))) ≤
      ∫ y, (chiSupAbs * chiSmallDecay M)
          * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * |g0 v h (z - y)|)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)) := by
    refine integral_mono_of_nonneg (ae_of_all _ (fun y => norm_nonneg _)) hGint
      (ae_of_all _ (fun y => ?_))
    simpa only [Real.norm_eq_abs] using hpt y
  have hval : (∫ y, (chiSupAbs * chiSmallDecay M)
          * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * |g0 v h (z - y)|)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)))
      = (chiSupAbs * chiSmallDecay M)
          * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * (∫ y in acube ℓ, |g0 v h (z - y)|)) := by
    rw [integral_const_mul, integral_const_mul]
  have hY : (∫ y in acube ℓ, |g0 v h (z - y)|) ≤ 8 * π * _root_.BoseGases.a v := by
    calc (∫ y in acube ℓ, |g0 v h (z - y)|)
        ≤ ∫ y : EuclideanSpace ℝ (Fin 3), |g0 v h (z - y)| :=
          setIntegral_le_integral hg0int (ae_of_all _ (fun y => abs_nonneg _))
      _ = ∫ w : EuclideanSpace ℝ (Fin 3), |g0 v h w| :=
          integral_sub_left_eq_self (fun w : EuclideanSpace ℝ (Fin 3) => |g0 v h w|) volume z
      _ = 8 * π * _root_.BoseGases.a v := g0_abs_integral hR0 hv hvrad hv_supp h
  calc |∫ y in acube ℓ, wSmallPair M ℓ d u (g0 v h) z y|
      ≤ ∫ y, ‖wSmallPair M ℓ d u (g0 v h) z y‖
          ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)) := hstep1
    _ ≤ ∫ y, (chiSupAbs * chiSmallDecay M)
          * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * |g0 v h (z - y)|)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict (acube ℓ)) := hstep2
    _ = (chiSupAbs * chiSmallDecay M)
          * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * (∫ y in acube ℓ, |g0 v h (z - y)|)) := hval
    _ ≤ (chiSupAbs * chiSmallDecay M)
          * ((2 * (chiSupAbs * chiSmallDecay M) / Work.SmallBoxSliding.smallConvLower M)
            * (8 * π * _root_.BoseGases.a v)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hY hK0) hD0

end Work.BoseFixB1

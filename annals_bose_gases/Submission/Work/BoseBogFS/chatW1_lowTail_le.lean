import ChallengeDeps
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.BoseB7AK.W1rows.W1hat_abs_le
import Submission.Work.BoseFixB1S.slidingNewtonMassSharpB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.chatW1_lowTail_le`

The low-momentum part of the FS `‖p‖^{-3}` tail of `Ŵ₁ = chat (W1fun v h ℓ)`:

    ∫_{P₀ < ‖p‖ ≤ (a v)^{-1}} Ŵ₁(p)²/‖p‖³ dp ≤ (16π·a v)²·4π·(1 + log(1/(P₀·a v)))

with the **exact** constant `(16π·a v)²` matching the uniform per-mode bound
`|Ŵ₁(k)| ≤ 16π·a v` (`Work.BoseB7AK.W1rows.W1hat_abs_le`, FS `eq:WSestimate`).

## Route

1. **Uniform bound.**  `|Ŵ₁(p)| ≤ 16π·a v` for every `p` (`W1hat_abs_le`), hence
   `Ŵ₁(p)² ≤ (16π·a v)²` pointwise, *without any low-momentum restriction*.
2. **The `‖p‖^{-3}` integral over the annulus.**  The exact polar-coordinates value
   `∫_{a < ‖q‖ ≤ b} ‖q‖^{-3} dq = 4π(log b − log a)` (`regionAnnulusInv3_Ioc`, the
   `Ioc`-variant of the proved `Work.BoseFixB1S.regionAnnulusInv3`).
3. **Assembly.**  With `A = a v` and `b = A^{-1}` the set integral is bounded by
   `(16πA)²·4π(log A^{-1} − log P₀) = (16πA)²·4π·log(1/(P₀A))`, and
   `log(1/(P₀A)) ≥ 0` because `P₀A ≤ 1`.

The two elementary ingredients missing from the corpus are supplied above the target:
the `Ioc`-variant of the annulus integral, and (inline) the integrability of
`‖p‖^{-3}` on the annulus, which follows from `IntegrableOn.of_bound` with the
pointwise bound `(‖p‖³)⁻¹ ≤ (P₀³)⁻¹` on `{P₀ < ‖p‖}` and the finiteness of the
measure of the enclosing closed ball.
-/

namespace Work.BoseBogFS

open MeasureTheory
open scoped Real

/-- **The `‖q‖^{-3}` integral over the half-open annulus `{a < ‖q‖ ≤ b}` in `ℝ³`.**

The `Ioc`-variant of the proved `Work.BoseFixB1S.regionAnnulusInv3` (which handles
`{a ≤ ‖q‖ ≤ b}`), obtained by the same polar-coordinates computation
(`Submission.BoseGases.integral_fun_norm_r3`): the volume element is `r² dr dΩ`,
the solid angle is `4π`, and `∫_a^b r²·r^{-3} dr = log b − log a`. -/
theorem regionAnnulusInv3_Ioc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ q in {q : EuclideanSpace ℝ (Fin 3) | a < ‖q‖ ∧ ‖q‖ ≤ b}, ((‖q‖ : ℝ) ^ 3)⁻¹
      = 4 * Real.pi * (Real.log b - Real.log a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  set S : Set (EuclideanSpace ℝ (Fin 3)) := {q | a < ‖q‖ ∧ ‖q‖ ≤ b} with hS
  have hSmeas : MeasurableSet S := by
    have h : S = (fun q : EuclideanSpace ℝ (Fin 3) => ‖q‖) ⁻¹' Set.Ioc a b := by
      ext q; simp only [hS, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioc]
    rw [h]; exact measurableSet_Ioc.preimage continuous_norm.measurable
  set g : ℝ → ℝ := (Set.Ioc a b).indicator (fun r : ℝ => (r ^ 3)⁻¹) with hg
  have hpoint : ∀ q : EuclideanSpace ℝ (Fin 3),
      S.indicator (fun q => ((‖q‖ : ℝ) ^ 3)⁻¹) q = g ‖q‖ := by
    intro q
    by_cases hq : q ∈ S
    · have hqn : ‖q‖ ∈ Set.Ioc a b := by rw [hS] at hq; exact hq
      rw [Set.indicator_of_mem hq, hg, Set.indicator_of_mem hqn]
    · have hqn : ‖q‖ ∉ Set.Ioc a b := by
        intro hc; exact hq (by rw [hS]; exact hc)
      rw [Set.indicator_of_notMem hq, hg, Set.indicator_of_notMem hqn]
  rw [← integral_indicator hSmeas]
  rw [show (∫ (x : EuclideanSpace ℝ (Fin 3)),
        S.indicator (fun q => ((‖q‖ : ℝ) ^ 3)⁻¹) x)
      = ∫ (x : EuclideanSpace ℝ (Fin 3)), g ‖x‖ from
      integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [Submission.BoseGases.integral_fun_norm_r3 (g := g)]
  congr 1
  have hg' : ∀ r : ℝ, r ^ 2 * g r = (Set.Ioc a b).indicator (fun r => r⁻¹) r := by
    intro r
    by_cases h : r ∈ Set.Ioc a b
    · rw [hg, Set.indicator_of_mem h, Set.indicator_of_mem h]
      have hr : r ≠ 0 := by have := h.1; linarith
      field_simp
    · rw [hg, Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  rw [show (∫ r in Set.Ioi (0 : ℝ), r ^ 2 * g r)
      = ∫ r in Set.Ioi (0 : ℝ), (Set.Ioc a b).indicator (fun r => r⁻¹) r from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun r _ => hg' r)]
  rw [MeasureTheory.setIntegral_indicator (μ := volume) (s := Set.Ioi (0 : ℝ))
      (t := Set.Ioc a b) measurableSet_Ioc]
  rw [show (Set.Ioi (0 : ℝ)) ∩ Set.Ioc a b = Set.Ioc a b from by
      ext r; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
      exact ⟨fun h => h.2, fun h => ⟨lt_trans ha h.1, h⟩⟩]
  rw [← intervalIntegral.integral_of_le hab]
  rw [integral_inv (by rw [Set.uIcc_of_le hab]; exact fun h => absurd h.1 (not_le.mpr ha)),
    Real.log_div hb.ne' ha.ne']

theorem chatW1_lowTail_le :
    ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R ℓ P₀ : ℝ},
      0 < R → 0 < ℓ → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R →
      R ≤ ℓ * Submission.BoseGases.chiR0 → 0 < P₀ → 0 < _root_.BoseGases.a v →
      P₀ * _root_.BoseGases.a v ≤ 1 →
      (∫ p in {p : EuclideanSpace ℝ (Fin 3) | P₀ < ‖p‖ ∧ ‖p‖ ≤ (_root_.BoseGases.a v)⁻¹},
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / ‖p‖ ^ 3)
        ≤ (16 * Real.pi * _root_.BoseGases.a v) ^ 2
            * (4 * Real.pi * (1 + Real.log (1 / (P₀ * _root_.BoseGases.a v)))) := by
  intro v h R ℓ P₀ hR hℓ hv hvrad hv_supp hRℓ hP₀ hav hPa
  set A : ℝ := _root_.BoseGases.a v with hA
  have hApos : 0 < A := hav
  have hP0b : P₀ ≤ A⁻¹ := by
    have h := (le_div_iff₀ hApos).mpr hPa
    simpa [one_div] using h
  set s : Set (EuclideanSpace ℝ (Fin 3)) := {p | P₀ < ‖p‖ ∧ ‖p‖ ≤ A⁻¹} with hs
  -- (1) the uniform pointwise bound `|Ŵ₁| ≤ 16πA`
  have hsup : ∀ p : EuclideanSpace ℝ (Fin 3),
      (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 ≤ (16 * Real.pi * A) ^ 2 := by
    intro p
    have hle := Work.BoseB7AK.W1rows.W1hat_abs_le hR hℓ hv hvrad hv_supp h hRℓ p
    rw [← hA] at hle
    have h2 : |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p| ^ 2
        ≤ (16 * Real.pi * A) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hle 2
    rwa [sq_abs] at h2
  have hs_meas : MeasurableSet s := by
    have h : s = (fun q : EuclideanSpace ℝ (Fin 3) => ‖q‖) ⁻¹' Set.Ioc P₀ A⁻¹ := by
      ext q; simp only [hs, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ioc]
    rw [h]; exact measurableSet_Ioc.preimage continuous_norm.measurable
  -- the majorant `g` and its integrability on `s`
  have hfg : ∀ p ∈ s, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / ‖p‖ ^ 3
      ≤ (16 * Real.pi * A) ^ 2 * ((‖p‖ ^ 3)⁻¹) := by
    intro p _
    have h1 : (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / ‖p‖ ^ 3
        ≤ (16 * Real.pi * A) ^ 2 / ‖p‖ ^ 3 :=
      div_le_div_of_nonneg_right (hsup p) (by positivity)
    rwa [div_eq_mul_inv] at h1
  have hgint : IntegrableOn
      (fun p : EuclideanSpace ℝ (Fin 3) => (16 * Real.pi * A) ^ 2 * ((‖p‖ ^ 3)⁻¹)) s := by
    have hsub : s ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) A⁻¹ := by
      intro p hp
      rw [hs] at hp
      rw [Metric.mem_closedBall, dist_eq_norm]
      simpa using hp.2
    have hfin : volume s < ⊤ :=
      lt_of_le_of_lt (measure_mono hsub) (isCompact_closedBall _ _).measure_lt_top
    have hcont : ContinuousOn
        (fun p : EuclideanSpace ℝ (Fin 3) => (16 * Real.pi * A) ^ 2 * ((‖p‖ ^ 3)⁻¹)) s := by
      have h1 : ContinuousOn (fun p : EuclideanSpace ℝ (Fin 3) => ((‖p‖ : ℝ) ^ 3)⁻¹) s := by
        refine ContinuousOn.inv₀ ((continuous_norm.pow 3).continuousOn) ?_
        intro p hp
        rw [hs] at hp
        have hp0 : 0 < ‖p‖ := lt_trans hP₀ hp.1
        positivity
      exact continuousOn_const.mul h1
    refine IntegrableOn.of_bound hfin (hcont.aestronglyMeasurable hs_meas)
      ((16 * Real.pi * A) ^ 2 * ((P₀ ^ 3)⁻¹)) ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict hs_meas] with p hp
    rw [hs] at hp
    have hp0 : 0 < ‖p‖ := lt_trans hP₀ hp.1
    have h3 : P₀ ^ 3 ≤ ‖p‖ ^ 3 :=
      pow_le_pow_left₀ (le_of_lt hP₀) (le_of_lt hp.1) 3
    have hinv : (‖p‖ ^ 3)⁻¹ ≤ (P₀ ^ 3)⁻¹ :=
      (inv_le_inv₀ (pow_pos hp0 3) (pow_pos hP₀ 3)).mpr h3
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (16 * Real.pi * A) ^ 2),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (‖p‖ ^ 3)⁻¹)]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  -- the value of the majorant integral
  have hval : (∫ p in s, (16 * Real.pi * A) ^ 2 * ((‖p‖ ^ 3)⁻¹))
      = (16 * Real.pi * A) ^ 2 * (4 * Real.pi * (Real.log A⁻¹ - Real.log P₀)) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [hs]
    exact regionAnnulusInv3_Ioc hP₀ hP0b
  have hlogid : Real.log A⁻¹ - Real.log P₀ = Real.log (1 / (P₀ * A)) := by
    rw [← Real.log_div (inv_ne_zero hApos.ne') hP₀.ne']
    congr 1
    field_simp
  have hmain : (∫ p in s, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / ‖p‖ ^ 3)
      ≤ (16 * Real.pi * A) ^ 2 * (4 * Real.pi * (1 + Real.log (1 / (P₀ * A)))) := by
    calc (∫ p in s, (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / ‖p‖ ^ 3)
        ≤ ∫ p in s, (16 * Real.pi * A) ^ 2 * ((‖p‖ ^ 3)⁻¹) :=
          MeasureTheory.setIntegral_mono_of_nonneg (fun p _ => by positivity) hfg hgint
      _ = (16 * Real.pi * A) ^ 2 * (4 * Real.pi * (Real.log A⁻¹ - Real.log P₀)) := hval
      _ = (16 * Real.pi * A) ^ 2 * (4 * Real.pi * Real.log (1 / (P₀ * A))) := by
          rw [hlogid]
      _ ≤ (16 * Real.pi * A) ^ 2 * (4 * Real.pi * (1 + Real.log (1 / (P₀ * A)))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hL : 0 ≤ Real.log (1 / (P₀ * A)) :=
            Real.log_nonneg ((le_div_iff₀ (mul_pos hP₀ hApos)).mpr (by simpa using hPa))
          nlinarith [Real.pi_pos]
  simpa [hA, hs] using hmain

end Work.BoseBogFS

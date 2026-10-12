import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBogFS.chatW1_coulomb_le
import Submission.Work.BoseBogFS.chatW1_lowTail_le
import Submission.Work.BoseBogFS.setIntegral_inv_cube_le
import Submission.Work.BoseBogFS.setIntegral_split_le
import Submission.Work.BoseFixR.IntegrableChatW1sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.W1_tail_log_le` — the logarithmic `‖p‖^{-3}` tail of `Ŵ₁`

For a nonnegative radial potential `v` of range `R` in the dilute regime
`R ≤ ℓ·chiR0`, and any `P₀ > 0` with `P₀·(a v) ≤ 1`,

    ∫_{‖p‖ > P₀}  Ŵ₁(p)²/‖p‖³ dp  ≤  C·(a v)²·(1 + log (1/(P₀·(a v))))

with an absolute constant `C` (`W₁ = W1fun v h ℓ = wScaled ℓ (g₀)`, FS §4's
χ-renormalised one-body kernel).

## Route (split at the reciprocal scattering length `L := (a v)⁻¹`)

* **Pointwise** (`Work.BoseB7AK.W1rows.W1hat_abs_le`, FS `eq:WSestimate`):
  `|Ŵ₁(p)| ≤ 16π·(a v)` for *every* `p`, so `Ŵ₁(p)² ≤ (16π a v)²`.
* **Low band** `{P₀ < ‖p‖ ≤ (a v)⁻¹}`: the annulus computation
  `Work.BoseFixB1S.regionAnnulusInv3` gives
  `∫_{c ≤ ‖q‖ ≤ d}‖q‖⁻³ = 4π(log d − log c)`, so the band contributes
  `(16π a v)²·4π·(1 + log(1/(P₀ a v))) = 1024π³(a v)²(1 + log(1/(P₀ a v)))`
  (`chatW1_lowTail_le`).
* **High band** `{L < ‖p‖}`: there `1/‖p‖³ ≤ (a v)/‖p‖²`, so the band is at most
  `(a v)·∫Ŵ₁²/‖p‖² ≤ (a v)·512π⁴(a v) = 512π⁴(a v)²` (`setIntegral_inv_cube_le`
  plus the Coulomb bound `chatW1_coulomb_le`, which chains FS `eq:I2-integral`
  `Work.BoseFixR.mass_le_W1omega2` with `Work.BoseFixR.W1omegaMassLe`).
* `setIntegral_split_le` decomposes the outer set integral (junk-value safe, via
  `ℝ≥0∞` and `ENNReal.toReal_add_le`), and `π ≤ 4` plus `log ≥ 0` give the
  numerical conclusion with `C = 10⁶`.

The degenerate case `a v = 0` is separate: then `|Ŵ₁| ≤ 0`, so the integrand
vanishes identically.
-/

open MeasureTheory
open scoped Real

namespace Work.BoseBogFS

theorem W1_tail_log_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
        {R ℓ P₀ : ℝ},
      0 < R → 0 < ℓ → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v →
      tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R →
      R ≤ ℓ * Submission.BoseGases.chiR0 → 0 < P₀ →
      P₀ * (_root_.BoseGases.a v) ≤ 1 →
      (∫ p in {p : EuclideanSpace ℝ (Fin 3) | P₀ < ‖p‖},
          (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / ‖p‖ ^ 3)
        ≤ C * (_root_.BoseGases.a v) ^ 2
            * (1 + Real.log (1 / (P₀ * _root_.BoseGases.a v))) := by
  refine ⟨10 ^ 6, by norm_num, ?_⟩
  intro v h R ℓ P₀ hR hℓ hv hvrad hv_supp hRℓ hP₀ hP₀A
  -- `a v ≥ 0`: `8π·a v = ∫|g₀| ≥ 0`.
  have hAnn : 0 ≤ _root_.BoseGases.a v := by
    have h1 : 0 ≤ ∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h z| :=
      integral_nonneg (fun z => abs_nonneg _)
    have h2 : (∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h z|)
        = 8 * Real.pi * _root_.BoseGases.a v :=
      Submission.BoseGases.g0_abs_integral hR hv hvrad hv_supp h
    have h3 : 0 ≤ 8 * Real.pi * _root_.BoseGases.a v := by rw [← h2]; exact h1
    nlinarith [Real.pi_pos]
  by_cases hA0 : _root_.BoseGases.a v = 0
  · -- Degenerate case: `|Ŵ₁| ≤ 16π·0 = 0`, so the integrand vanishes identically.
    have hchat0 : ∀ p : EuclideanSpace ℝ (Fin 3),
        Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p = 0 := by
      intro p
      have h1 := Work.BoseB7AK.W1rows.W1hat_abs_le hR hℓ hv hvrad hv_supp h hRℓ p
      rw [hA0, mul_zero] at h1
      exact abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
    have hzero : (∫ p in {p : EuclideanSpace ℝ (Fin 3) | P₀ < ‖p‖},
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / ‖p‖ ^ 3) = 0 := by
      rw [show (∫ p in {p : EuclideanSpace ℝ (Fin 3) | P₀ < ‖p‖},
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / ‖p‖ ^ 3)
          = ∫ p in {p : EuclideanSpace ℝ (Fin 3) | P₀ < ‖p‖}, (0 : ℝ) from
        setIntegral_congr_fun (measurableSet_lt measurable_const measurable_norm)
          (fun p _ => by rw [hchat0 p]; simp)]
      simp
    rw [hzero, hA0]
    norm_num
  · -- Main case `a v > 0`.
    have hApos : 0 < _root_.BoseGases.a v := lt_of_le_of_ne hAnn (Ne.symm hA0)
    have hP₀L : P₀ ≤ (_root_.BoseGases.a v)⁻¹ := by
      rw [inv_eq_one_div]
      exact (le_div_iff₀ hApos).mpr hP₀A
    -- measurability of the integrand
    have hFmeas : AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin 3) =>
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / ‖p‖ ^ 3) volume := by
      have hW1 : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) :=
        Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
      have hc : Continuous (fun p : EuclideanSpace ℝ (Fin 3) =>
          Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) :=
        Work.BoseFixR.continuous_chat _ hW1
      exact ((hc.measurable.pow_const 2).div
        ((continuous_norm.pow 3).measurable)).aestronglyMeasurable
    -- the disjoint split of the region `{P₀ < ‖p‖}`
    have hsplit := setIntegral_split_le (f := fun p : EuclideanSpace ℝ (Fin 3) =>
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / ‖p‖ ^ 3)
      (fun p => by positivity) hFmeas hP₀L
    -- integrability of the Coulomb density `Ŵ₁²/‖p‖²`
    have hIntC : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / ‖p‖ ^ 2) := by
      have h0 := Work.BoseFixR.IntegrableChatW1sq h hv hvrad hR hℓ hv_supp hRℓ
      refine (h0.const_mul 2).congr (Filter.Eventually.of_forall (fun q => ?_))
      show (2:ℝ) * ((Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2
            / (2 * ‖q‖ ^ 2)) = (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q) ^ 2 / ‖q‖ ^ 2
      rw [← mul_div_assoc, mul_div_mul_left _ _ (by norm_num : (2:ℝ) ≠ 0)]
    -- the two band bounds
    have hcou := chatW1_coulomb_le (h := h) hR hℓ hv hvrad hv_supp hRℓ
    have hhigh := setIntegral_inv_cube_le (f := fun p : EuclideanSpace ℝ (Fin 3) =>
        (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2) (fun p => sq_nonneg _)
      hApos (le_refl _) hIntC hcou
    have hlow := chatW1_lowTail_le (h := h) hR hℓ hv hvrad hv_supp hRℓ hP₀ hApos hP₀A
    have hlog0 : 0 ≤ Real.log (1 / (P₀ * _root_.BoseGases.a v)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (mul_pos hP₀ hApos)]
      simpa using hP₀A
    -- assembly and numerics
    calc (∫ p in {p : EuclideanSpace ℝ (Fin 3) | P₀ < ‖p‖},
            (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / ‖p‖ ^ 3)
        ≤ (∫ p in {p : EuclideanSpace ℝ (Fin 3) | P₀ < ‖p‖ ∧ ‖p‖ ≤ (_root_.BoseGases.a v)⁻¹},
              (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / ‖p‖ ^ 3)
          + (∫ p in {p : EuclideanSpace ℝ (Fin 3) | (_root_.BoseGases.a v)⁻¹ < ‖p‖},
              (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p) ^ 2 / ‖p‖ ^ 3) := hsplit
      _ ≤ (16 * Real.pi * _root_.BoseGases.a v) ^ 2
            * (4 * Real.pi * (1 + Real.log (1 / (P₀ * _root_.BoseGases.a v))))
          + (_root_.BoseGases.a v) * (512 * Real.pi ^ 4 * (_root_.BoseGases.a v)) :=
          add_le_add hlow hhigh
      _ ≤ 10 ^ 6 * (_root_.BoseGases.a v) ^ 2
            * (1 + Real.log (1 / (P₀ * _root_.BoseGases.a v))) := by
          have hpi0 : (0:ℝ) < Real.pi := Real.pi_pos
          have hsq : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_le_four, hpi0]
          have hpi3 : Real.pi ^ 3 ≤ 64 := by nlinarith [Real.pi_le_four, hsq, hpi0]
          have hpi4 : Real.pi ^ 4 ≤ 256 := by nlinarith [hsq, hpi0]
          have hM2 : 0 ≤ (_root_.BoseGases.a v) ^ 2 := sq_nonneg _
          have h1L : 0 ≤ 1 + Real.log (1 / (P₀ * _root_.BoseGases.a v)) := by linarith
          have h16 : (16 * Real.pi * _root_.BoseGases.a v) ^ 2
              * (4 * Real.pi * (1 + Real.log (1 / (P₀ * _root_.BoseGases.a v))))
              ≤ 65536 * (_root_.BoseGases.a v) ^ 2
                * (1 + Real.log (1 / (P₀ * _root_.BoseGases.a v))) := by
            nlinarith [hpi3, hM2, h1L, mul_nonneg hM2 h1L,
              sq_nonneg (Real.pi * _root_.BoseGases.a v)]
          have h17 : (_root_.BoseGases.a v) * (512 * Real.pi ^ 4 * (_root_.BoseGases.a v))
              ≤ 131072 * (_root_.BoseGases.a v) ^ 2
                * (1 + Real.log (1 / (P₀ * _root_.BoseGases.a v))) := by
            nlinarith [hpi4, hM2, h1L, mul_nonneg hM2 h1L]
          have hT : 0 ≤ (_root_.BoseGases.a v) ^ 2
              * (1 + Real.log (1 / (P₀ * _root_.BoseGases.a v))) := mul_nonneg hM2 h1L
          have h16' : (16 * Real.pi * _root_.BoseGases.a v) ^ 2
              * (4 * Real.pi * (1 + Real.log (1 / (P₀ * _root_.BoseGases.a v))))
              ≤ 65536 * ((_root_.BoseGases.a v) ^ 2
                * (1 + Real.log (1 / (P₀ * _root_.BoseGases.a v)))) := by
            simpa only [mul_assoc] using h16
          have h17' : (_root_.BoseGases.a v) * (512 * Real.pi ^ 4 * (_root_.BoseGases.a v))
              ≤ 131072 * ((_root_.BoseGases.a v) ^ 2
                * (1 + Real.log (1 / (P₀ * _root_.BoseGases.a v)))) := by
            simpa only [mul_assoc] using h17
          nlinarith [h16', h17', hT]

end Work.BoseBogFS

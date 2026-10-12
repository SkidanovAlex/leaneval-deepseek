import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.measurable_tBamp_boxQInd_pair
import Submission.Work.BoseFixB1.setIntegral_indicator_one_acube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory
open Submission.BoseGases

/-- **Slot-invariant indicator integral** (namespace `Work.BoseFixB1`).

Let `Ac ⊆ acube a` be a measurable set of volume `volA > 0`, and let `G` be a function of the
`n`-particle configuration which does not depend on the `i`-th coordinate
(`∀ x t, G (update x i t) = G x`) and is integrable on the centred box `abox n a`.  Then the
`i`-th coordinate of `G` may be replaced by the uniform measure over the box: averaging
`1_{Ac}(x i) G x` over the box is the same as multiplying the box average of `G` by
`volA / a³`.

The proof peels the `i`-th coordinate out of the product box (`abox_integral_peel`), evaluates
the one-particle slice (`setIntegral_indicator_one_acube`), and recognises the same peelled
integral applied to `G` itself. -/
theorem slotInvariant_indicator_integral {n : ℕ} {a volA : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAcsub : Ac ⊆ Submission.BoseGases.acube a) (hvol : volA = (MeasureTheory.volume Ac).toReal)
    (i : Fin n) {G : Submission.BoseGases.X n → ℝ}
    (hGinv : ∀ (x : Submission.BoseGases.X n) (t : EuclideanSpace ℝ (Fin 3)),
      G (Function.update x i t) = G x)
    (hGint : MeasureTheory.IntegrableOn G (Submission.BoseGases.abox n a) MeasureTheory.volume) :
    volA⁻¹ * (∫ x in Submission.BoseGases.abox n a,
        Ac.indicator (fun _ => (1 : ℝ)) (x i) * G x)
      = (a ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox n a, G x) := by
  -- Peel off particle `i`: write `n = m + 1`.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
    ⟨n.pred, (Nat.succ_pred_eq_of_pos (Fin.pos i)).symm⟩
  have ha3 : (0 : ℝ) < a ^ 3 := by positivity
  have hcubevol : (MeasureTheory.volume (Submission.BoseGases.acube a)).toReal = a ^ 3 := by
    rw [Submission.BoseGases.acube_volume a (le_of_lt ha), ENNReal.toReal_ofReal (by positivity)]
  -- The one-particle slice of the indicator.
  have hAint : ∀ c : ℝ, (∫ y in Submission.BoseGases.acube a,
      Ac.indicator (fun _ => (1 : ℝ)) y * c) = volA * c := by
    intro c
    rw [setIntegral_indicator_one_acube hAcm hAcsub (fun _ => c), setIntegral_const,
      Measure.real_def, ← hvol, smul_eq_mul]
  let H : Submission.BoseGases.X (m + 1) → ℝ :=
    fun x => Ac.indicator (fun _ => (1 : ℝ)) (x i) * G x
  change volA⁻¹ * (∫ x in Submission.BoseGases.abox (m + 1) a, H x)
      = (a ^ 3)⁻¹ * (∫ x in Submission.BoseGases.abox (m + 1) a, G x)
  -- `H` is the indicator of `{x | x i ∈ Ac}` times `G`, hence integrable on the box.
  have hHms : MeasurableSet {x : Submission.BoseGases.X (m + 1) | x i ∈ Ac} :=
    hAcm.preimage (measurable_pi_apply i)
  have hH_eq : H = ({x : Submission.BoseGases.X (m + 1) | x i ∈ Ac}).indicator G := by
    funext x
    show Ac.indicator (fun _ => (1 : ℝ)) (x i) * G x
      = ({x : Submission.BoseGases.X (m + 1) | x i ∈ Ac}).indicator G x
    by_cases hx : x i ∈ Ac
    · have hx' : x ∈ {x : Submission.BoseGases.X (m + 1) | x i ∈ Ac} := hx
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx', one_mul]
    · have hx' : x ∉ {x : Submission.BoseGases.X (m + 1) | x i ∈ Ac} := hx
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx', zero_mul]
  have hHint : MeasureTheory.IntegrableOn H (Submission.BoseGases.abox (m + 1) a)
      MeasureTheory.volume := by
    have h1 := hGint.indicator hHms
    simpa [hH_eq] using h1
  -- The peeled slices are constant in the peeled coordinate.
  have hinnerH : ∀ r : Submission.BoseGases.X m,
      (∫ y in Submission.BoseGases.acube a, H (Submission.BoseGases.kcInsN m i (y, r)))
        = volA * G (Submission.BoseGases.kcInsN m i (0, r)) := by
    intro r
    have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
        H (Submission.BoseGases.kcInsN m i (y, r))
          = Ac.indicator (fun _ => (1 : ℝ)) y * G (Submission.BoseGases.kcInsN m i (0, r)) := by
      intro y
      show Ac.indicator (fun _ => (1 : ℝ)) ((Submission.BoseGases.kcInsN m i (y, r)) i)
          * G (Submission.BoseGases.kcInsN m i (y, r))
        = Ac.indicator (fun _ => (1 : ℝ)) y * G (Submission.BoseGases.kcInsN m i (0, r))
      rw [Submission.BoseGases.kc_insN_apply_same]
      congr 1
      rw [← Submission.BoseGases.update_kcInsN i (0 : EuclideanSpace ℝ (Fin 3)) y r]
      exact hGinv (Submission.BoseGases.kcInsN m i (0, r)) y
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact hAint (G (Submission.BoseGases.kcInsN m i (0, r)))
  have hinnerG : ∀ r : Submission.BoseGases.X m,
      (∫ y in Submission.BoseGases.acube a, G (Submission.BoseGases.kcInsN m i (y, r)))
        = a ^ 3 * G (Submission.BoseGases.kcInsN m i (0, r)) := by
    intro r
    have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
        G (Submission.BoseGases.kcInsN m i (y, r))
          = G (Submission.BoseGases.kcInsN m i (0, r)) := by
      intro y
      rw [← Submission.BoseGases.update_kcInsN i (0 : EuclideanSpace ℝ (Fin 3)) y r]
      exact hGinv (Submission.BoseGases.kcInsN m i (0, r)) y
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), setIntegral_const, Measure.real_def,
      hcubevol, smul_eq_mul]
  -- Both box integrals reduce to the same peelled integral.
  have hI : (∫ x in Submission.BoseGases.abox (m + 1) a, H x)
      = volA * (∫ r in Submission.BoseGases.abox m a,
          G (Submission.BoseGases.kcInsN m i (0, r))) := by
    rw [Submission.BoseGases.abox_integral_peel (n := m) (ℓ := a) i H hHint,
      integral_congr_ae (Filter.Eventually.of_forall hinnerH), integral_const_mul]
  have hJ : (∫ x in Submission.BoseGases.abox (m + 1) a, G x)
      = a ^ 3 * (∫ r in Submission.BoseGases.abox m a,
          G (Submission.BoseGases.kcInsN m i (0, r))) := by
    rw [Submission.BoseGases.abox_integral_peel (n := m) (ℓ := a) i G hGint,
      integral_congr_ae (Filter.Eventually.of_forall hinnerG), integral_const_mul]
  rw [hI, hJ, inv_mul_cancel_left₀ (ne_of_gt hvolpos), inv_mul_cancel_left₀ (ne_of_gt ha3)]

end Work.BoseFixB1

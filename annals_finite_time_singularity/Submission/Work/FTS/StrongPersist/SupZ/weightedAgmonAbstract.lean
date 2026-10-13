import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongPersist.SupZ

set_option linter.unusedVariables false

/-- The elementary AM–GM inequality `2√(ab) ≤ a + b` for `a, b ≥ 0`. -/
private lemma two_mul_sqrt_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt (a * b) ≤ a + b := by
  have h4 : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := Real.sqrt_mul ha b
  rw [h4]
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.mul_self_sqrt ha,
    Real.mul_self_sqrt hb]

/--
Abstract (weighted) Agmon inequality.

Assume `F, G ≥ 0` on `(0,∞)`, with `F z / z` and `G z * z` integrable there, and that for
every `x > z₀`
`F z₀ ≤ F x + 2 ∫_{z₀}^{x} √(F s · G s) ds`.
Then `F z₀ ≤ 2 ∫_0^∞ F z / z dz + ∫_0^∞ G z · z dz`.

The proof is the standard Agmon argument: AM–GM turns the integral term into
`∫_{z₀}^{x} (F s / s + G s · s) ds ≤ A + B` where `A = ∫ F/z`, `B = ∫ G·z`, so that
`F z₀ ≤ F x + A + B` for every `x > z₀`. If `A + B < F z₀` held, then `F s ≥ c := F z₀ - A - B >
0` on `(z₀,∞)`, whence `A ≥ ∫_{z₀}^{X} F s/s ds ≥ c log (X / z₀)` for every `X > z₀`, which is
absurd for `X = z₀ · exp (A/c + 1)`. Hence `F z₀ ≤ A + B ≤ 2A + B`. -/
theorem weightedAgmonAbstract {F G : ℝ → ℝ} {z₀ : ℝ} (hz₀ : 0 < z₀)
    (hFm : MeasureTheory.AEStronglyMeasurable F (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hGm : MeasureTheory.AEStronglyMeasurable G (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hFnn : ∀ z ∈ Set.Ioi 0, 0 ≤ F z)
    (hGnn : ∀ z ∈ Set.Ioi 0, 0 ≤ G z)
    (hFint : MeasureTheory.IntegrableOn (fun z : ℝ => F z / z) (Set.Ioi 0))
    (hGint : MeasureTheory.IntegrableOn (fun z : ℝ => G z * z) (Set.Ioi 0))
    (hkey : ∀ x ∈ Set.Ioi z₀, F z₀ ≤ F x + 2 * ∫ s in z₀..x, Real.sqrt (F s * G s)) :
    F z₀ ≤ 2 * (∫ z in Set.Ioi 0, F z / z) + (∫ z in Set.Ioi 0, G z * z) := by
  set A : ℝ := ∫ z in Set.Ioi 0, F z / z with hAdef
  set B : ℝ := ∫ z in Set.Ioi 0, G z * z with hBdef
  have hFnn_ae : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] fun z : ℝ => F z / z := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact div_nonneg (hFnn z hz) hz.le
  have hGnn_ae : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)] fun z : ℝ => G z * z := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    exact mul_nonneg (hGnn z hz) hz.le
  have hA_nonneg : 0 ≤ A := by
    rw [hAdef]
    exact integral_nonneg_of_ae hFnn_ae
  -- It suffices to prove the (stronger) bound `F z₀ ≤ A + B`.
  suffices hmain : F z₀ ≤ A + B by linarith
  by_contra hcon
  rw [not_le] at hcon
  -- AM–GM replaces `2√(F s G s)` by `F s / s + G s * s`.
  have hkeyb : ∀ x ∈ Set.Ioi z₀, 2 * ∫ s in z₀..x, Real.sqrt (F s * G s) ≤ A + B := by
    intro x hx
    have hxle : z₀ ≤ x := le_of_lt hx
    have hsub : Set.Ioc z₀ x ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_trans hz₀ hs.1
    have hsum_int : MeasureTheory.IntegrableOn (fun s : ℝ => F s / s + G s * s)
        (Set.Ioc z₀ x) := (hFint.mono_set hsub).add (hGint.mono_set hsub)
    have hsum_int0 : MeasureTheory.IntegrableOn (fun s : ℝ => F s / s + G s * s)
        (Set.Ioi 0) := hFint.add hGint
    have hsum_nn : 0 ≤ᵐ[volume.restrict (Set.Ioi 0)]
        fun s : ℝ => F s / s + G s * s := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
      exact add_nonneg (div_nonneg (hFnn s hs) hs.le) (mul_nonneg (hGnn s hs) hs.le)
    calc 2 * ∫ s in z₀..x, Real.sqrt (F s * G s)
        = ∫ s in z₀..x, 2 * Real.sqrt (F s * G s) :=
          (intervalIntegral.integral_const_mul 2
            (fun s : ℝ => Real.sqrt (F s * G s))).symm
      _ = ∫ s in Set.Ioc z₀ x, 2 * Real.sqrt (F s * G s) := by
          rw [intervalIntegral.integral_of_le hxle]
      _ ≤ ∫ s in Set.Ioc z₀ x, (F s / s + G s * s) := by
          refine setIntegral_mono_of_nonneg (fun s _ => ?_) (fun s hs => ?_) hsum_int
          · exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
          · have hs0 : 0 < s := lt_trans hz₀ hs.1
            have ha : 0 ≤ F s / s := div_nonneg (hFnn s hs0) hs0.le
            have hb : 0 ≤ G s * s := mul_nonneg (hGnn s hs0) hs0.le
            have hprod : F s / s * (G s * s) = F s * G s := by field_simp
            have h := two_mul_sqrt_mul_le ha hb
            rwa [hprod] at h
      _ ≤ ∫ s in Set.Ioi (0 : ℝ), (F s / s + G s * s) := by
          refine setIntegral_mono_set hsum_int0 hsum_nn ?_
          exact Filter.Eventually.of_forall fun s hs => hsub hs
      _ = A + B := by rw [integral_add hFint hGint, ← hAdef, ← hBdef]
  -- Hence `F s ≥ c` on `(z₀,∞)`, where `c = F z₀ - (A + B) > 0`.
  set c : ℝ := F z₀ - (A + B) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; linarith
  have hstep : ∀ x ∈ Set.Ioi z₀, c ≤ F x := by
    intro x hx
    have h1 := hkey x hx
    have h2 := hkeyb x hx
    rw [hcdef]; linarith
  -- Choose `X = z₀ · exp (A/c + 1)`, so that `∫_{z₀}^{X} c/s = A + c`.
  set X : ℝ := z₀ * Real.exp (A / c + 1) with hXdef
  have hXpos : 0 < X := by rw [hXdef]; exact mul_pos hz₀ (Real.exp_pos _)
  have hXgt : z₀ < X := by
    have h1 : 1 < Real.exp (A / c + 1) :=
      Real.one_lt_exp_iff.mpr (add_pos_of_nonneg_of_pos (div_nonneg hA_nonneg hcpos.le) one_pos)
    rw [hXdef]
    simpa using mul_lt_mul_of_pos_left h1 hz₀
  have hXdiv : X / z₀ = Real.exp (A / c + 1) := by rw [hXdef]; field_simp
  have hlog : Real.log (X / z₀) = A / c + 1 := by rw [hXdiv, Real.log_exp]
  have hsubX : Set.Ioc z₀ X ⊆ Set.Ioi (0 : ℝ) := fun s hs => lt_trans hz₀ hs.1
  have hFintX : IntervalIntegrable (fun s : ℝ => F s / s) volume z₀ X :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hXgt.le).mpr (hFint.mono_set hsubX)
  have hcintX : IntervalIntegrable (fun s : ℝ => c / s) volume z₀ X := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hXgt.le]
    exact ContinuousOn.div continuousOn_const continuousOn_id
      (fun s hs => ne_of_gt (lt_of_lt_of_le hz₀ hs.1))
  have hval : c * (A / c + 1) = A + c := by
    have : c ≠ 0 := ne_of_gt hcpos
    field_simp
  -- Lower bound on `∫_{z₀}^{X} F s / s`.
  have hlow : c * (A / c + 1) ≤ ∫ s in z₀..X, F s / s := by
    have hcle : ∫ s in z₀..X, c / s ≤ ∫ s in z₀..X, F s / s := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo hXgt.le hcintX hFintX ?_
      intro s hs
      have hs0 : 0 < s := lt_trans hz₀ hs.1
      exact div_le_div_of_nonneg_right (hstep s hs.1) hs0.le
    have heq : ∫ s in z₀..X, c / s = c * (A / c + 1) := by
      calc ∫ s in z₀..X, c / s
          = ∫ s in z₀..X, c * s⁻¹ := by simp only [div_eq_mul_inv]
        _ = c * ∫ s in z₀..X, s⁻¹ := intervalIntegral.integral_const_mul c _
        _ = c * Real.log (X / z₀) := by rw [integral_inv_of_pos hz₀ hXpos]
        _ = c * (A / c + 1) := by rw [hlog]
    linarith
  -- Upper bound on `∫_{z₀}^{X} F s / s`, coming from integrability on `(0,∞)`.
  have hup : ∫ s in z₀..X, F s / s ≤ A := by
    rw [intervalIntegral.integral_of_le hXgt.le]
    calc ∫ s in Set.Ioc z₀ X, F s / s
        ≤ ∫ s in Set.Ioi (0 : ℝ), F s / s := by
          refine setIntegral_mono_set hFint hFnn_ae ?_
          exact Filter.Eventually.of_forall fun s hs => hsubX hs
      _ = A := by rw [hAdef]
  linarith

end Work.FTS.StrongPersist.SupZ

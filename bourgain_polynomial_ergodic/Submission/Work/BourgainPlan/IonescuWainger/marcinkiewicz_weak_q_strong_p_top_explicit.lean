import Mathlib
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_q_strong_p_top

/-!
# Marcinkiewicz interpolation with an explicit constant

Weak type `(q,q)` with constant `A₀` together with strong type `(∞,∞)` with constant `A₁`
gives strong type `(p,p)` for every `p > q`, with the explicit constant

`C = (p (2A₀)^q (2A₁)^{p-q} / (p-q))^{1/p}`.

This is the explicit-constant form of
`Commons.Analysis.MeasureTheory.marcinkiewicz_weak_q_strong_p_top`; the proof is the same
truncation/layer-cake argument, with the constant `K = p (2A₀)^q (2A₁)^{p-q}/(p-q)`
carried through instead of existentially quantified away.
-/

open MeasureTheory Measure Filter Set
open scoped ENNReal

namespace Work.BourgainPlan.IonescuWainger

theorem marcinkiewicz_weak_q_strong_p_top_explicit {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {μ : MeasureTheory.Measure α} [MeasureTheory.SFinite μ] {ν : MeasureTheory.Measure β}
    (T : (α → E) → (β → E)) (hadd : ∀ f g : α → E, T (f + g) = T f + T g)
    (hmeas : ∀ f : α → E, AEMeasurable (T f) ν)
    {q A0 A1 : ℝ} (hq : 1 ≤ q) (hA0 : 0 < A0) (hA1 : 0 < A1)
    (hweak : ∀ (f : α → E) (lam : ℝ), 0 < lam →
      ν {x : β | lam < ‖T f x‖}
        ≤ ENNReal.ofReal (A0 / lam) ^ q * (MeasureTheory.eLpNorm f (ENNReal.ofReal q) μ) ^ q)
    (hstrong : ∀ f : α → E,
      MeasureTheory.eLpNorm (T f) ⊤ ν ≤ ENNReal.ofReal A1 * MeasureTheory.eLpNorm f ⊤ μ)
    {p : ℝ} (hp : q < p) :
    ∀ f : α → E, Measurable f →
      MeasureTheory.eLpNorm (T f) (ENNReal.ofReal p) ν
        ≤ ENNReal.ofReal ((p * (2*A0)^q * (2*A1)^(p-q) / (p-q)) ^ (1/p))
          * MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp0 : 0 < p := lt_trans hq0 hp
  have hr0 : -1 < p - 1 - q := by linarith
  set K : ℝ := p * (2*A0)^q * (2*A1)^(p-q) / (p-q) with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  have hKnn : 0 ≤ K := hKpos.le
  intro f hf
  have hCpos : ENNReal.ofReal (K ^ (1/p)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hKpos _)).ne'
  by_cases hfm : AEStronglyMeasurable f μ
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hfm, ENNReal.mul_top hCpos]
    exact le_top
  by_cases hfin : eLpNorm f (ENNReal.ofReal p) μ = ∞
  · rw [hfin, ENNReal.mul_top hCpos]
    exact le_top
  have hTm : AEStronglyMeasurable (T f) ν :=
    Commons.Analysis.MeasureTheory.wq_aestronglyMeasurable_T T hadd hq0 hweak hstrong hp hfm hfin
  have hvm : Measurable fun x : α => ‖f x‖ := hf.norm
  have hvnn : ∀ x : α, 0 ≤ ‖f x‖ := fun x => norm_nonneg _
  set Ψ : ℝ → ℝ≥0∞ := fun t => ∫⁻ x,
      Set.indicator {x : α | ENNReal.ofReal (t / (2*A1)) < ENNReal.ofReal ‖f x‖}
        (fun x => ENNReal.ofReal ‖f x‖ ^ q) x ∂μ with hΨ
  have hlayer : ∫⁻ x, ‖T f x‖ₑ ^ p ∂ν
      = ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0:ℝ),
          ν {x : β | t < ‖T f x‖} * ENNReal.ofReal (t ^ (p - 1)) := by
    have hcongr : ∫⁻ x, ‖T f x‖ₑ ^ p ∂ν = ∫⁻ x, ENNReal.ofReal (‖T f x‖ ^ p) ∂ν := by
      refine lintegral_congr fun x => ?_
      simpa only [ofReal_norm] using
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (T f x)) hp0.le
    rw [hcongr]
    exact lintegral_rpow_eq_lintegral_meas_lt_mul ν (f := fun x => ‖T f x‖)
      (Eventually.of_forall fun x => norm_nonneg _) ((hmeas f).norm) hp0
  have hA : ∫⁻ t in Set.Ioi (0:ℝ), ν {x : β | t < ‖T f x‖} * ENNReal.ofReal (t ^ (p - 1))
      ≤ ENNReal.ofReal ((2*A0)^q) *
          ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-1-q)) * Ψ t := by
    have hstep : ∫⁻ t in Set.Ioi (0:ℝ), ν {x : β | t < ‖T f x‖} * ENNReal.ofReal (t ^ (p - 1))
        ≤ ∫⁻ t in Set.Ioi (0:ℝ),
            (ENNReal.ofReal (2*A0/t)^q * Ψ t) * ENNReal.ofReal (t ^ (p - 1)) := by
      refine lintegral_mono_ae ?_
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have h1 := Commons.Analysis.MeasureTheory.lvl_set_q (μ := μ) (ν := ν) T hadd hq0 hA1
        hweak hstrong f hfm ht
      simp only [hΨ] at h1 ⊢
      exact mul_le_mul_of_nonneg_right h1 bot_le
    have hconst : ∀ t : ℝ, 0 < t →
        ENNReal.ofReal (2*A0/t)^q * ENNReal.ofReal (t^(p-1))
          = ENNReal.ofReal ((2*A0)^q) * ENNReal.ofReal (t^(p-1-q)) := by
      intro t ht
      have hreal : (2*A0/t)^q * t^(p-1) = (2*A0)^q * t^(p-1-q) := by
        rw [Real.div_rpow (by positivity) ht.le q]
        rw [div_eq_mul_inv, ← Real.rpow_neg ht.le q]
        rw [mul_assoc, ← Real.rpow_add ht (-q) (p-1)]
        congr 1; ring_nf
      calc ENNReal.ofReal (2*A0/t)^q * ENNReal.ofReal (t^(p-1))
          = ENNReal.ofReal ((2*A0/t)^q) * ENNReal.ofReal (t^(p-1)) := by
              rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : (0:ℝ) ≤ 2*A0/t) hq0.le]
        _ = ENNReal.ofReal ((2*A0/t)^q * t^(p-1)) := (ENNReal.ofReal_mul (by positivity)).symm
        _ = ENNReal.ofReal ((2*A0)^q * t^(p-1-q)) := by rw [hreal]
        _ = ENNReal.ofReal ((2*A0)^q) * ENNReal.ofReal (t^(p-1-q)) := ENNReal.ofReal_mul (by positivity)
    calc ∫⁻ t in Set.Ioi (0:ℝ), ν {x : β | t < ‖T f x‖} * ENNReal.ofReal (t ^ (p - 1))
        ≤ ∫⁻ t in Set.Ioi (0:ℝ),
            (ENNReal.ofReal (2*A0/t)^q * Ψ t) * ENNReal.ofReal (t ^ (p - 1)) := hstep
      _ = ∫⁻ t in Set.Ioi (0:ℝ),
            ENNReal.ofReal ((2*A0)^q) * (ENNReal.ofReal (t^(p-1-q)) * Ψ t) := by
          refine lintegral_congr_ae ?_
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          calc ENNReal.ofReal (2*A0/t)^q * Ψ t * ENNReal.ofReal (t^(p-1))
              = (ENNReal.ofReal (2*A0/t)^q * ENNReal.ofReal (t^(p-1))) * Ψ t := by ring
            _ = (ENNReal.ofReal ((2*A0)^q) * ENNReal.ofReal (t^(p-1-q))) * Ψ t := by
                rw [hconst t ht]
            _ = ENNReal.ofReal ((2*A0)^q) * (ENNReal.ofReal (t^(p-1-q)) * Ψ t) := by ring
      _ = ENNReal.ofReal ((2*A0)^q) *
            ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(p-1-q)) * Ψ t :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hB : ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p-1-q)) * Ψ t
      = ENNReal.ofReal ((2*A1)^(p-q)/(p-q)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
    simp only [hΨ]
    rw [Commons.Analysis.MeasureTheory.key_lintegral (μ := μ) (v := fun x => ‖f x‖) hvm hvnn hA1
      (q := q) (r := p-1-q) hq0.le hr0]
    rw [show (2*A1)^(p-1-q+1)/(p-1-q+1) = (2*A1)^(p-q)/(p-q) by
      rw [show p - 1 - q + 1 = p - q by ring]]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [show q + (p - 1 - q) + 1 = p from by ring, ofReal_norm]
  have hKconst : ENNReal.ofReal K
      = ENNReal.ofReal p * (ENNReal.ofReal ((2*A0)^q) * ENNReal.ofReal ((2*A1)^(p-q)/(p-q))) := by
    rw [hK, show p * (2*A0)^q * (2*A1)^(p-q)/(p-q)
          = (p * (2*A0)^q) * ((2*A1)^(p-q)/(p-q)) by ring]
    rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ p * (2*A0)^q)]
    rw [show ENNReal.ofReal (p * (2*A0)^q) = ENNReal.ofReal p * ENNReal.ofReal ((2*A0)^q) from
      ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ p)]
    ring
  have hmain : ∫⁻ x, ‖T f x‖ₑ ^ p ∂ν ≤ ENNReal.ofReal K * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
    rw [hlayer]
    calc ENNReal.ofReal p * ∫⁻ t in Set.Ioi (0:ℝ),
            ν {x : β | t < ‖T f x‖} * ENNReal.ofReal (t ^ (p - 1))
        ≤ ENNReal.ofReal p * (ENNReal.ofReal ((2*A0)^q) *
            ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(p-1-q)) * Ψ t) :=
            mul_le_mul_of_nonneg_left hA bot_le
      _ = ENNReal.ofReal p * (ENNReal.ofReal ((2*A0)^q) *
            (ENNReal.ofReal ((2*A1)^(p-q)/(p-q)) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ)) := by rw [hB]
      _ = ENNReal.ofReal K * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by rw [hKconst]; ring
  have hL : MeasureTheory.eLpNorm (T f) (ENNReal.ofReal p) ν
      = (∫⁻ x, ‖T f x‖ₑ ^ p ∂ν) ^ (1/p) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p)
      (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top hTm, ENNReal.toReal_ofReal hp0.le]
  have hR : MeasureTheory.eLpNorm f (ENNReal.ofReal p) μ
      = (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) := by
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := ENNReal.ofReal p)
      (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top hfm, ENNReal.toReal_ofReal hp0.le]
  rw [hL, hR]
  calc (∫⁻ x, ‖T f x‖ₑ ^ p ∂ν) ^ (1/p)
      ≤ (ENNReal.ofReal K * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) :=
          ENNReal.rpow_le_rpow hmain (by positivity)
    _ = (ENNReal.ofReal K) ^ (1/p) * (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) :=
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = ENNReal.ofReal (K ^ (1/p)) * (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hKnn (by positivity)]
    _ = ENNReal.ofReal ((p * (2*A0)^q * (2*A1)^(p-q) / (p-q)) ^ (1/p))
          * (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ^ (1/p) := by rw [hK]

end Work.BourgainPlan.IonescuWainger

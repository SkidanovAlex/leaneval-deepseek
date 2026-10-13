/-
# The `(0,1)` interval-integral tool for the radial honesty estimates

Two measure-theory lemmas used by `radGreen_l2_near_zero` (and reusable for the whole
`FTS/EllExist/Honesty` area):

* `integrableOn_Ioo_of_bounded_intervalIntegrals` — a nonnegative continuous function on an open
  interval `(a,β)` whose integrals over all compact subintervals are bounded by `M` is integrable
  on `(a,β)` (and its integral is at most `M`).  This is the standard "improper integral of a
  nonnegative continuous function is the supremum of the integrals over compact subintervals"
  statement, proved here by exhausting `(a,β)` with the intervals `Ioc (a + 1/(n+1)) (β - 1/(n+1))`
  and applying `MeasureTheory.AECover.integrable_of_integral_bounded_of_nonneg_ae` /
  `MeasureTheory.AECover.iSup_lintegral_eq_of_countably_generated`.

* `integrableOn_add_sq_div_of_interval_bounds` — the assembly step: if `F` and `G` are continuous on
  `(0,1)` and their weighted squares `F z²/z⁴`, `G z²/z⁴` have uniformly bounded interval integrals
  over `0 < x < y < 1`, then the weighted square of the sum is integrable on `(0,1)`.  This is what
  turns the two estimates for the Green terms `G1`, `G2` of `radGreen` into the honesty of
  `radGreen` itself.

(Adapted from the argument of `Submission/Work/FTS/EllipticEst/remov/
integrableOn_of_bounded_intervalIntegrals.lean`, which is not compilable in this tree — it is
missing `open scoped Topology` and has no build record — so the tool is carried here, in the
`Honesty` area, to keep the honesty development independent of a broken module.)
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace Work.FTS.EllExist.Honesty

/-- If `f` is continuous and nonnegative on the open interval `(a, β)` and every interval
integral `∫ t in x..y, f t` with `a < x < y < β` is bounded above by `M`, then `f` is
integrable on `(a, β)` and its integral is at most `M`. -/
theorem integrableOn_Ioo_of_bounded_intervalIntegrals {a β : ℝ} (ha : a < β) {f : ℝ → ℝ} {M : ℝ}
    (hcont : ContinuousOn f (Set.Ioo a β))
    (hnn : ∀ x ∈ Set.Ioo a β, 0 ≤ f x)
    (hK : ∀ x y, a < x → x < y → y < β → (∫ t in x..y, f t) ≤ M) :
    MeasureTheory.IntegrableOn f (Set.Ioo a β) ∧ (∫ t in Set.Ioo a β, f t) ≤ M := by
  have hMnn : 0 ≤ M := by
    have h1 : (0 : ℝ) ≤ ∫ t in (2 * a + β) / 3..(a + 2 * β) / 3, f t := by
      refine intervalIntegral.integral_nonneg (by linarith) fun u hu => ?_
      exact hnn u ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h2 : (∫ t in (2 * a + β) / 3..(a + 2 * β) / 3, f t) ≤ M :=
      hK _ _ (by linarith) (by linarith) (by linarith)
    linarith
  set c : ℕ → ℝ := fun n => a + 1 / ((n : ℝ) + 1) with hcdef
  set d : ℕ → ℝ := fun n => β - 1 / ((n : ℝ) + 1) with hddef
  have hc_lt : ∀ n, a < c n := by
    intro n
    simp only [hcdef]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hd_gt : ∀ n, d n < β := by
    intro n
    simp only [hddef]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hc_tendsto : Tendsto c atTop (𝓝 a) := by
    simp only [hcdef]
    simpa using (tendsto_const_nhds (x := a)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hd_tendsto : Tendsto d atTop (𝓝 β) := by
    simp only [hddef]
    simpa using (tendsto_const_nhds (x := β)).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsub : ∀ n, Set.Ioc (c n) (d n) ⊆ Set.Ioo a β := fun n x hx =>
    ⟨lt_trans (hc_lt n) hx.1, lt_of_le_of_lt hx.2 (hd_gt n)⟩
  have hsubIcc : ∀ n, Set.Icc (c n) (d n) ⊆ Set.Ioo a β := fun n x hx =>
    ⟨lt_of_lt_of_le (hc_lt n) hx.1, lt_of_le_of_lt hx.2 (hd_gt n)⟩
  have hφ : AECover (volume.restrict (Set.Ioo a β)) atTop fun n => Set.Ioc (c n) (d n) :=
    aecover_Ioo_of_Ioc hc_tendsto hd_tendsto
  have hfi : ∀ n, IntegrableOn f (Set.Ioc (c n) (d n)) (volume.restrict (Set.Ioo a β)) := fun n =>
    (((hcont.mono (hsubIcc n)).integrableOn_compact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self).restrict
  have hnng' : ∀ᵐ x ∂(volume.restrict (Set.Ioo a β)), 0 ≤ f x := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact ae_of_all _ fun x hx => hnn x hx
  -- The integral over each subinterval is at most `M`.
  have hbound : ∀ n, ∫ x in Set.Ioc (c n) (d n), f x ∂(volume.restrict (Set.Ioo a β)) ≤ M := by
    intro n
    rcases lt_or_ge (c n) (d n) with hlt | hge
    · have hmeas : (volume.restrict (Set.Ioo a β)).restrict (Set.Ioc (c n) (d n))
          = volume.restrict (Set.Ioc (c n) (d n)) := by
        rw [Measure.restrict_restrict measurableSet_Ioc, Set.inter_eq_left.mpr (hsub n)]
      have hconv : ∫ x in Set.Ioc (c n) (d n), f x ∂(volume.restrict (Set.Ioo a β))
          = ∫ x in c n..d n, f x := by
        rw [hmeas]
        exact (intervalIntegral.integral_of_le hlt.le).symm
      rw [hconv]
      exact hK (c n) (d n) (hc_lt n) hlt (hd_gt n)
    · have hempty : Set.Ioc (c n) (d n) = ∅ := by
        rw [Set.Ioc_eq_empty_iff]
        exact not_lt.mpr hge
      rw [hempty, Measure.restrict_empty, integral_zero_measure]
      exact hMnn
  have hfm : AEMeasurable (fun x => ENNReal.ofReal (f x)) (volume.restrict (Set.Ioo a β)) :=
    (hcont.aemeasurable measurableSet_Ioo (μ := volume)).ennreal_ofReal
  have hbound_lin : ∀ n, ∫⁻ x in Set.Ioc (c n) (d n), ENNReal.ofReal (f x)
      ∂(volume.restrict (Set.Ioo a β)) ≤ ENNReal.ofReal M := by
    intro n
    have hnngn : 0 ≤ᵐ[(volume.restrict (Set.Ioo a β)).restrict (Set.Ioc (c n) (d n))] f :=
      ae_mono Measure.restrict_le_self hnng'
    have key := ofReal_integral_eq_lintegral_ofReal (hfi n) hnngn
    rw [← key]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  -- Monotone convergence over the exhausting sequence of intervals.
  have hlin : ∫⁻ x in Set.Ioo a β, ENNReal.ofReal (f x) ≤ ENNReal.ofReal M := by
    rw [← hφ.iSup_lintegral_eq_of_countably_generated hfm]
    exact iSup_le hbound_lin
  refine ⟨hφ.integrable_of_integral_bounded_of_nonneg_ae M hfi hnng'
    (Eventually.of_forall hbound), ?_⟩
  calc (∫ t in Set.Ioo a β, f t)
      = (∫⁻ t in Set.Ioo a β, ENNReal.ofReal (f t)).toReal :=
        integral_eq_lintegral_of_nonneg_ae hnng' (hcont.aestronglyMeasurable measurableSet_Ioo)
    _ ≤ (ENNReal.ofReal M).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
    _ = M := ENNReal.toReal_ofReal hMnn

/-- Assembly step for the honesty of `radGreen`: if `F`, `G` are continuous on `(0,1)` and the
weighted squares `F z^2/z^4`, `G z^2/z^4` have uniformly bounded interval integrals over
`0 < x < y < 1`, then the weighted square of the sum is integrable on `(0,1)`. -/
theorem integrableOn_add_sq_div_of_interval_bounds {F G : ℝ → ℝ} {M₁ M₂ : ℝ}
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hFc : ContinuousOn F (Set.Ioo 0 1)) (hGc : ContinuousOn G (Set.Ioo 0 1))
    (hF : ∀ x y : ℝ, 0 < x → x < y → y < 1 → (∫ z in x..y, F z ^ 2 / z ^ 4) ≤ M₁)
    (hG : ∀ x y : ℝ, 0 < x → x < y → y < 1 → (∫ z in x..y, G z ^ 2 / z ^ 4) ≤ M₂) :
    MeasureTheory.IntegrableOn (fun z => (F z + G z) ^ 2 / z ^ 4) (Set.Ioo 0 1) := by
  have hcont : ContinuousOn (fun z => (F z + G z) ^ 2 / z ^ 4) (Set.Ioo (0 : ℝ) 1) := by
    refine (((hFc.add hGc).pow 2).div (continuous_pow 4).continuousOn) fun z hz => ?_
    exact pow_ne_zero 4 (ne_of_gt hz.1)
  refine (integrableOn_Ioo_of_bounded_intervalIntegrals (a := 0) (β := 1)
    (M := 2 * M₁ + 2 * M₂) one_pos hcont (fun z hz => ?_) (fun x y hx hxy hy => ?_)).1
  · have hz4 : 0 < z ^ 4 := pow_pos hz.1 4
    positivity
  · -- pointwise domination of the sum by twice the two squares
    have hpt : ∀ z ∈ Set.Icc x y, (F z + G z) ^ 2 / z ^ 4
        ≤ 2 * (F z ^ 2 / z ^ 4) + 2 * (G z ^ 2 / z ^ 4) := by
      intro z hz
      have hz4 : 0 < z ^ 4 := pow_pos (lt_of_lt_of_le hx hz.1) 4
      have h1 : (F z + G z) ^ 2 ≤ 2 * F z ^ 2 + 2 * G z ^ 2 := by
        nlinarith [sq_nonneg (F z - G z)]
      have h2 : (2 * F z ^ 2 + 2 * G z ^ 2) / z ^ 4
          = 2 * (F z ^ 2 / z ^ 4) + 2 * (G z ^ 2 / z ^ 4) := by
        field_simp
      have h3 := div_le_div_of_nonneg_right h1 hz4.le
      rwa [h2] at h3
    -- interval integrability on `x..y ⊆ (0,1)`, via continuity
    have hsub : Set.uIcc x y ⊆ Set.Ioo (0 : ℝ) 1 := by
      intro z hz
      rw [Set.uIcc_of_le hxy.le] at hz
      exact ⟨lt_of_lt_of_le hx hz.1, lt_of_le_of_lt hz.2 hy⟩
    have hc1 : ContinuousOn (fun z => F z ^ 2 / z ^ 4) (Set.uIcc x y) :=
      ((hFc.mono hsub).pow 2).div (continuous_pow 4).continuousOn
        (fun z hz => pow_ne_zero 4 (ne_of_gt (hsub hz).1))
    have hc2 : ContinuousOn (fun z => G z ^ 2 / z ^ 4) (Set.uIcc x y) :=
      ((hGc.mono hsub).pow 2).div (continuous_pow 4).continuousOn
        (fun z hz => pow_ne_zero 4 (ne_of_gt (hsub hz).1))
    have hI1 : IntervalIntegrable (fun z => (F z + G z) ^ 2 / z ^ 4) volume x y :=
      (hcont.mono hsub).intervalIntegrable
    have hI2 : IntervalIntegrable (fun z => 2 * (F z ^ 2 / z ^ 4) + 2 * (G z ^ 2 / z ^ 4))
        volume x y :=
      ((hc1.const_mul 2).add (hc2.const_mul 2)).intervalIntegrable
    have hI1a : IntervalIntegrable (fun z => F z ^ 2 / z ^ 4) volume x y := hc1.intervalIntegrable
    have hI2a : IntervalIntegrable (fun z => G z ^ 2 / z ^ 4) volume x y := hc2.intervalIntegrable
    have hmono := intervalIntegral.integral_mono_on hxy.le hI1 hI2 hpt
    have hsplit : (∫ z in x..y, (2 * (F z ^ 2 / z ^ 4) + 2 * (G z ^ 2 / z ^ 4)))
        = 2 * (∫ z in x..y, F z ^ 2 / z ^ 4) + 2 * (∫ z in x..y, G z ^ 2 / z ^ 4) := by
      rw [intervalIntegral.integral_add (hI1a.const_mul 2) (hI2a.const_mul 2),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [hsplit] at hmono
    linarith [hF x y hx hxy hy, hG x y hx hxy hy]

end Work.FTS.EllExist.Honesty

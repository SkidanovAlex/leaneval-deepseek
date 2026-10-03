import Mathlib

/-!
# Integrability of `β ↦ (min N (C |β|^{-1/d}))^{2s}`

For `C > 0`, `d ≥ 1` and integers `N` and `s` with `d < 2s`, the function

`β ↦ (min (N : ℝ) (C * |β| ^ (-(1:ℝ)/(d:ℝ)))) ^ (2*s)`

is Lebesgue-integrable on `ℝ`.

Indeed it is bounded by `N ^ (2*s)` on the unit interval `{|β| ≤ 1}` (a set of finite
measure) and by `C ^ (2*s) * |β| ^ (-(2s)/d)` on its complement; the latter exponent is
`< -1` because `2s > d`, so `x ^ (-(2s)/d)` is integrable on `(1, ∞)` (Mathlib's
`integrableOn_Ioi_rpow_of_lt`), and symmetry (`x ↦ -x` preserves Lebesgue measure) gives
integrability on `(-∞, -1)` as well.  This is the standing hypothesis that makes the
`β`-integral of the major-arc computation of §5 well defined.

The auxiliary `decay` bound `C ^ (2s) * |β| ^ (-(2s)/d)` together with the two pointwise
bounds on the integrand are also useful on their own; they are proved here as private
lemmas.
-/

set_option maxHeartbeats 800000

namespace Work.A3

open MeasureTheory

/-- The integrand of the A3 `β`-integral: `(min N (C |β|^{-1/d}))^{2s}`. -/
private noncomputable def ibeta (C : ℝ) (d N s : ℕ) : ℝ → ℝ :=
  fun β => (min (N : ℝ) (C * |β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s)

/-- The integrand `ibeta` is (Borel) measurable: away from `0` it is continuous, and a function
continuous on the complement of a point is measurable. -/
private lemma ibeta_measurable (C : ℝ) (d N s : ℕ) : Measurable (ibeta C d N s) := by
  show Measurable (fun β : ℝ => (min (N : ℝ) (C * |β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s))
  have hcont : ContinuousOn (fun β : ℝ => |β| ^ (-(1 : ℝ) / (d : ℝ))) ({0}ᶜ : Set ℝ) := by
    refine (continuous_abs.continuousOn).rpow_const ?_
    intro x hx
    exact Or.inl (abs_ne_zero.mpr (by simpa using hx))
  have hmeas : Measurable (fun β : ℝ => |β| ^ (-(1 : ℝ) / (d : ℝ))) :=
    measurable_of_continuousOn_compl_singleton 0 hcont
  exact (measurable_const.min (measurable_const.mul hmeas)).pow_const (2 * s)

/-- The integrand is bounded by `N ^ (2s)`. -/
private lemma norm_ibeta_le_const (C : ℝ) (hC : 0 < C) (d N s : ℕ) (β : ℝ) :
    ‖ibeta C d N s β‖ ≤ (N : ℝ) ^ (2 * s) := by
  show ‖(min (N : ℝ) (C * |β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s)‖ ≤ (N : ℝ) ^ (2 * s)
  have hb : 0 ≤ C * |β| ^ (-(1 : ℝ) / (d : ℝ)) :=
    mul_nonneg (le_of_lt hC) (Real.rpow_nonneg (abs_nonneg β) _)
  have hnn : 0 ≤ min (N : ℝ) (C * |β| ^ (-(1 : ℝ) / (d : ℝ))) :=
    le_min (Nat.cast_nonneg N) hb
  rw [Real.norm_of_nonneg (pow_nonneg hnn _)]
  exact pow_le_pow_left₀ hnn (min_le_left _ _) (2 * s)

/-- The integrand is dominated by the decaying function `C ^ (2s) * |β| ^ (-(2s)/d)`. -/
private lemma norm_ibeta_le_decay (C : ℝ) (hC : 0 < C) (d : ℕ) (hd : 1 ≤ d) (N s : ℕ)
    (β : ℝ) :
    ‖ibeta C d N s β‖ ≤ C ^ (2 * s) * |β| ^ (-(2 * (s : ℝ)) / (d : ℝ)) := by
  show ‖(min (N : ℝ) (C * |β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s)‖
      ≤ C ^ (2 * s) * |β| ^ (-(2 * (s : ℝ)) / (d : ℝ))
  have hb : 0 ≤ C * |β| ^ (-(1 : ℝ) / (d : ℝ)) :=
    mul_nonneg (le_of_lt hC) (Real.rpow_nonneg (abs_nonneg β) _)
  have hnn : 0 ≤ min (N : ℝ) (C * |β| ^ (-(1 : ℝ) / (d : ℝ))) :=
    le_min (Nat.cast_nonneg N) hb
  have hexp : (-(1 : ℝ) / (d : ℝ)) * ((2 * s : ℕ) : ℝ) = -(2 * (s : ℝ)) / (d : ℝ) := by
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    rw [Nat.cast_mul, Nat.cast_ofNat]
    field_simp
  rw [Real.norm_of_nonneg (pow_nonneg hnn _)]
  calc (min (N : ℝ) (C * |β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s)
      ≤ (C * |β| ^ (-(1 : ℝ) / (d : ℝ))) ^ (2 * s) :=
        pow_le_pow_left₀ hnn (min_le_right _ _) (2 * s)
    _ = C ^ (2 * s) * |β| ^ (-(2 * (s : ℝ)) / (d : ℝ)) := by
        rw [mul_pow, ← Real.rpow_mul_natCast (x := |β|) (abs_nonneg β) (-(1 : ℝ) / (d : ℝ))
          (2 * s), hexp]

/-- The decaying majorant is integrable on `{β | 1 < |β|}`. -/
private lemma integrableOn_decay (C : ℝ) (d s : ℕ) (hd : 1 ≤ d) (hs : d < 2 * s) :
    IntegrableOn (fun β : ℝ => C ^ (2 * s) * |β| ^ (-(2 * (s : ℝ)) / (d : ℝ)))
      {β : ℝ | 1 < |β|} := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hq : -(2 * (s : ℝ)) / (d : ℝ) < -1 := by
    have hsR : (d : ℝ) < 2 * (s : ℝ) := by exact_mod_cast hs
    rw [neg_div, neg_lt_neg_iff, one_lt_div hd0]
    linarith
  have hIoi : IntegrableOn (fun β : ℝ => C ^ (2 * s) * |β| ^ (-(2 * (s : ℝ)) / (d : ℝ)))
      (Set.Ioi 1) volume := by
    have hbase : IntegrableOn (fun β : ℝ => β ^ (-(2 * (s : ℝ)) / (d : ℝ))) (Set.Ioi 1) volume :=
      integrableOn_Ioi_rpow_of_lt hq zero_lt_one
    have hcm : IntegrableOn (fun β : ℝ => C ^ (2 * s) * β ^ (-(2 * (s : ℝ)) / (d : ℝ)))
        (Set.Ioi 1) volume := hbase.const_mul (C ^ (2 * s))
    refine IntegrableOn.congr_fun hcm ?_ measurableSet_Ioi
    intro β hβ
    show C ^ (2 * s) * β ^ (-(2 * (s : ℝ)) / (d : ℝ))
      = C ^ (2 * s) * |β| ^ (-(2 * (s : ℝ)) / (d : ℝ))
    rw [abs_of_pos (lt_trans zero_lt_one hβ)]
  have hIio : IntegrableOn (fun β : ℝ => C ^ (2 * s) * |β| ^ (-(2 * (s : ℝ)) / (d : ℝ)))
      (Set.Iio (-1)) volume := by
    have h1 : IntegrableOn (fun β : ℝ => C ^ (2 * s) * |β| ^ (-(2 * (s : ℝ)) / (d : ℝ)))
        (Set.Ioi (-(-1))) volume := by simpa using hIoi
    have h2 := h1.comp_neg_Iio
    exact IntegrableOn.congr_fun h2 (fun x _ => by simp only [abs_neg]) measurableSet_Iio
  refine (hIoi.union hIio).mono_set ?_
  intro β hβ
  have hβ' : 1 < |β| := hβ
  rcases lt_or_ge β 0 with h | h
  · rw [abs_of_neg h] at hβ'
    exact Or.inr (by linarith : β < -1)
  · rw [abs_of_nonneg h] at hβ'
    exact Or.inl hβ'

lemma integrable_min_rpow (C : ℝ) (hC : 0 < C) (d : ℕ) (hd : 1 ≤ d) (N s : ℕ)
    (hs : d < 2 * s) :
    MeasureTheory.Integrable (fun β : ℝ => (min (N : ℝ) (C * |β| ^ (-(1 : ℝ) / (d : ℝ)))) ^ (2 * s)) := by
  show Integrable (ibeta C d N s)
  have hmeas : Measurable (ibeta C d N s) := ibeta_measurable C d N s
  have hae : AEStronglyMeasurable (ibeta C d N s) volume := hmeas.aestronglyMeasurable
  have hAmeas : MeasurableSet {β : ℝ | |β| ≤ 1} :=
    measurableSet_le measurable_abs measurable_const
  have hAvol : volume {β : ℝ | |β| ≤ 1} < ⊤ := by
    have hsub : {β : ℝ | |β| ≤ 1} ⊆ Set.Icc (-1 : ℝ) 1 := fun x hx => abs_le.mp hx
    calc volume {β : ℝ | |β| ≤ 1} ≤ volume (Set.Icc (-1 : ℝ) 1) := measure_mono hsub
      _ = ENNReal.ofReal (1 - (-1)) := Real.volume_Icc
      _ < ⊤ := by simp
  have hAc : IntegrableOn (ibeta C d N s) {β : ℝ | |β| ≤ 1} volume := by
    refine IntegrableOn.of_bound hAvol (hae.mono_measure Measure.restrict_le_self)
      ((N : ℝ) ^ (2 * s)) ?_
    filter_upwards [self_mem_ae_restrict hAmeas] with x _
    exact norm_ibeta_le_const C hC d N s x
  have hBc : IntegrableOn (ibeta C d N s) {β : ℝ | |β| ≤ 1}ᶜ volume := by
    have hset : {β : ℝ | |β| ≤ 1}ᶜ = {β : ℝ | 1 < |β|} := by ext x; simp [not_le]
    have hdom : Integrable (fun β : ℝ => C ^ (2 * s) * |β| ^ (-(2 * (s : ℝ)) / (d : ℝ)))
        (volume.restrict {β : ℝ | |β| ≤ 1}ᶜ) := by
      rw [hset]
      exact integrableOn_decay C d s hd hs
    refine Integrable.mono' hdom (hae.mono_measure Measure.restrict_le_self) ?_
    filter_upwards with x
    exact norm_ibeta_le_decay C hC d hd N s x
  simpa using hAc.union hBc

end Work.A3

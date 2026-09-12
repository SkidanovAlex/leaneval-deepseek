import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.HalflineBound

noncomputable section

open MeasureTheory
open scoped Real ENNReal Topology

namespace Submission.GenericLocalLog

open Filter

/-! # Basic measurability, nonnegativity and tail-containment helpers -/

/-- The log kernel `t ↦ |log |t-c||` is measurable. -/
lemma log_kernel_measurable (c : ℝ) : Measurable (fun t : ℝ => |Real.log (|t - c|)|) := by
  refine (continuous_abs.measurable.comp ?_)
  refine Real.measurable_log.comp ?_
  fun_prop

/-- The set `{t | |t-c| ≤ r}` is measurable. -/
lemma ball_measurableSet (c r : ℝ) : MeasurableSet {t : ℝ | |t - c| ≤ r} := by
  have h : {t : ℝ | |t - c| ≤ r} = (fun t : ℝ => |t - c|) ⁻¹' (Set.Iic r) := by
    ext t; simp
  rw [h]
  exact measurableSet_Iic.preimage (by fun_prop)

/-- Measurability of the truncated log kernel `f`. -/
lemma log_kernel_trunc_measurable (c r : ℝ) :
    Measurable (fun t : ℝ => Set.indicator {t : ℝ | |t - c| ≤ r} (fun t : ℝ => |Real.log (|t - c|)|) t) := by
  exact (log_kernel_measurable c).indicator (ball_measurableSet c r)

/-- Nonnegativity of the truncated log kernel. -/
lemma log_kernel_trunc_nonneg (c r : ℝ) :
    ∀ t : ℝ, 0 ≤ Set.indicator {t : ℝ | |t - c| ≤ r} (fun t : ℝ => |Real.log (|t - c|)|) t := by
  intro t
  by_cases h : t ∈ {t : ℝ | |t - c| ≤ r}
  · simp [Set.indicator, h]
  · simp [Set.indicator, h]

/-- Tail containment: for `0 < r ≤ 1` and `0 < s`, the set where the truncated
log kernel exceeds `s` is contained in the ball of radius `min r (exp(-s))`. -/
lemma tail_subset_ball {c r s : ℝ} (_hr0 : 0 < r) (hr1 : r ≤ 1) (hs0 : 0 < s) :
    {t : ℝ | s < Set.indicator {t : ℝ | |t - c| ≤ r} (fun t : ℝ => |Real.log (|t - c|)|) t}
      ⊆ {t : ℝ | |t - c| ≤ min r (Real.exp (-s))} := by
  intro t ht
  simp only [Set.mem_ofPred_eq] at ht ⊢
  have htA : |t - c| ≤ r := by
    by_contra hnot
    have : Set.indicator {t : ℝ | |t - c| ≤ r} (fun t : ℝ => |Real.log (|t - c|)|) t = 0 := by
      simp [Set.indicator, hnot]
    rw [this] at ht
    linarith
  have hfslog : s < |Real.log (|t - c|)| := by
    have hle : Set.indicator {t : ℝ | |t - c| ≤ r} (fun t : ℝ => |Real.log (|t - c|)|) t
        ≤ |Real.log (|t - c|)| := by
      by_cases h : t ∈ {t : ℝ | |t - c| ≤ r}
      · simp [Set.indicator, h]
      · simp [Set.indicator, h]
    exact lt_of_lt_of_le ht hle
  have hu0 : 0 < |t - c| := by
    by_contra hz
    have hu_eq : |t - c| = 0 := by
      exact le_antisymm (not_lt.mp hz) (abs_nonneg (t - c))
    have hlog0 : |Real.log (|t - c|)| = 0 := by simp [hu_eq]
    linarith
  have hu1 : |t - c| ≤ 1 := le_trans htA hr1
  have hlogu0 : Real.log (|t - c|) ≤ 0 := Real.log_nonpos (le_of_lt hu0) hu1
  have habslog : |Real.log (|t - c|)| = -Real.log (|t - c|) := abs_of_nonpos hlogu0
  have hslt : s < -Real.log (|t - c|) := by
    rw [← habslog]
    exact hfslog
  have hloglt : Real.log (|t - c|) < -s := by linarith
  have hexplt : Real.exp (Real.log (|t - c|)) < Real.exp (-s) := (Real.exp_lt_exp).2 hloglt
  have hlt : |t - c| < Real.exp (-s) := by
    rw [← Real.exp_log hu0]
    exact hexplt
  exact le_min htA (le_of_lt hlt)

/-- Conversion: for nonnegative integrable `g` on `(0,∞)`, the ENNReal lintegral of
`ofReal (g s)` equals `ofReal` of the real integral. -/
lemma lintegral_Ioi_ofReal_eq_ofReal_integral {g : ℝ → ℝ} (hg0 : ∀ s : ℝ, 0 ≤ g s)
    (hgm : Measurable g) (hgint : IntegrableOn g (Set.Ioi 0) volume) :
    (∫⁻ s : ℝ in Set.Ioi 0, ENNReal.ofReal (g s)) =
      ENNReal.ofReal (∫ s : ℝ in Set.Ioi 0, g s) := by
  let μ := (volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))
  have hL : (∫⁻ s : ℝ in Set.Ioi 0, ENNReal.ofReal (g s)) ≠ ∞ := by
    exact ne_of_lt (hgint.integrable.lintegral_lt_top)
  have htoReal : (∫ s : ℝ in Set.Ioi 0, g s) =
      (∫⁻ s : ℝ in Set.Ioi 0, ENNReal.ofReal (g s)).toReal := by
    have hh := MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (μ := μ) (hf := Eventually.of_forall hg0) hgm.aestronglyMeasurable
    simpa [μ] using hh
  rw [htoReal]
  exact (ENNReal.ofReal_toReal hL).symm

/-! # Assembly -/

/-- Mass of the tail set is controlled by the ball-mass assumption. -/
lemma mass_tail_le {μ : Measure ℝ} {C c r s : ℝ} (_hC : 0 ≤ C)
    (hmass : ∀ (c R : ℝ), 0 ≤ R →
      μ {t : ℝ | |t - c| ≤ R} ≤ ENNReal.ofReal (C * Real.sqrt (2 * R)))
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hs0 : 0 < s) :
    μ {t : ℝ | s < Set.indicator {t : ℝ | |t - c| ≤ r} (fun t : ℝ => |Real.log (|t - c|)|) t}
      ≤ ENNReal.ofReal (C * Real.sqrt (2 * min r (Real.exp (-s)))) := by
  have hsub := tail_subset_ball (c := c) (r := r) (s := s) hr0 hr1 hs0
  have hm := measure_mono (μ := μ) hsub
  have hR : 0 ≤ min r (Real.exp (-s)) := le_of_lt (lt_min hr0 (Real.exp_pos (-s)))
  exact le_trans hm (hmass c (min r (Real.exp (-s))) hR)

/-- The scalar inequality `C · 4096 · X ≤ (C+1) · 4096 · X` for `X ≥ 0`. -/
lemma scalar_4096_le {C r : ℝ} (_hC : 0 ≤ C) :
    C * (4096 * Real.sqrt r * (2 + |Real.log r|)) ≤
      (C + 1) * 4096 * (Real.sqrt r * (2 + |Real.log r|)) := by
  have hX : 0 ≤ Real.sqrt r * (2 + |Real.log r|) := by
    exact mul_nonneg (Real.sqrt_nonneg r) (by positivity)
  calc
    C * (4096 * Real.sqrt r * (2 + |Real.log r|))
        = C * 4096 * (Real.sqrt r * (2 + |Real.log r|)) := by ring
    _ ≤ (C + 1) * 4096 * (Real.sqrt r * (2 + |Real.log r|)) := by
      have h1 : C * 4096 ≤ (C + 1) * 4096 := by nlinarith
      exact mul_le_mul_of_nonneg_right h1 hX

/-- ENNReal lintegral over the half-line of the pointwise ball-mass bound. -/
lemma halfline_lintegral_le {C r : ℝ} (hC : 0 ≤ C) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (∫⁻ s : ℝ in Set.Ioi (0 : ℝ), ENNReal.ofReal
        (C * Real.sqrt (2 * min r (Real.exp (-s))))) ≤
      ENNReal.ofReal ((C + 1) * 4096 * (Real.sqrt r * (2 + |Real.log r|))) := by
  let g : ℝ → ℝ := fun s => Real.sqrt (2 * min r (Real.exp (-s)))
  let h : ℝ → ℝ := fun s => C * g s
  have hgmeas : Measurable g := by
    dsimp [g]
    fun_prop
  have hg0 : ∀ s : ℝ, 0 ≤ g s := by
    intro s
    dsimp [g]
    positivity
  have hh0 : ∀ s : ℝ, 0 ≤ h s := by
    intro s
    exact mul_nonneg hC (hg0 s)
  have hhm : Measurable h := by
    dsimp [h]
    exact hgmeas.const_mul C
  have hhint : IntegrableOn h (Set.Ioi 0) volume := by
    dsimp [h]
    exact (Submission.HalflineBound.integrableOn_sqrtmin_Ioi (r := r) hr0).integrable.const_mul C
  have hconv := lintegral_Ioi_ofReal_eq_ofReal_integral (g := h) hh0 hhm hhint
  have hreal : (∫ s : ℝ in Set.Ioi 0, h s) ≤
      C * (4096 * Real.sqrt r * (2 + |Real.log r|)) := by
    have hb := Submission.HalflineBound.halfline_sqrtmin_le (r := r) hr0 hr1
    calc
      (∫ s : ℝ in Set.Ioi 0, h s)
          = C * (∫ s : ℝ in Set.Ioi 0, Real.sqrt (2 * min r (Real.exp (-s)))) := by
        dsimp [h, g]
        rw [MeasureTheory.integral_const_mul]
      _ ≤ C * (4096 * Real.sqrt r * (2 + |Real.log r|)) := by
        exact mul_le_mul_of_nonneg_left hb hC
  rw [hconv]
  exact le_trans (ENNReal.ofReal_le_ofReal hreal) (ENNReal.ofReal_le_ofReal (scalar_4096_le (C := C) (r := r) hC))

/-- The ENNReal version of the main bound (layer-cake / Cavalieri). -/
lemma log_kernel_ennreal_bound {μ : Measure ℝ} {C c r : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ (c R : ℝ), 0 ≤ R →
      μ {t : ℝ | |t - c| ≤ R} ≤ ENNReal.ofReal (C * Real.sqrt (2 * R)))
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (∫⁻ t : ℝ, ENNReal.ofReal
        (Set.indicator {t : ℝ | |t - c| ≤ r} (fun t : ℝ => |Real.log (|t - c|)|) t) ∂μ) ≤
      ENNReal.ofReal ((C + 1) * 4096 * (Real.sqrt r * (2 + |Real.log r|))) := by
  let f : ℝ → ℝ := fun t =>
    Set.indicator {t : ℝ | |t - c| ≤ r} (fun t : ℝ => |Real.log (|t - c|)|) t
  have hfnn : ∀ t, 0 ≤ f t := log_kernel_trunc_nonneg c r
  have hfm : Measurable f := log_kernel_trunc_measurable c r
  have hlc := MeasureTheory.lintegral_eq_lintegral_meas_lt μ
    (f := f) (f_nn := Eventually.of_forall hfnn) (f_mble := hfm.aemeasurable)
  rw [hlc]
  calc
    (∫⁻ s : ℝ in Set.Ioi 0, μ {t : ℝ | s < f t}) ≤
        (∫⁻ s : ℝ in Set.Ioi 0, ENNReal.ofReal
          (C * Real.sqrt (2 * min r (Real.exp (-s))))) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact mass_tail_le (μ := μ) (c := c) (s := s) hC hmass hr0 hr1 (Set.mem_Ioi.mp hs)
    _ ≤ ENNReal.ofReal ((C + 1) * 4096 * (Real.sqrt r * (2 + |Real.log r|))) := by
      exact halfline_lintegral_le (C := C) (r := r) hC hr0 hr1

/-- Generic local log-kernel mass estimate from the ball non-concentration
bound `μ {|t−c| ≤ R} ≤ C·√(2R)`.  (Coefficient `(C+1)·4096` is deliberately
loose.) -/
theorem local_log_bound {μ : Measure ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hmass : ∀ (c R : ℝ), 0 ≤ R →
      μ {t : ℝ | |t - c| ≤ R} ≤ ENNReal.ofReal (C * Real.sqrt (2 * R))) :
    ∀ c : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 →
    (∫ t : ℝ, Set.indicator {t : ℝ | |t - c| ≤ r} (fun t : ℝ => |Real.log (|t - c|)|) t ∂μ)
        ≤ (C + 1) * 4096 * (Real.sqrt r * (2 + |Real.log r|)) := by
  intro c r hr0 hr1
  let f : ℝ → ℝ := fun t =>
    Set.indicator {t : ℝ | |t - c| ≤ r} (fun t : ℝ => |Real.log (|t - c|)|) t
  let B : ℝ := (C + 1) * 4096 * (Real.sqrt r * (2 + |Real.log r|))
  have hfnn : ∀ t : ℝ, 0 ≤ f t := log_kernel_trunc_nonneg c r
  have hfm : Measurable f := log_kernel_trunc_measurable c r
  have hen := log_kernel_ennreal_bound (μ := μ) (C := C) (c := c) (r := r) hC hmass hr0 hr1
  have hB0 : 0 ≤ B := by
    dsimp [B]
    positivity
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (μ := μ) (f := f) (hf := Eventually.of_forall hfnn) hfm.aestronglyMeasurable]
  change (∫⁻ t : ℝ, ENNReal.ofReal (f t) ∂μ).toReal ≤ B
  have hen' : (∫⁻ t : ℝ, ENNReal.ofReal (f t) ∂μ) ≤ ENNReal.ofReal B := by
    simpa [f, B] using hen
  have htr := ENNReal.toReal_mono (a := (∫⁻ t : ℝ, ENNReal.ofReal (f t) ∂μ))
    (b := ENNReal.ofReal B) (ENNReal.ofReal_ne_top (r := B)) hen'
  calc
    (∫⁻ t : ℝ, ENNReal.ofReal (f t) ∂μ).toReal ≤ (ENNReal.ofReal B).toReal := htr
    _ = B := ENNReal.toReal_ofReal hB0

end Submission.GenericLocalLog

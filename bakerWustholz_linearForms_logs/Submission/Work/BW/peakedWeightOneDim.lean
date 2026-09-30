import Mathlib
import Submission.Work.BW.peakSetAeEqIcc
import Submission.Work.BW.integrableStepPeak
import Submission.Work.BW.phiIntegralNonpos

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Peaked weight, one-dimensional form

If `φ` has non-positive integral over every symmetric interval `[-a,a]` (`a ≥ 0`) and
`W` is a non-negative, even, measurable weight which is antitone on `[0,∞)`, then
`∫ φ x * W x ≤ 0`.

The proof decomposes `W = c + U` where `c = sInf (W '' [0,∞))` is the limit of `W` at
`+∞` and `U = W - c ≥ 0` is a "tail-vanishing" weight.  For the tail-vanishing weight we
use the layer-cake identity `U x = ∫ t, 1_{0 < t ≤ U x} dt`, exchange the order of
integration (Fubini/Tonelli) and observe that each slice `{x | t ≤ U x}` is, up to a null
set, a symmetric interval `[-r,r]` on which `φ` has non-positive integral.
-/

namespace Work.BW

open MeasureTheory Set

/-- The tail value `sInf (W '' [0,∞))` of a non-negative, even weight antitone on `[0,∞)`
is non-negative, is a lower bound for `W`, and is approached along `+∞`. -/
lemma sInf_tail_props {W : ℝ → ℝ} (hW_even : ∀ x, W (-x) = W x)
    (hW_anti : AntitoneOn W (Set.Ici 0)) (hW_nn : ∀ x, 0 ≤ W x) :
    0 ≤ sInf (W '' Set.Ici 0) ∧ (∀ x, sInf (W '' Set.Ici 0) ≤ W x) ∧
    (∀ t > 0, ∃ Y, ∀ y, Y ≤ y → W y - sInf (W '' Set.Ici 0) < t) := by
  have hne : (W '' Set.Ici 0).Nonempty := ⟨W 0, ⟨0, Set.mem_Ici.mpr le_rfl, rfl⟩⟩
  have hbdd : BddBelow (W '' Set.Ici 0) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, -, rfl⟩; exact hW_nn y
  have hc_nn : 0 ≤ sInf (W '' Set.Ici 0) := le_csInf hne (by rintro _ ⟨y,-,rfl⟩; exact hW_nn y)
  refine ⟨hc_nn, ?_, ?_⟩
  · intro x
    have hxabs : W |x| = W x := by
      rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, hW_even x]
    have hx : W |x| ∈ W '' Set.Ici 0 := ⟨|x|, Set.mem_Ici.mpr (abs_nonneg x), rfl⟩
    have h2 : sInf (W '' Set.Ici 0) ≤ W |x| := csInf_le hbdd hx
    rwa [hxabs] at h2
  · intro t ht
    have hlt : sInf (W '' Set.Ici 0) < sInf (W '' Set.Ici 0) + t := by linarith
    obtain ⟨w, hw_mem, hw_lt⟩ := (csInf_lt_iff hbdd hne).mp hlt
    obtain ⟨y0, hy0, rfl⟩ := hw_mem
    refine ⟨max y0 0, fun y hy => ?_⟩
    have hy_y0 : y0 ≤ y := le_trans (le_max_left _ _) hy
    have hy_nn : 0 ≤ y := le_trans (le_max_right _ _) hy
    have hmono : W y ≤ W y0 := hW_anti hy0 (Set.mem_Ici.mpr hy_nn) hy_y0
    have : W y < sInf (W '' Set.Ici 0) + t := lt_of_le_of_lt hmono hw_lt
    linarith

/-- For a positive level `t`, the integral of `φ` over the superlevel set `{x | t ≤ U x}`
of an even weight `U` antitone on `[0,∞)` (with `U → 0` at `+∞`) is non-positive, because
that set is a.e. a symmetric interval `[-r,r]`. -/
lemma integral_peakSet_nonpos {φ U : ℝ → ℝ} (hU_even : ∀ x, U (-x) = U x)
    (hU_anti : AntitoneOn U (Set.Ici 0))
    (hU_small : ∀ t > 0, ∃ Y, ∀ y, Y ≤ y → U y < t)
    (hpeak : ∀ a, 0 ≤ a → ∫ x in Set.Icc (-a) a, φ x ≤ 0) {t : ℝ} (ht : 0 < t) :
    ∫ x in {x : ℝ | t ≤ U x}, φ x ≤ 0 := by
  obtain ⟨r, hr, hae⟩ := peakSetAeEqIcc hU_even hU_anti hU_small ht
  rw [setIntegral_congr_set hae]
  exact hpeak r hr

/-- Core case: the weight `U` is non-negative, even, antitone on `[0,∞)` and vanishes at
`+∞`.  Then `∫ φ x * U x ≤ 0`. -/
lemma tail_core {φ U : ℝ → ℝ} (hφ_meas : Measurable φ) (hU_meas : Measurable U)
    (hU_even : ∀ x, U (-x) = U x) (hU_anti : AntitoneOn U (Set.Ici 0))
    (hU_nn : ∀ x, 0 ≤ U x) (hU_small : ∀ t > 0, ∃ Y, ∀ y, Y ≤ y → U y < t)
    (hint : Integrable (fun x => φ x * U x))
    (hpeak : ∀ a, 0 ≤ a → ∫ x in Set.Icc (-a) a, φ x ≤ 0) :
    ∫ x, φ x * U x ≤ 0 := by
  have hprod := integrableStepPeak hφ_meas hU_meas hU_nn hint
  have hpoint : ∀ x, (∫ t, (if 0 < t ∧ t ≤ U x then φ x else (0:ℝ))) = φ x * U x := by
    intro x
    have hfun : (fun t : ℝ => (if 0 < t ∧ t ≤ U x then φ x else (0:ℝ)))
        = (Set.Ioc 0 (U x)).indicator (fun _ => φ x) := by
      funext t; by_cases h : 0 < t ∧ t ≤ U x <;> simp [Set.indicator, h]
    rw [hfun, integral_indicator_const (φ x) measurableSet_Ioc,
        Real.volume_real_Ioc_of_le (hU_nn x), smul_eq_mul]
    ring
  have h1 : (fun x => φ x * U x) =ᵐ[volume]
      (fun x => ∫ t, (if 0 < t ∧ t ≤ U x then φ x else (0:ℝ))) := by
    filter_upwards with x using (hpoint x).symm
  rw [integral_congr_ae h1,
      integral_integral_swap (f := fun x t : ℝ => if 0 < t ∧ t ≤ U x then φ x else (0:ℝ)) hprod]
  apply integral_nonpos
  intro t
  change (∫ x, (if 0 < t ∧ t ≤ U x then φ x else (0:ℝ))) ≤ 0
  by_cases ht : 0 < t
  · have hset : (fun x : ℝ => (if 0 < t ∧ t ≤ U x then φ x else (0:ℝ)))
        = ({x : ℝ | t ≤ U x}).indicator φ := by
      funext x; by_cases hx : t ≤ U x <;> simp [Set.indicator, hx, ht]
    rw [hset, integral_indicator (measurableSet_le measurable_const hU_meas)]
    exact integral_peakSet_nonpos hU_even hU_anti hU_small hpeak ht
  · have hzero : (fun x : ℝ => (if 0 < t ∧ t ≤ U x then φ x else (0:ℝ))) = fun _ => 0 := by
      funext x; simp [ht]
    rw [hzero]; simp

theorem peakedWeightOneDim {φ W : ℝ → ℝ} (hφ_meas : Measurable φ) (hW_meas : Measurable W)
    (hW_even : ∀ x, W (-x) = W x) (hW_anti : AntitoneOn W (Set.Ici 0))
    (hW_nn : ∀ x, 0 ≤ W x) (hint : MeasureTheory.Integrable (fun x => φ x * W x))
    (hpeak : ∀ a, 0 ≤ a → ∫ x in Set.Icc (-a) a, φ x ≤ 0) :
    ∫ x, φ x * W x ≤ 0 := by
  obtain ⟨hc_nn, hW_ge, hW_small⟩ := sInf_tail_props hW_even hW_anti hW_nn
  set c : ℝ := sInf (W '' Set.Ici 0) with hc
  have hU_nn : ∀ x, 0 ≤ W x - c := fun x => sub_nonneg.mpr (hW_ge x)
  have hU_even : ∀ x, W (-x) - c = W x - c := fun x => by rw [hW_even x]
  have hU_anti : AntitoneOn (fun x => W x - c) (Set.Ici 0) :=
    fun a ha b hb hab => sub_le_sub_right (hW_anti ha hb hab) c
  have hU_meas : Measurable (fun x => W x - c) := hW_meas.sub measurable_const
  by_cases hc0 : c = 0
  · have hUI : Integrable (fun x => φ x * (W x - c)) := by
      refine hint.congr ?_
      filter_upwards with x; rw [hc0]; ring
    have hcore := tail_core hφ_meas hU_meas hU_even hU_anti hU_nn hW_small hUI hpeak
    simpa [hc0] using hcore
  · have hcpos : 0 < c := lt_of_le_of_ne hc_nn (Ne.symm hc0)
    -- in this case `W ≥ c > 0`, so `φ` is integrable
    have hint_abs : Integrable (fun x => |φ x| * W x) := by
      refine hint.norm.congr ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hW_nn x)]
    have hbound_int : Integrable (fun x => |φ x| * W x / c) := by
      have hh := hint_abs.mul_const (1/c)
      simpa [div_eq_mul_inv, one_div] using hh
    have hphi_int : Integrable φ := by
      refine Integrable.mono' hbound_int hφ_meas.aestronglyMeasurable ?_
      filter_upwards with x
      rw [Real.norm_eq_abs, le_div_iff₀ hcpos]
      exact mul_le_mul_of_nonneg_left (hW_ge x) (abs_nonneg (φ x))
    have hpeak_inf : ∫ x, φ x ≤ 0 := phiIntegralNonpos hφ_meas hphi_int hpeak
    have h2 : Integrable (fun x => φ x * c) := hphi_int.mul_const c
    have hUI : Integrable (fun x => φ x * (W x - c)) := by
      have h3 : Integrable ((fun x => φ x * W x) - (fun x => φ x * c)) := hint.sub h2
      refine h3.congr ?_
      filter_upwards with x
      simp only [Pi.sub_apply]; ring
    have hcore := tail_core hφ_meas hU_meas hU_even hU_anti hU_nn hW_small hUI hpeak
    calc ∫ x, φ x * W x = ∫ x, (φ x * (W x - c) + φ x * c) := by
          apply integral_congr_ae; filter_upwards with x; ring
      _ = (∫ x, φ x * (W x - c)) + (∫ x, φ x * c) := integral_add hUI h2
      _ ≤ 0 + 0 := add_le_add hcore (by
            have hh : ∫ x, φ x * c = (∫ x, φ x) * c := integral_mul_const c φ
            rw [hh]; exact mul_nonpos_of_nonpos_of_nonneg hpeak_inf hc_nn)
      _ = 0 := by ring

end Work.BW

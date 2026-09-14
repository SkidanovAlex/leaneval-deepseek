import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Commons.Analysis.Calculus

open MeasureTheory Filter
open scoped Topology

theorem deriv_clamped_affine_smul_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (δ : E) (T : ℝ) (hδ : δ ≠ 0) (u : E) :
    (fun t : ℝ => deriv (fun s : ℝ => min 1 (max 0 ((T - s) / ‖δ‖)) • u) t)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) T)]
    (fun t : ℝ => (if t ≤ T - ‖δ‖ then (0:E) else (-(‖δ‖)⁻¹) • u)) := by
  have hc : 0 < ‖δ‖ := norm_pos_iff.mpr hδ
  -- derivative of the affine part `(T - ·)/‖δ‖`
  have hd : ∀ t : ℝ, deriv (fun s : ℝ => (T - s)/‖δ‖) t = -(‖δ‖)⁻¹ := by
    intro t
    have h1 : deriv (fun s : ℝ => T - s) t = -1 := by rw [deriv_const_sub]; simp
    rw [deriv_div_const, h1]
    rw [neg_div, one_div]
  have hderivfun : ∀ t : ℝ,
      deriv (fun s : ℝ => ((T - s)/‖δ‖) • u) t = (-(‖δ‖)⁻¹) • u := by
    intro t
    rw [deriv_smul_const (c := fun s : ℝ => (T - s)/‖δ‖) (x := t) (by fun_prop) u, hd t]
  -- pointwise identification away from the two kinks
  have hgood : ∀ t ∈ Set.Ioc (0:ℝ) T, t ≠ T - ‖δ‖ → t ≠ T →
      deriv (fun s : ℝ => min 1 (max 0 ((T - s) / ‖δ‖)) • u) t
        = (if t ≤ T - ‖δ‖ then (0:E) else (-(‖δ‖)⁻¹) • u) := by
    intro t ht hne1 hne2
    rcases lt_trichotomy t (T - ‖δ‖) with hlt | heq | hgt
    · -- t < T - ‖δ‖ : the clamp is eventually equal to 1
      have hev : ∀ᶠ s in 𝓝 t, min 1 (max 0 ((T - s) / ‖δ‖)) = 1 := by
        have hgt' : (1:ℝ) < (T - t)/‖δ‖ := by rw [lt_div_iff₀ hc]; linarith
        have hne : ∀ᶠ s in 𝓝 t, (T - s)/‖δ‖ ∈ Set.Ioi (1:ℝ) :=
          (by fun_prop : Continuous (fun s : ℝ => (T - s)/‖δ‖)).tendsto t
            |>.eventually (IsOpen.mem_nhds isOpen_Ioi hgt')
        filter_upwards [hne] with s hs
        rw [Set.mem_Ioi] at hs
        rw [min_eq_left (le_trans (le_of_lt hs) (le_max_right 0 _))]
      have hfun : (fun s : ℝ => min 1 (max 0 ((T - s) / ‖δ‖)) • u) =ᶠ[𝓝 t]
          (fun _ => (1:ℝ) • u) := by
        filter_upwards [hev] with s hs
        rw [hs]
      have hz : deriv (fun _ : ℝ => (1:ℝ) • u) t = 0 := deriv_const t ((1:ℝ) • u)
      rw [hfun.deriv_eq, hz, if_pos (le_of_lt hlt)]
    · exact absurd heq hne1
    · -- T - ‖δ‖ < t < T : the clamp is eventually the affine part
      have htT : t < T := lt_of_le_of_ne ht.2 hne2
      have hpos : 0 < T - t := by linarith
      have hltc : T - t < ‖δ‖ := by linarith
      have hev : ∀ᶠ s in 𝓝 t, min 1 (max 0 ((T - s) / ‖δ‖)) = (T - s)/‖δ‖ := by
        have h1 : ∀ᶠ s in 𝓝 t, (0:ℝ) < T - s :=
          (by fun_prop : Continuous (fun s : ℝ => T - s)).tendsto t
            |>.eventually (IsOpen.mem_nhds isOpen_Ioi hpos)
        have h2 : ∀ᶠ s in 𝓝 t, T - s < ‖δ‖ :=
          (by fun_prop : Continuous (fun s : ℝ => T - s)).tendsto t
            |>.eventually (IsOpen.mem_nhds isOpen_Iio hltc)
        filter_upwards [h1, h2] with s hs1 hs2
        rw [max_eq_right (le_of_lt (div_pos hs1 hc)),
            min_eq_right (le_of_lt ((div_lt_one hc).mpr hs2))]
      have hfun : (fun s : ℝ => min 1 (max 0 ((T - s) / ‖δ‖)) • u) =ᶠ[𝓝 t]
          (fun s : ℝ => ((T - s)/‖δ‖) • u) := by
        filter_upwards [hev] with s hs
        rw [hs]
      rw [hfun.deriv_eq, if_neg (not_le.mpr hgt), hderivfun t]
  -- the two kinks form a null set
  have hsub : {t : ℝ | ¬ (t ∈ Set.Ioc (0:ℝ) T →
        deriv (fun s : ℝ => min 1 (max 0 ((T - s) / ‖δ‖)) • u) t
          = (if t ≤ T - ‖δ‖ then (0:E) else (-(‖δ‖)⁻¹) • u))}
      ⊆ ({T - ‖δ‖, T} : Set ℝ) := by
    intro t ht
    obtain ⟨htIoc, hne⟩ := (Classical.not_imp).mp ht
    rcases eq_or_ne t (T - ‖δ‖) with h | h
    · simp [h]
    · rcases eq_or_ne t T with h2 | h2
      · simp [h2]
      · exact absurd (hgood t htIoc h h2) hne
  have hfin : ({T - ‖δ‖, T} : Set ℝ).Finite := Set.toFinite _
  show ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ioc (0:ℝ) T),
    deriv (fun s : ℝ => min 1 (max 0 ((T - s) / ‖δ‖)) • u) t
      = (if t ≤ T - ‖δ‖ then (0:E) else (-(‖δ‖)⁻¹) • u)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc, MeasureTheory.ae_iff]
  exact MeasureTheory.measure_mono_null hsub (hfin.measure_zero volume)

end Commons.Analysis.Calculus
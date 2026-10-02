import Mathlib
import Submission.Work.LandLeaves.sqrtReduction
import Submission.Work.LandLeaves.gronwallDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves.koebeDerivAux

open Complex Metric Set Filter
open scoped Topology

/-- If `F` satisfies the expansion `‖F z - (1/z + a z)‖ ≤ C ‖z‖²` near `0` (for `0 < ‖z‖ < δ`),
then the function `ζ ↦ (if ζ = 0 then 0 else F ζ - ζ⁻¹)` is continuous at `0` with value `0`. -/
lemma tendsto_ite_sub_inv (F : ℂ → ℂ) (a : ℂ) (C δ : ℝ) (hδ : 0 < δ)
    (h : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < δ → ‖F z - (1 / z + a * z)‖ ≤ C * ‖z‖ ^ 2) :
    Tendsto (fun ζ : ℂ => if ζ = 0 then 0 else F ζ - ζ⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
  have hball : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ‖ζ‖ < δ := by
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℂ) hδ)] with ζ hζ
    simpa [Metric.mem_ball, dist_zero_right] using hζ
  have hgbound : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < δ → ‖F ζ - ζ⁻¹ - a * ζ‖ ≤ |C| * ‖ζ‖ ^ 2 := by
    intro ζ h1 h2
    have h' := h ζ h1 h2
    have he : F ζ - ζ⁻¹ - a * ζ = F ζ - (1 / ζ + a * ζ) := by rw [one_div]; ring
    rw [he]
    calc ‖F ζ - (1 / ζ + a * ζ)‖ ≤ C * ‖ζ‖ ^ 2 := h'
      _ ≤ |C| * ‖ζ‖ ^ 2 := by nlinarith [le_abs_self C, sq_nonneg ‖ζ‖]
  have hg0 : Tendsto (fun ζ : ℂ => F ζ - ζ⁻¹ - a * ζ) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (f := fun ζ : ℂ => ‖F ζ - ζ⁻¹ - a * ζ‖)
      (g := fun ζ : ℂ => |C| * ‖ζ‖ ^ 2)
      (Eventually.of_forall fun ζ => norm_nonneg _) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, hball] with ζ hζ hlt
      exact hgbound ζ (norm_pos_iff.mpr (by simpa using hζ)) hlt
    · have hnorm : Tendsto (fun ζ : ℂ => ‖ζ‖) (𝓝[≠] (0:ℂ)) (𝓝 0) := by
        simpa using (continuous_norm.tendsto (0:ℂ)).mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds.mul (hnorm.pow 2))
  have hmain : Tendsto (fun ζ : ℂ => (F ζ - ζ⁻¹ - a * ζ) + a * ζ) (𝓝[≠] (0:ℂ)) (𝓝 0) := by
    have h2 : Tendsto (fun ζ : ℂ => a * ζ) (𝓝[≠] (0:ℂ)) (𝓝 0) := by
      have hid : Tendsto (fun ζ : ℂ => ζ) (𝓝[≠] (0:ℂ)) (𝓝 0) :=
        (Filter.tendsto_id : Tendsto (fun ζ : ℂ => ζ) (𝓝 (0:ℂ)) (𝓝 0)).mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds.mul hid)
    simpa using hg0.add h2
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ζ hζ
  rw [show (if ζ = 0 then (0:ℂ) else F ζ - ζ⁻¹) = F ζ - ζ⁻¹ from ite_eq_right (by simpa using hζ)]
  ring

/-- If `F` satisfies the expansion `‖F z - (1/z + a z)‖ ≤ C ‖z‖²` near `0` (for `0 < ‖z‖ < δ`),
then `ζ ↦ (if ζ = 0 then 0 else F ζ - ζ⁻¹)` is differentiable at `0` with derivative `a`. -/
lemma hasDerivAt_ite_sub_inv (F : ℂ → ℂ) (a : ℂ) (C δ : ℝ) (hδ : 0 < δ)
    (h : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < δ → ‖F z - (1 / z + a * z)‖ ≤ C * ‖z‖ ^ 2) :
    HasDerivAt (fun ζ : ℂ => if ζ = 0 then 0 else F ζ - ζ⁻¹) a 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hball : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ‖ζ‖ < δ := by
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0:ℂ) hδ)] with ζ hζ
    simpa [Metric.mem_ball, dist_zero_right] using hζ
  have hgbound : ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < δ → ‖F ζ - ζ⁻¹ - a * ζ‖ ≤ |C| * ‖ζ‖ ^ 2 := by
    intro ζ h1 h2
    have h' := h ζ h1 h2
    have he : F ζ - ζ⁻¹ - a * ζ = F ζ - (1 / ζ + a * ζ) := by rw [one_div]; ring
    rw [he]
    calc ‖F ζ - (1 / ζ + a * ζ)‖ ≤ C * ‖ζ‖ ^ 2 := h'
      _ ≤ |C| * ‖ζ‖ ^ 2 := by nlinarith [le_abs_self C, sq_nonneg ‖ζ‖]
  have hkey : (fun ζ : ℂ => slope (fun ζ : ℂ => if ζ = 0 then 0 else F ζ - ζ⁻¹) 0 ζ - a)
      =ᶠ[𝓝[≠] (0:ℂ)] (fun ζ : ℂ => ζ⁻¹ * (F ζ - ζ⁻¹ - a * ζ)) := by
    filter_upwards [self_mem_nhdsWithin] with ζ hζ
    have hζ' : ζ ≠ 0 := by simpa using hζ
    rw [slope_def_field]
    rw [show (if (0:ℂ) = 0 then (0:ℂ) else F 0 - 0⁻¹) = 0 from ite_eq_left rfl]
    rw [show (if ζ = 0 then (0:ℂ) else F ζ - ζ⁻¹) = F ζ - ζ⁻¹ from ite_eq_right hζ']
    rw [sub_zero, sub_zero]
    field_simp
  have h0 : Tendsto (fun ζ : ℂ => ζ⁻¹ * (F ζ - ζ⁻¹ - a * ζ)) (𝓝[≠] (0:ℂ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (f := fun ζ : ℂ => ‖ζ⁻¹ * (F ζ - ζ⁻¹ - a * ζ)‖)
      (g := fun ζ : ℂ => |C| * ‖ζ‖) (Eventually.of_forall fun ζ => norm_nonneg _) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, hball] with ζ hζ hlt
      have hζ' : ζ ≠ 0 := by simpa using hζ
      have hpos : 0 < ‖ζ‖ := norm_pos_iff.mpr hζ'
      rw [norm_mul, norm_inv]
      calc ‖ζ‖⁻¹ * ‖F ζ - ζ⁻¹ - a * ζ‖ ≤ ‖ζ‖⁻¹ * (|C| * ‖ζ‖ ^ 2) := by
            gcongr
            exact hgbound ζ hpos hlt
        _ = |C| * ‖ζ‖ := by field_simp
    · have hnorm : Tendsto (fun ζ : ℂ => ‖ζ‖) (𝓝[≠] (0:ℂ)) (𝓝 0) := by
        simpa using (continuous_norm.tendsto (0:ℂ)).mono_left nhdsWithin_le_nhds
      simpa using (tendsto_const_nhds.mul hnorm)
  have h1 : Tendsto (fun ζ : ℂ => slope (fun ζ : ℂ => if ζ = 0 then 0 else F ζ - ζ⁻¹) 0 ζ - a)
      (𝓝[≠] (0:ℂ)) (𝓝 0) := h0.congr' hkey.symm
  have h2 := h1.add (tendsto_const_nhds : Tendsto (fun _ : ℂ => a) (𝓝[≠] (0:ℂ)) (𝓝 a))
  simpa using h2

/-- Instantiation of the exterior setup from a univalent `f` on the unit ball.

Take `F` from `Work.LandLeaves.sqrtReduction` and set `ψ := fun w => F w⁻¹`, which is holomorphic and injective on `‖w‖ > 1` (chain rule with `w ↦ w⁻¹`, and injectivity of the inversion on the exterior). Since `ψ w - w = F (w⁻¹) - (w⁻¹)⁻¹`, the expansion `‖F z - (1/z + a z)‖ ≤ C ‖z‖²` with `z = w⁻¹` (valid for `0 < ‖z‖ < δ`, hence for `‖w‖ > 1/δ`) gives `‖ψ w - w‖ ≤ ‖a‖/‖w‖ + C/‖w‖² ≤ ‖a‖ + C` for `‖w‖ ≥ W := max 2 (1/δ + 1)`.

For the coefficient: `bco ψ 1 = deriv (Fext ψ) 0` and `Fext_eq` gives `Fext ψ ζ = F ζ - ζ⁻¹` for `ζ ≠ 0`; subtracting the expansion, `F ζ - ζ⁻¹ - a ζ = O(‖ζ‖²)`, so the difference quotient tends to `0` and `deriv (Fext ψ) 0 = a = -(iteratedDeriv 2 f 0) / 4`. (Note `Fext ψ 0 = 0`, which follows from the same estimate; `Fext ψ` is holomorphic at `0` because it is bounded there.) -/
lemma bco_one_inst (f : ℂ → ℂ) (hd : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hf : Set.InjOn f (Metric.ball 0 1)) (h0 : f 0 = 0) (h1 : deriv f 0 = 1) :
    ∃ (ψ : ℂ → ℂ) (W C : ℝ), 1 < W ∧
      DifferentiableOn ℂ ψ {w : ℂ | 1 < ‖w‖} ∧
      Set.InjOn ψ {w : ℂ | 1 < ‖w‖} ∧
      (∀ w, W ≤ ‖w‖ → ‖ψ w - w‖ ≤ C) ∧
      bco ψ 1 = -(iteratedDeriv 2 f 0) / 4 := by
  obtain ⟨F, hFdiff, hFinj, C0, δ, hδpos, hexp⟩ := sqrtReduction f hd hf h0 h1
  set a : ℂ := -(iteratedDeriv 2 f 0) / 4 with ha
  have hexpa : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < δ → ‖F z - (1 / z + a * z)‖ ≤ C0 * ‖z‖ ^ 2 := by
    intro z hz0 hzδ
    simpa only [ha] using hexp z hz0 hzδ
  set ψ : ℂ → ℂ := fun w => F w⁻¹ with hψ
  have hmem_iff : ∀ w : ℂ, w ∈ {w : ℂ | 1 < ‖w‖} → w⁻¹ ∈ {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} := by
    intro w hw
    simp only [Set.mem_ofPred_eq] at hw ⊢
    have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; norm_num at hw
    refine ⟨?_, ?_⟩
    · rw [norm_inv]; exact inv_pos.mpr (norm_pos_iff.mpr hw0)
    · rw [norm_inv, inv_lt_one₀ (norm_pos_iff.mpr hw0)]; exact hw
  have hψdiff : DifferentiableOn ℂ ψ {w : ℂ | 1 < ‖w‖} := by
    have h1' : DifferentiableOn ℂ (fun w : ℂ => w⁻¹) {w : ℂ | 1 < ‖w‖} := by
      intro w hw
      simp only [Set.mem_ofPred_eq] at hw
      have hw0 : w ≠ 0 := by intro h; rw [h, norm_zero] at hw; norm_num at hw
      exact (differentiableAt_inv hw0).differentiableWithinAt
    have h3 := DifferentiableOn.comp hFdiff h1' hmem_iff
    rw [hψ]
    simpa [Function.comp_def] using h3
  have hψinj : Set.InjOn ψ {w : ℂ | 1 < ‖w‖} := by
    rw [hψ]
    intro u hu v hv huv
    exact inv_inj.mp (hFinj (hmem_iff u hu) (hmem_iff v hv) huv)
  have hψb : ∀ w : ℂ, max 2 (1 / δ + 1) ≤ ‖w‖ → ‖ψ w - w‖ ≤ |C0| + ‖a‖ := by
    intro w hw
    have hWpos : (0:ℝ) < max 2 (1 / δ + 1) := lt_of_lt_of_le zero_lt_two (le_max_left _ _)
    have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at hw; linarith
    set z : ℂ := w⁻¹ with hz
    have hz0 : 0 < ‖z‖ := by rw [hz, norm_inv]; exact inv_pos.mpr (norm_pos_iff.mpr hw0)
    have hzδ : ‖z‖ < δ := by
      rw [hz, norm_inv]
      have hδ1 : 0 < 1 / δ + 1 := by positivity
      have hle : 1 / δ + 1 ≤ ‖w‖ := le_trans (le_max_right _ _) hw
      have hstep : (1 / δ + 1)⁻¹ < δ := by
        have h2 : 1 < δ * (1 / δ + 1) := by
          have h3 : δ * (1 / δ) = 1 := by field_simp
          nlinarith
        calc (1 / δ + 1)⁻¹ = 1 / (1 / δ + 1) := (one_div _).symm
          _ < δ := by rw [div_lt_iff₀ hδ1]; exact h2
      exact lt_of_le_of_lt (inv_anti₀ hδ1 hle) hstep
    have hz1 : ‖z‖ ≤ 1 := by
      rw [hz, norm_inv]
      exact inv_le_one_of_one_le₀ (by
        have : (2:ℝ) ≤ ‖w‖ := le_trans (le_max_left _ _) hw
        linarith)
    have hexpz := hexpa z hz0 hzδ
    have hwz : w = 1 / z := by rw [hz, one_div, inv_inv]
    have hdecomp : F z - w = (F z - (1 / z + a * z)) + a * z := by rw [hwz]; ring
    have hb1 : C0 * ‖z‖ ^ 2 ≤ |C0| := by
      have hsq1 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z, hz1]
      calc C0 * ‖z‖ ^ 2 ≤ |C0| * ‖z‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (le_abs_self C0) (sq_nonneg _)
        _ ≤ |C0| * 1 := mul_le_mul_of_nonneg_left hsq1 (abs_nonneg C0)
        _ = |C0| := mul_one _
    have hb2 : ‖a‖ * ‖z‖ ≤ ‖a‖ := by
      calc ‖a‖ * ‖z‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hz1 (norm_nonneg a)
        _ = ‖a‖ := mul_one _
    rw [hψ]
    show ‖F w⁻¹ - w‖ ≤ |C0| + ‖a‖
    rw [show F w⁻¹ = F z from by rw [hz], hdecomp]
    calc ‖(F z - (1 / z + a * z)) + a * z‖
        ≤ ‖F z - (1 / z + a * z)‖ + ‖a * z‖ := norm_add_le _ _
      _ ≤ C0 * ‖z‖ ^ 2 + ‖a‖ * ‖z‖ := add_le_add hexpz (le_of_eq (norm_mul a z))
      _ ≤ |C0| + ‖a‖ := by linarith
  refine ⟨ψ, max 2 (1 / δ + 1), |C0| + ‖a‖, ?_, hψdiff, hψinj, hψb, ?_⟩
  · exact lt_of_lt_of_le one_lt_two (le_max_left _ _)
  · have hregPart_eq : Work.LandLeaves.regPart ψ =
        fun ζ : ℂ => if ζ = 0 then 0 else F ζ - ζ⁻¹ := by
      funext ζ
      by_cases hζ : ζ = 0
      · subst hζ; simp [Work.LandLeaves.regPart]
      · simp [Work.LandLeaves.regPart, hψ, hζ]
    have hreglim : Tendsto (Work.LandLeaves.regPart ψ) (𝓝[≠] (0:ℂ)) (𝓝 0) := by
      have h := tendsto_ite_sub_inv F a C0 δ hδpos hexpa
      rw [← hregPart_eq] at h
      exact h
    have hregderiv : HasDerivAt (Work.LandLeaves.regPart ψ) a 0 := by
      have h := hasDerivAt_ite_sub_inv F a C0 δ hδpos hexpa
      rw [← hregPart_eq] at h
      exact h
    have hlimUnder : (𝓝[≠] (0:ℂ)).limUnder (Work.LandLeaves.regPart ψ) = 0 :=
      Tendsto.limUnder_eq hreglim
    have hFext_eq : Work.LandLeaves.Fext ψ = Work.LandLeaves.regPart ψ := by
      funext ζ
      rcases eq_or_ne ζ 0 with rfl | hζ
      · rw [Work.LandLeaves.Fext, Function.update_self, hlimUnder]
        simp [Work.LandLeaves.regPart]
      · rw [Work.LandLeaves.Fext, Function.update_of_ne hζ]
    have hderiv : HasDerivAt (Work.LandLeaves.Fext ψ) a 0 :=
      (Filter.EventuallyEq.hasDerivAt_iff (Filter.EventuallyEq.of_eq hFext_eq)).mpr hregderiv
    have hbco : Work.LandLeaves.bco ψ 1 = a := by
      rw [Work.LandLeaves.bco]
      simp only [Nat.factorial_one, Nat.cast_one, div_one]
      rw [iteratedDeriv_one]
      exact hderiv.deriv
    exact hbco

end Work.LandLeaves.koebeDerivAux

import Mathlib
import Submission.Work.MRMT.Cauchy.integrable_cauchyKernel_of_memLp_lintegral
import Submission.Work.MRMT.Cauchy.lintegral_norm_sub_rpow_neg_ball

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Cauchy

open MeasureTheory

/-- **Hölder continuity of the Cauchy integral of a compactly supported `L^t` function, `t > 2`.**
Put `q = t/(t-1) ∈ (1,2)` and `F z = ∫ w, ν w / (w - z)`.  Assuming `ν` is a.e. strongly
measurable, `∫⁻ ‖ν‖ₑ^t < ⊤`, has compact support, and the two-point kernel bound `hK` holds,
the difference `F z - F z'` is `O(‖z - z'‖^((t-2)/t))`.

Hints: `F z - F z' = (z - z') * ∫ w, ν w / ((w - z) * (w - z'))` — get
`Integrable (fun w => ν w / (w - z))` for every `z` from
`Work.MRMT.Cauchy.integrable_cauchyKernel_of_memLp_lintegral` (with `hsupp` from `hs`) and
`MeasureTheory.integral_sub`.  Then Hölder with conjugate exponents `t` and `q = t/(t-1)`
(`Real.HolderTriple.mk`, `ENNReal.lintegral_mul_le_Lp_mul_Lq`) gives
`∫⁻ w, ‖ν w‖ₑ * ‖(w-z)⁻¹‖ₑ * ‖(w-z')⁻¹‖ₑ ≤ (∫⁻ ‖ν‖ₑ^t)^(1/t) * (∫⁻ ‖w-z‖ₑ^(-q) * ‖w-z'‖ₑ^(-q))^(1/q)`;
the second factor is `≤ ofReal (K^(1/q) * d^(-2/t))` since `(2-2q)/q = -2/t`, hence
`‖F z - F z'‖ ≤ C * d^(1-2/t)` with `C = ((∫⁻ ‖ν‖ₑ^t)^(1/t)).toReal * K^(1/q)` and
`1 - 2/t = (t-2)/t`.  Use `MeasureTheory.enorm_integral_le_lintegral_enorm` and
`MeasureTheory.integral_norm_eq_lintegral_enorm` to move between the Bochner integral and the
`ℝ≥0∞`-integral; `z = z'` is trivial since `0 ^ ((t-2)/t) = 0`. -/
theorem holder_bound_cauchyIntegral {ν : ℂ → ℂ} {t K : ℝ} (ht : 2 < t) (hK0 : 0 ≤ K)
    (hν : MeasureTheory.AEStronglyMeasurable ν (MeasureTheory.volume : MeasureTheory.Measure ℂ))
    (hint : (∫⁻ w : ℂ, ‖ν w‖ₑ ^ t) < ⊤)
    (hs : HasCompactSupport ν)
    (hK : ∀ z z' : ℂ, z ≠ z' →
      (∫⁻ w : ℂ, ‖w - z‖ₑ ^ (-(t / (t - 1))) * ‖w - z'‖ₑ ^ (-(t / (t - 1))))
        ≤ ENNReal.ofReal (K * ‖z - z'‖ ^ (2 - 2 * (t / (t - 1))))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z z' : ℂ,
      ‖(∫ w : ℂ, ν w / (w - z)) - (∫ w : ℂ, ν w / (w - z'))‖
        ≤ C * ‖z - z'‖ ^ ((t - 2) / t) := by
  have ht0 : 0 < t := by linarith
  have htm1 : 0 < t - 1 := by linarith
  let q : ℝ := t / (t - 1)
  have hqeq : q = t / (t - 1) := rfl
  have hq1 : 1 < q := by rw [hqeq, lt_div_iff₀ htm1]; linarith
  have hq2 : q < 2 := by rw [hqeq, div_lt_iff₀ htm1]; linarith
  have hqpos : 0 < q := lt_trans zero_lt_one hq1
  have hqq : q / (q - 1) = t := by rw [hqeq]; field_simp; ring
  have hexp2 : (2 - 2 * q) * (1 / q) = -2 / t := by rw [hqeq]; field_simp; ring
  have hexp3 : (t - 2) / t = 1 + (-2 / t) := by field_simp; ring
  have hconj : Real.HolderConjugate t q := by
    refine Real.HolderTriple.mk ?_ ht0 hqpos
    rw [inv_one, hqeq]; field_simp; ring
  -- extract a ball containing the support of `ν`
  obtain ⟨R₀, hR₀⟩ := hs.isCompact.isBounded.exists_norm_le
  have hsupp : ∀ w : ℂ, R₀ + 1 ≤ ‖w‖ → ν w = 0 := by
    intro w hw
    by_contra hne
    have hmem : w ∈ tsupport ν := subset_tsupport ν (by simpa [Function.mem_support] using hne)
    have := hR₀ w hmem
    linarith
  -- `ν · /(· - z)` is integrable for every `z`
  have hball : ∀ (z : ℂ) (r : ℝ), 0 < r → (∫⁻ w in Metric.ball z r, ‖w - z‖ₑ ^ (-q)) < ⊤ := by
    intro z r hr
    rw [lintegral_norm_sub_rpow_neg_ball z hq1 hq2 hr]
    exact ENNReal.ofReal_lt_top
  have hInt : ∀ z : ℂ, Integrable (fun w : ℂ => ν w / (w - z)) (volume : Measure ℂ) := by
    intro z
    refine integrable_cauchyKernel_of_memLp_lintegral (ν := ν) (R := R₀ + 1)
      (q := q) hq1 hq2 hν ?_ hsupp hball z
    rw [hqq]; exact hint
  have hA' : (∫⁻ w : ℂ, ‖ν w‖ₑ ^ t) ^ (1 / t) < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (by positivity) hint.ne
  have htexp : (t - 2) / t ≠ 0 := div_ne_zero (by linarith) (by linarith)
  have hrearr : ∀ c k d e : ℝ, d * (c * (k * e)) = (c * k) * (d * e) := by
    intro c k d e; ring
  refine ⟨((∫⁻ w : ℂ, ‖ν w‖ₑ ^ t) ^ (1 / t)).toReal * K ^ (1 / q), ?_, ?_⟩
  · exact mul_nonneg ENNReal.toReal_nonneg (Real.rpow_nonneg hK0 _)
  · intro z z'
    by_cases hzz : z = z'
    · subst hzz
      simp [Real.zero_rpow htexp]
    · have hd : 0 < ‖z - z'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzz)
      have hne_z : ∀ᵐ w : ℂ ∂(volume : Measure ℂ), w ≠ z := by
        rw [MeasureTheory.ae_iff]
        simp
      have hne_z' : ∀ᵐ w : ℂ ∂(volume : Measure ℂ), w ≠ z' := by
        rw [MeasureTheory.ae_iff]
        simp
      -- the difference is `(z - z')` times an integral, off the two poles
      have hae : (fun w : ℂ => ν w / (w - z) - ν w / (w - z'))
          =ᵐ[(volume : Measure ℂ)] (fun w : ℂ => (z - z') * (ν w / ((w - z) * (w - z')))) := by
        filter_upwards [hne_z, hne_z'] with w hwz hwz'
        field_simp
        ring
      have hdiff : (∫ w : ℂ, ν w / (w - z)) - (∫ w : ℂ, ν w / (w - z'))
          = (z - z') * ∫ w : ℂ, ν w / ((w - z) * (w - z')) := by
        rw [← MeasureTheory.integral_sub (hInt z) (hInt z'),
          MeasureTheory.integral_congr_ae hae,
          MeasureTheory.integral_const_mul]
      -- pointwise value of the `ℝ≥0∞`-norm of the two-pole kernel
      have hGnorm : ∀ w : ℂ,
          ‖ν w / ((w - z) * (w - z'))‖ₑ = ‖ν w‖ₑ * (‖(w - z)⁻¹‖ₑ * ‖(w - z')⁻¹‖ₑ) := by
        intro w
        rw [div_eq_mul_inv, mul_inv_rev, enorm_mul, enorm_mul]
        ring
      have hBpt : ∀ w : ℂ,
          (‖(w - z)⁻¹‖ₑ * ‖(w - z')⁻¹‖ₑ) ^ q ≤ ‖w - z‖ₑ ^ (-q) * ‖w - z'‖ₑ ^ (-q) := by
        intro w
        rw [ENNReal.mul_rpow_of_nonneg _ _ hqpos.le]
        refine mul_le_mul' ?_ ?_
        · by_cases hw : w - z = 0
          · rw [hw, _root_.inv_zero, enorm_zero, ENNReal.zero_rpow_of_pos hqpos]
            exact bot_le
          · rw [enorm_inv hw, ENNReal.inv_rpow, ENNReal.rpow_neg]
        · by_cases hw : w - z' = 0
          · rw [hw, _root_.inv_zero, enorm_zero, ENNReal.zero_rpow_of_pos hqpos]
            exact bot_le
          · rw [enorm_inv hw, ENNReal.inv_rpow, ENNReal.rpow_neg]
      have hKq : (∫⁻ w : ℂ, ‖w - z‖ₑ ^ (-q) * ‖w - z'‖ₑ ^ (-q))
          ≤ ENNReal.ofReal (K * ‖z - z'‖ ^ (2 - 2 * q)) := by
        simpa only [hqeq] using hK z z' hzz
      have hB : (∫⁻ w : ℂ, (‖(w - z)⁻¹‖ₑ * ‖(w - z')⁻¹‖ₑ) ^ q)
          ≤ ENNReal.ofReal (K * ‖z - z'‖ ^ (2 - 2 * q)) :=
        le_trans (lintegral_mono hBpt) hKq
      have hB' : (∫⁻ w : ℂ, (‖(w - z)⁻¹‖ₑ * ‖(w - z')⁻¹‖ₑ) ^ q) ^ (1 / q)
          ≤ ENNReal.ofReal (K ^ (1 / q) * ‖z - z'‖ ^ (-2 / t)) := by
        refine le_trans (ENNReal.rpow_le_rpow hB (by positivity)) ?_
        rw [ENNReal.ofReal_rpow_of_nonneg (show 0 ≤ K * ‖z - z'‖ ^ (2 - 2 * q) by positivity)
          (by positivity)]
        rw [Real.mul_rpow hK0 (Real.rpow_nonneg hd.le _)]

        rw [← Real.rpow_mul hd.le (2 - 2 * q) (1 / q)]
        rw [hexp2]
      -- Hölder in `t` and `q`
      have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume : Measure ℂ) hconj
          (f := fun w : ℂ => ‖ν w‖ₑ) (g := fun w : ℂ => ‖(w - z)⁻¹‖ₑ * ‖(w - z')⁻¹‖ₑ)
          hν.enorm (by measurability)
      have hGbound : (∫⁻ w : ℂ, ‖ν w / ((w - z) * (w - z'))‖ₑ)
          ≤ (∫⁻ w : ℂ, ‖ν w‖ₑ ^ t) ^ (1 / t)
            * ENNReal.ofReal (K ^ (1 / q) * ‖z - z'‖ ^ (-2 / t)) := by
        rw [lintegral_congr hGnorm]
        exact le_trans hHolder (mul_le_mul_of_nonneg_left hB' bot_le)
      have haesmG : MeasureTheory.AEStronglyMeasurable
          (fun w : ℂ => ν w / ((w - z) * (w - z'))) (volume : Measure ℂ) :=
        hν.mul (by measurability : MeasureTheory.AEStronglyMeasurable
          (fun w : ℂ => ((w - z) * (w - z'))⁻¹) (volume : Measure ℂ))
      have hne_top : (∫⁻ w : ℂ, ‖ν w‖ₑ ^ t) ^ (1 / t)
          * ENNReal.ofReal (K ^ (1 / q) * ‖z - z'‖ ^ (-2 / t)) ≠ ⊤ :=
        (ENNReal.mul_lt_top hA' ENNReal.ofReal_lt_top).ne
      have hIntG : ‖∫ w : ℂ, ν w / ((w - z) * (w - z'))‖
          ≤ ((∫⁻ w : ℂ, ‖ν w‖ₑ ^ t) ^ (1 / t)
            * ENNReal.ofReal (K ^ (1 / q) * ‖z - z'‖ ^ (-2 / t))).toReal := by
        calc ‖∫ w : ℂ, ν w / ((w - z) * (w - z'))‖
            ≤ ∫ w : ℂ, ‖ν w / ((w - z) * (w - z'))‖ :=
              MeasureTheory.norm_integral_le_integral_norm _
          _ = (∫⁻ w : ℂ, ‖ν w / ((w - z) * (w - z'))‖ₑ).toReal :=
              MeasureTheory.integral_norm_eq_lintegral_enorm haesmG
          _ ≤ _ := ENNReal.toReal_mono hne_top hGbound
      have hpow : ‖z - z'‖ * ‖z - z'‖ ^ (-2 / t) = ‖z - z'‖ ^ ((t - 2) / t) := by
        conv_rhs => rw [hexp3]
        rw [Real.rpow_add hd, Real.rpow_one]
      calc ‖(∫ w : ℂ, ν w / (w - z)) - (∫ w : ℂ, ν w / (w - z'))‖
          = ‖(z - z') * ∫ w : ℂ, ν w / ((w - z) * (w - z'))‖ := by rw [hdiff]
        _ = ‖z - z'‖ * ‖∫ w : ℂ, ν w / ((w - z) * (w - z'))‖ := by rw [norm_mul]
        _ ≤ ‖z - z'‖ * ((∫⁻ w : ℂ, ‖ν w‖ₑ ^ t) ^ (1 / t)
              * ENNReal.ofReal (K ^ (1 / q) * ‖z - z'‖ ^ (-2 / t))).toReal :=
            mul_le_mul_of_nonneg_left hIntG (norm_nonneg _)
        _ = ((∫⁻ w : ℂ, ‖ν w‖ₑ ^ t) ^ (1 / t)).toReal * K ^ (1 / q)
              * ‖z - z'‖ ^ ((t - 2) / t) := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hrearr, hpow]

end Work.MRMT.Cauchy

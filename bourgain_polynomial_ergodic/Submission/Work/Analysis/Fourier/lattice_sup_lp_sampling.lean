import Mathlib
import Submission.Commons.Analysis.Fourier.band_limited_reproducing_kernel
import Submission.Commons.Analysis.CalderonZygmund.lacunary_shifted_kernel_sum_le
import Submission.Commons.Analysis.CalderonZygmund.cz_shift
import Submission.Commons.Analysis.Fourier.sampling_reproducing
import Submission.Commons.Analysis.Fourier.schwartz_lattice_sum_bound

open MeasureTheory
open scoped FourierTransform ENNReal BigOperators

set_option maxHeartbeats 1000000

namespace Commons.Analysis.Fourier
noncomputable section

/-- **Weighted Hölder / power-mean inequality** in `ℝ≥0∞`: for `p > 1` and measurable
`f, w : ℝ → ℝ≥0∞`,
`(∫ f w)^p ≤ (∫ w)^{p-1} · ∫ f^p w`. -/
theorem lintegral_mul_rpow_le_rpow_mul_lintegral {p : ℝ} (hp : 1 < p)
    {f w : ℝ → ENNReal} (hf : AEMeasurable f volume) (hw : AEMeasurable w volume) :
    (∫⁻ t, f t * w t) ^ p ≤ (∫⁻ t, w t) ^ (p - 1) * ∫⁻ t, f t ^ p * w t := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  have hpinv : (0:ℝ) < 1 / p := by positivity
  have hqinv : (0:ℝ) < 1 / (p / (p - 1)) := by positivity
  have hinv : (1:ℝ) / p + 1 / (p / (p - 1)) = 1 := by
    simpa only [one_div] using hpq.inv_add_inv_eq_one
  have hp1 : (1:ℝ) / p * p = 1 := by field_simp
  have hsub : (1:ℝ) / (p / (p - 1)) * p = p - 1 := by field_simp
  have h1 : ∀ t : ℝ, f t * w t ^ ((1:ℝ) / p) * w t ^ ((1:ℝ) / (p / (p - 1))) = f t * w t := by
    intro t
    rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg (1 / p) (1 / (p / (p - 1))) hpinv.le hqinv.le,
      hinv, ENNReal.rpow_one]
  have h2 : ∀ t : ℝ, (f t * w t ^ ((1:ℝ) / p)) ^ p = f t ^ p * w t := by
    intro t
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, hp1, ENNReal.rpow_one]
  have h3 : ∀ t : ℝ, (w t ^ ((1:ℝ) / (p / (p - 1)))) ^ (p / (p - 1)) = w t := by
    intro t
    have hx : (1:ℝ) / (p / (p - 1)) * (p / (p - 1)) = 1 := by
      rw [one_div]
      exact inv_mul_cancel₀ (by positivity)
    rw [← ENNReal.rpow_mul, hx, ENNReal.rpow_one]
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq
    (hf.mul (hw.pow_const ((1:ℝ) / p))) (hw.pow_const ((1:ℝ) / (p / (p - 1))))
  simp only [Pi.mul_apply] at hholder
  rw [lintegral_congr (fun t => h1 t), lintegral_congr (fun t => h2 t),
    lintegral_congr (fun t => h3 t)] at hholder
  calc (∫⁻ t, f t * w t) ^ p
      ≤ ((∫⁻ t, f t ^ p * w t) ^ (1 / p) *
            (∫⁻ t, w t) ^ (1 / (p / (p - 1)))) ^ p := ENNReal.rpow_le_rpow hholder hp0.le
    _ = (∫⁻ t, f t ^ p * w t) ^ ((1 / p) * p) *
          (∫⁻ t, w t) ^ ((1 / (p / (p - 1))) * p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.rpow_mul, ENNReal.rpow_mul]
    _ = (∫⁻ t, f t ^ p * w t) * (∫⁻ t, w t) ^ (p - 1) := by
        rw [hp1, hsub, ENNReal.rpow_one]
    _ = (∫⁻ t, w t) ^ (p - 1) * ∫⁻ t, f t ^ p * w t := by ring


private lemma inv_one_add_sq_le (n:ℕ) : (1+(n:ℝ)^2)⁻¹ ≤ 2 * (((n:ℝ)+1)^2)⁻¹ := by
  rw [inv_le_iff_one_le_mul₀ (by positivity : (0:ℝ) < 1 + (n:ℝ)^2)]
  rw [show 2 * (((n:ℝ) + 1)^2)⁻¹ = 2 / ((n:ℝ) + 1)^2 by rw [div_eq_mul_inv]]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < ((n:ℝ)+1)^2)]
  nlinarith [sq_nonneg ((n:ℝ) - 1)]

private lemma summable_nat_inv_one_add_sq : Summable (fun n : ℕ => (1 + (n:ℝ)^2)⁻¹) := by
  have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr one_lt_two
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (h.mul_left 2)
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ) + 1), one_div, Real.rpow_ofNat]
  exact inv_one_add_sq_le n

private lemma summable_int_inv_one_add_sq : Summable (fun m : ℤ => (1 + (m:ℝ)^2)⁻¹) := by
  apply Summable.of_nat_of_neg
  · simpa using summable_nat_inv_one_add_sq
  · simpa using summable_nat_inv_one_add_sq

private noncomputable def phiW : ℤ → ℝ := fun m => (1 + (max (|(m:ℝ)| - 1) 0)^2)⁻¹

private lemma phiW_nn : ∀ m, 0 ≤ phiW m := fun m => by rw [phiW]; positivity

private lemma phiW_dom : ∀ m, phiW m ≤ 4 * (1 + (m:ℝ)^2)⁻¹ := by
  intro m
  rw [phiW]
  set A : ℝ := max (|(m:ℝ)| - 1) 0 with hA
  have hkey : 1 + (m:ℝ)^2 ≤ 4 * (1 + A^2) := by
    rcases lt_or_ge (1:ℝ) (|(m:ℝ)|) with h | h
    · rw [hA, max_eq_left (by linarith)]
      nlinarith [sq_nonneg (m:ℝ), sq_abs (m:ℝ), abs_nonneg (m:ℝ), h]
    · rw [hA, max_eq_right (by linarith)]
      nlinarith [sq_nonneg (|(m:ℝ)| - 1), abs_nonneg (m:ℝ), sq_abs (m:ℝ), h,
        sq_nonneg (|(m:ℝ)| - 4/3)]
  rw [show 4 * (1 + (m:ℝ)^2)⁻¹ = ((1 + (m:ℝ)^2) / 4)⁻¹ by rw [inv_div, div_eq_mul_inv]]
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  nlinarith [hkey]

private lemma phiW_summable : Summable phiW :=
  Summable.of_nonneg_of_le phiW_nn phiW_dom (summable_int_inv_one_add_sq.mul_left 4)

private lemma phiW_pt (t : ℝ) : ∀ m : ℤ, (1 + ((m:ℝ) - t)^2)⁻¹ ≤ phiW (m - ⌊t⌋) := by
  intro m
  set s := t - ⌊t⌋ with hs
  have hs0 : 0 ≤ s := Int.fract_nonneg t
  have hs1 : s < 1 := Int.fract_lt_one t
  have hcast : (m:ℝ) - t = ((m - ⌊t⌋ : ℤ) : ℝ) - s := by rw [hs]; push_cast; ring
  set j : ℝ := ((m - ⌊t⌋ : ℤ) : ℝ) with hj
  have hA : max (|j| - 1) 0 ≤ |j - s| := by
    rcases lt_or_ge (1:ℝ) (|j|) with hgt | hle
    · rw [max_eq_left (by linarith)]
      rcases lt_or_ge j 0 with hjj | hjj
      · rw [abs_of_nonpos hjj.le, abs_of_nonpos (by linarith)]; rw [neg_sub]; linarith
      · rw [abs_of_nonneg hjj]
        have hj1 : 1 < j := by have := hgt; rwa [abs_of_nonneg hjj] at this
        rw [abs_of_nonneg (by linarith)]
        linarith
    · rw [max_eq_right (by linarith)]; positivity
  have hA2 : (max (|j| - 1) 0)^2 ≤ (j - s)^2 := by
    have h0 := le_max_right (|j| - 1) 0
    nlinarith [hA, abs_nonneg (j - s), sq_abs (j - s), h0]
  rw [phiW, hcast]
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  nlinarith [hA2]

private lemma count_weight_le : ∃ B0 : ℝ, 0 < B0 ∧
    ∀ t : ℝ, (∑' m : ℤ, (1 + ((m : ℝ) - t) ^ 2)⁻¹ ≤ B0 ∧
      Summable (fun m : ℤ => (1 + ((m : ℝ) - t) ^ 2)⁻¹)) := by
  refine ⟨∑' m : ℤ, phiW m, ?_, ?_⟩
  · have hφ0 : 0 < phiW 0 := by rw [phiW]; norm_num
    exact lt_of_lt_of_le hφ0 (phiW_summable.le_tsum 0 (fun j hj => phiW_nn j))
  · intro t
    have hg : Summable (fun m : ℤ => phiW (m - ⌊t⌋)) :=
      phiW_summable.comp_injective (fun a b h => by omega)
    have hf : Summable (fun m : ℤ => (1 + ((m:ℝ) - t)^2)⁻¹) :=
      Summable.of_nonneg_of_le (fun m => by positivity) (fun m => phiW_pt t m) hg
    refine ⟨?_, hf⟩
    calc ∑' m : ℤ, (1 + ((m:ℝ) - t)^2)⁻¹ ≤ ∑' m : ℤ, phiW (m - ⌊t⌋) :=
          Summable.tsum_le_tsum (fun m => phiW_pt t m) hf hg
      _ = ∑' j : ℤ, phiW j := Equiv.tsum_eq (Equiv.addRight (-⌊t⌋)) phiW




/-- **`ℓ^p`-version of the lattice sup-sampling inequality.** For `p > 1` and a family
`h : ℕ → ℝ → ℂ` of continuous integrable functions whose Fourier transforms are supported in
`[-1/2, 1/2]`, the `ℓ^p(ℤ)` norm of the lattice values of the pointwise supremum
`x ↦ sup_j ‖h j x‖` is controlled by the `L^p(ℝ)` norm of that supremum. -/
theorem lattice_sup_le_integral_sup_band_limited_rpow {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℕ → ℝ → ℂ),
      (∀ j : ℕ, Integrable (h j)) →
      (∀ j : ℕ, Continuous (h j)) →
      (∀ (j : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2) → 𝓕 (h j) ξ = 0) →
      ∫⁻ m : ℤ, (⨆ j : ℕ, ‖h j (m : ℝ)‖ₑ) ^ p ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C *
            ∫⁻ x : ℝ, (⨆ j : ℕ, ‖h j x‖ₑ) ^ p ∂volume := by
  obtain ⟨K, hKint, ⟨C0, hC0pos, hKdec⟩, hrep⟩ := band_limited_reproducing_kernel
  obtain ⟨B0, hB0pos, hB0⟩ := count_weight_le
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1 : (0:ℝ) ≤ p - 1 := by linarith
  -- the total mass of the reproducing kernel
  set W : ENNReal := ∫⁻ s : ℝ, ‖K s‖ₑ with hWdef
  have hnormK : ∀ z : ℂ, ‖z‖ₑ = ENNReal.ofReal ‖z‖ := fun z => by simp
  have hW4 : W ≤ ENNReal.ofReal (C0 * 4) := by
    have h1 : W ≤ ∫⁻ s : ℝ, ENNReal.ofReal (C0 * (1 + s ^ 2)⁻¹) := by
      rw [hWdef]
      apply lintegral_mono
      intro s
      calc ‖K s‖ₑ = ENNReal.ofReal ‖K s‖ := hnormK _
        _ ≤ ENNReal.ofReal (C0 * (1 + s ^ 2)⁻¹) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have h := hKdec s
            rwa [div_eq_mul_inv] at h
    have hint1 : Integrable (fun s : ℝ => C0 * (1 + s ^ 2)⁻¹) volume := by
      have h := (Commons.Analysis.CalderonZygmund.integrable_inv_one_add_sq_affine 1 0
        (by norm_num)).const_mul C0
      refine h.congr (Filter.Eventually.of_forall fun x => ?_)
      simp
    have h2 : (∫⁻ s : ℝ, ENNReal.ofReal (C0 * (1 + s ^ 2)⁻¹))
        = ENNReal.ofReal (∫ s : ℝ, C0 * (1 + s ^ 2)⁻¹) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint1
        (Filter.Eventually.of_forall (fun x => by positivity))).symm
    rw [h2] at h1
    refine le_trans h1 (ENNReal.ofReal_le_ofReal ?_)
    rw [integral_const_mul]
    have h4 := Commons.Analysis.CalderonZygmund.integral_inv_one_add_sq_le_four
    nlinarith [h4, hC0pos]
  have hWtop : W ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hW4
  have hWx : ∀ x : ℝ, (∫⁻ t : ℝ, ‖K (x - t)‖ₑ) = W := by
    intro x
    rw [hWdef]
    have hA : (∫⁻ t : ℝ, ‖K (x - t)‖ₑ) = ∫⁻ t : ℝ, ‖K (-t + x)‖ₑ := by
      apply lintegral_congr; intro t; rw [show -t + x = x - t by ring]
    have hB : (∫⁻ t : ℝ, ‖K (-t + x)‖ₑ) = ∫⁻ t : ℝ, ‖K (t + x)‖ₑ :=
      lintegral_neg_eq_self (fun u : ℝ => ‖K (u + x)‖ₑ)
    have hC : (∫⁻ t : ℝ, ‖K (t + x)‖ₑ) = ∫⁻ t : ℝ, ‖K (x + t)‖ₑ := by
      apply lintegral_congr; intro t; rw [add_comm]
    rw [hA, hB, hC]
    exact lintegral_add_left_eq_self (fun u : ℝ => ‖K u‖ₑ) x
  -- the lattice sum of the kernel
  have hwB : ∀ t : ℝ, (∑' m : ℤ, ‖K ((m : ℝ) - t)‖ₑ) ≤ ENNReal.ofReal (C0 * B0) := by
    intro t
    have hs : Summable (fun m : ℤ => C0 * (1 + ((m : ℝ) - t) ^ 2)⁻¹) :=
      (hB0 t).2.mul_left C0
    have h1 : (∑' m : ℤ, ‖K ((m : ℝ) - t)‖ₑ)
        ≤ ∑' m : ℤ, ENNReal.ofReal (C0 * (1 + ((m : ℝ) - t) ^ 2)⁻¹) := by
      apply ENNReal.tsum_le_tsum
      intro m
      calc ‖K ((m : ℝ) - t)‖ₑ = ENNReal.ofReal ‖K ((m : ℝ) - t)‖ := hnormK _
        _ ≤ ENNReal.ofReal (C0 * (1 + ((m : ℝ) - t) ^ 2)⁻¹) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have h := hKdec ((m : ℝ) - t)
            rwa [div_eq_mul_inv] at h
    have h2 : (∑' m : ℤ, ENNReal.ofReal (C0 * (1 + ((m : ℝ) - t) ^ 2)⁻¹))
        = ENNReal.ofReal (∑' m : ℤ, C0 * (1 + ((m : ℝ) - t) ^ 2)⁻¹) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hs).symm
    have h3 : (∑' m : ℤ, C0 * (1 + ((m : ℝ) - t) ^ 2)⁻¹)
        = C0 * (∑' m : ℤ, (1 + ((m : ℝ) - t) ^ 2)⁻¹) :=
      Summable.tsum_mul_left C0 (hB0 t).2
    refine le_trans h1 ?_
    rw [h2, h3]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hB0 t).1 hC0pos.le)
  -- the main argument
  refine ⟨(C0 * 4) ^ (p - 1) * (C0 * B0), by positivity, ?_⟩
  intro h hint hcont hbl
  set G : ℝ → ENNReal := fun x => ⨆ j : ℕ, ‖h j x‖ₑ with hG
  have hGmeas : AEMeasurable G volume := by
    rw [hG]
    exact AEMeasurable.iSup (fun j => (hcont j).aemeasurable.enorm)
  have hwmeas : ∀ x : ℝ, AEMeasurable (fun t : ℝ => ‖K (x - t)‖ₑ) volume := by
    intro x
    exact (AEMeasurable.comp_measurable (f := fun t : ℝ => x - t) (g := K)
      (by rw [MeasureTheory.Measure.map_sub_left_eq_self]; exact hKint.aemeasurable)
      (measurable_const.sub measurable_id)).enorm
  have hpointwise : ∀ x : ℝ, G x ≤ ∫⁻ t : ℝ, G t * ‖K (x - t)‖ₑ := by
    intro x
    refine iSup_le (fun j => ?_)
    have hx : h j x = ∫ y, h j y * K (x - y) := hrep (h j) (hint j) (hbl j) x (hcont j).continuousAt
    calc ‖h j x‖ₑ = ‖∫ y, h j y * K (x - y)‖ₑ := by rw [hx]
      _ ≤ ∫⁻ y, ‖h j y * K (x - y)‖ₑ := enorm_integral_le_lintegral_enorm _
      _ = ∫⁻ y, ‖h j y‖ₑ * ‖K (x - y)‖ₑ := by
            refine lintegral_congr (fun y => ?_); rw [enorm_mul]
      _ ≤ ∫⁻ y, G y * ‖K (x - y)‖ₑ := by
            refine lintegral_mono (fun y => ?_)
            exact mul_le_mul_of_nonneg_right (le_iSup (fun j => ‖h j y‖ₑ) j) bot_le
  calc ∫⁻ m : ℤ, (⨆ j : ℕ, ‖h j ((m : ℤ) : ℝ)‖ₑ) ^ p ∂MeasureTheory.Measure.count
      = ∑' m : ℤ, G (m : ℝ) ^ p := by
        rw [lintegral_count]
    _ ≤ ∑' m : ℤ, (∫⁻ t : ℝ, G t * ‖K ((m : ℝ) - t)‖ₑ) ^ p :=
        ENNReal.tsum_le_tsum (fun m => ENNReal.rpow_le_rpow (hpointwise _) hp0.le)
    _ ≤ ∑' m : ℤ, W ^ (p - 1) * ∫⁻ t : ℝ, G t ^ p * ‖K ((m : ℝ) - t)‖ₑ := by
        apply ENNReal.tsum_le_tsum; intro m
        have h := lintegral_mul_rpow_le_rpow_mul_lintegral hp hGmeas (hwmeas (m : ℝ))
        rwa [hWx (m : ℝ)] at h
    _ = W ^ (p - 1) * ∑' m : ℤ, ∫⁻ t : ℝ, G t ^ p * ‖K ((m : ℝ) - t)‖ₑ :=
        ENNReal.tsum_mul_left
    _ = W ^ (p - 1) * ∫⁻ t : ℝ, ∑' m : ℤ, G t ^ p * ‖K ((m : ℝ) - t)‖ₑ := by
        rw [← lintegral_tsum]
        intro m
        exact (hGmeas.pow_const p).mul (hwmeas (m : ℝ))
    _ = W ^ (p - 1) * ∫⁻ t : ℝ, G t ^ p * (∑' m : ℤ, ‖K ((m : ℝ) - t)‖ₑ) := by
        congr 1
        apply lintegral_congr; intro t
        rw [ENNReal.tsum_mul_left]
    _ ≤ W ^ (p - 1) * ∫⁻ t : ℝ, G t ^ p * ENNReal.ofReal (C0 * B0) := by
        apply mul_le_mul_of_nonneg_left _ bot_le
        apply lintegral_mono; intro t
        exact mul_le_mul_of_nonneg_left (hwB t) bot_le
    _ = W ^ (p - 1) * (ENNReal.ofReal (C0 * B0) * ∫⁻ t : ℝ, G t ^ p) := by
        rw [lintegral_mul_const'' _ (hGmeas.pow_const p), mul_comm (∫⁻ t : ℝ, G t ^ p) _]
    _ ≤ ENNReal.ofReal ((C0 * 4) ^ (p - 1)) * ENNReal.ofReal (C0 * B0) *
          ∫⁻ t : ℝ, G t ^ p := by
        have hle : W ^ (p - 1) ≤ ENNReal.ofReal ((C0 * 4) ^ (p - 1)) := by
          rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity : (0:ℝ) ≤ C0 * 4) hp1]
          exact ENNReal.rpow_le_rpow hW4 hp1
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle bot_le) bot_le
    _ = ENNReal.ofReal ((C0 * 4) ^ (p - 1) * (C0 * B0)) * ∫⁻ t : ℝ, G t ^ p := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]

/-- Weighted Hölder / power-mean inequality for a general measure. -/
theorem lintegral_mul_rpow_le_rpow_mul_lintegral_measure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {p : ℝ} (hp : 1 < p)
    {f w : α → ENNReal} (hf : AEMeasurable f μ) (hw : AEMeasurable w μ) :
    (∫⁻ t, f t * w t ∂μ) ^ p ≤ (∫⁻ t, w t ∂μ) ^ (p - 1) * ∫⁻ t, f t ^ p * w t ∂μ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hpq : p.HolderConjugate (p / (p - 1)) := Real.HolderConjugate.conjExponent hp
  have hpinv : (0:ℝ) < 1 / p := by positivity
  have hqinv : (0:ℝ) < 1 / (p / (p - 1)) := by positivity
  have hinv : (1:ℝ) / p + 1 / (p / (p - 1)) = 1 := by
    simpa only [one_div] using hpq.inv_add_inv_eq_one
  have hp1 : (1:ℝ) / p * p = 1 := by field_simp
  have hsub : (1:ℝ) / (p / (p - 1)) * p = p - 1 := by field_simp
  have h1 : ∀ t : α, f t * w t ^ ((1:ℝ) / p) * w t ^ ((1:ℝ) / (p / (p - 1))) = f t * w t := by
    intro t
    rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg (1 / p) (1 / (p / (p - 1))) hpinv.le hqinv.le,
      hinv, ENNReal.rpow_one]
  have h2 : ∀ t : α, (f t * w t ^ ((1:ℝ) / p)) ^ p = f t ^ p * w t := by
    intro t
    rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ← ENNReal.rpow_mul, hp1, ENNReal.rpow_one]
  have h3 : ∀ t : α, (w t ^ ((1:ℝ) / (p / (p - 1)))) ^ (p / (p - 1)) = w t := by
    intro t
    have hx : (1:ℝ) / (p / (p - 1)) * (p / (p - 1)) = 1 := by
      rw [one_div]
      exact inv_mul_cancel₀ (by positivity)
    rw [← ENNReal.rpow_mul, hx, ENNReal.rpow_one]
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq
    (hf.mul (hw.pow_const ((1:ℝ) / p))) (hw.pow_const ((1:ℝ) / (p / (p - 1))))
  simp only [Pi.mul_apply] at hholder
  rw [lintegral_congr (fun t => h1 t), lintegral_congr (fun t => h2 t),
    lintegral_congr (fun t => h3 t)] at hholder
  calc (∫⁻ t, f t * w t ∂μ) ^ p
      ≤ ((∫⁻ t, f t ^ p * w t ∂μ) ^ (1 / p) *
            (∫⁻ t, w t ∂μ) ^ (1 / (p / (p - 1)))) ^ p := ENNReal.rpow_le_rpow hholder hp0.le
    _ = (∫⁻ t, f t ^ p * w t ∂μ) ^ ((1 / p) * p) *
          (∫⁻ t, w t ∂μ) ^ ((1 / (p / (p - 1))) * p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.rpow_mul, ENNReal.rpow_mul]
    _ = (∫⁻ t, f t ^ p * w t ∂μ) * (∫⁻ t, w t ∂μ) ^ (p - 1) := by
        rw [hp1, hsub, ENNReal.rpow_one]
    _ = (∫⁻ t, w t ∂μ) ^ (p - 1) * ∫⁻ t, f t ^ p * w t ∂μ := by ring

/-- Schwartz functions decay like `(1 + x ^ 2)⁻¹`. -/
theorem schwartz_decay_one_add_sq (φ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖φ x‖ ≤ C / (1 + x ^ 2) := by
  set S0 : ℝ := SchwartzMap.seminorm ℂ 0 0 φ with hS0
  set S2 : ℝ := SchwartzMap.seminorm ℂ 2 0 φ with hS2
  refine ⟨max (S0 + S2) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  have h0 : ‖φ x‖ ≤ S0 := SchwartzMap.norm_le_seminorm ℂ φ x
  have h2 : ‖x‖ ^ 2 * ‖φ x‖ ≤ S2 := SchwartzMap.norm_pow_mul_le_seminorm ℂ φ 2 x
  have hx2 : ‖x‖ ^ 2 = x ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  rw [hx2] at h2
  have hsum : (1 + x^2) * ‖φ x‖ ≤ S0 + S2 := by nlinarith [h0, h2]
  have hle : ‖φ x‖ ≤ max (S0 + S2) 1 / (1 + x^2) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hsum, le_max_left (S0+S2) 1, le_max_right (S0+S2) 1]
  simpa only [div_eq_mul_inv] using hle

/-- **Converse lattice sup-sampling inequality** (the reverse direction of Bourgain's (7.5)):
the `L^p(ℝ)` norm of the pointwise supremum of a family of `[-c₀,c₀]`-band-limited Schwartz
functions is controlled by the `ℓ^p(ℤ)` norm of the supremum of their lattice values,
`∫_ℝ (sup_j ‖h_j‖)^p ≤ C · Σ_{m∈ℤ} (sup_j ‖h_j(m)‖)^p`. -/
theorem integral_sup_rpow_le_lattice_tsum_rpow {p : ℝ} (hp : 1 < p)
    (c0 : ℝ) (hc0 : 0 < c0) (hc0' : c0 < 1 / 2) (ψ : SchwartzMap ℝ ℂ)
    (hψ1 : ∀ ξ ∈ Set.Icc (-c0) c0, FourierTransform.fourier ψ ξ = 1)
    (hψs : ∀ ξ : ℝ, ξ ∉ Set.Icc (-(1/2:ℝ)) (1/2) → FourierTransform.fourier ψ ξ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℕ → SchwartzMap ℝ ℂ),
      (∀ (j : ℕ) (ξ : ℝ), ξ ∉ Set.Icc (-c0) c0 → FourierTransform.fourier (h j) ξ = 0) →
      ∫⁻ x : ℝ, (⨆ j : ℕ, ‖(h j : ℝ → ℂ) x‖ₑ) ^ p ∂volume
        ≤ ENNReal.ofReal C *
            ∑' m : ℤ, (⨆ j : ℕ, ‖(h j : ℝ → ℂ) ((m : ℤ) : ℝ)‖ₑ) ^ p := by
  obtain ⟨A, hApos, hAbound⟩ := schwartz_lattice_sum_bound ψ
  obtain ⟨Cψ, hCψpos, hCψ⟩ := schwartz_decay_one_add_sq ψ
  have hnorm : ∀ z : ℂ, ‖z‖ₑ = ENNReal.ofReal ‖z‖ := fun z => by simp
  have hp1 : (0:ℝ) ≤ p - 1 := by linarith
  -- summability of the sampled Schwarz decay
  have hsumψ : ∀ y : ℝ, Summable (fun n : ℤ => ‖ψ (y - (n : ℝ))‖) := by
    intro y
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((count_weight_le.choose_spec.2 y).2.mul_left Cψ)
    have h := hCψ (y - (n : ℝ))
    rw [div_eq_mul_inv] at h
    have hsq : (y - (n : ℝ)) ^ 2 = ((n : ℝ) - y) ^ 2 := by ring_nf
    rwa [hsq] at h
  have hWt : ∀ y : ℝ, (∑' n : ℤ, ‖ψ (y - (n : ℝ))‖ₑ) ≤ ENNReal.ofReal A := by
    intro y
    rw [show (∑' n : ℤ, ‖ψ (y - (n : ℝ))‖ₑ)
          = ∑' n : ℤ, ENNReal.ofReal ‖ψ (y - (n : ℝ))‖ from tsum_congr (fun n => hnorm _),
      ← ENNReal.ofReal_tsum_of_nonneg (fun n => norm_nonneg _) (hsumψ y)]
    exact ENNReal.ofReal_le_ofReal (hAbound y)
  set W : ENNReal := ∫⁻ x : ℝ, ‖ψ x‖ₑ with hWdef
  have hW_eq : W = ENNReal.ofReal (∫ x : ℝ, ‖ψ x‖) := by
    rw [hWdef, show (fun x : ℝ => ‖ψ x‖ₑ) = fun x => ENNReal.ofReal ‖ψ x‖ from
        funext (fun x => hnorm _),
      ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal ψ.integrable.norm
        (Filter.Eventually.of_forall (fun x => norm_nonneg _))]
  have hWx : ∀ m : ℤ, (∫⁻ x : ℝ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) = W := by
    intro m
    rw [hWdef]
    exact lintegral_sub_right_eq_self (fun y : ℝ => ‖ψ y‖ₑ) ((m : ℤ) : ℝ)
  refine ⟨A ^ (p - 1) * (∫ x : ℝ, ‖ψ x‖) + 1, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ A ^ (p - 1) := Real.rpow_nonneg hApos.le _
    have h2 : (0:ℝ) ≤ ∫ x : ℝ, ‖ψ x‖ := integral_nonneg (fun x => norm_nonneg _)
    have h3 : (0:ℝ) ≤ A ^ (p - 1) * (∫ x : ℝ, ‖ψ x‖) := mul_nonneg h1 h2
    linarith
  intro h hband
  set G : ℝ → ENNReal := fun x => ⨆ j : ℕ, ‖(h j : ℝ → ℂ) x‖ₑ with hGm
  have hGmeas : AEMeasurable G volume := by
    rw [hGm]
    exact AEMeasurable.iSup (fun j => (h j).continuous.aemeasurable.enorm)
  -- the sampling identity bounds the sup pointwise by a lattice sum
  have hsample : ∀ x : ℝ, G x ≤ ∑' m : ℤ, G ((m : ℤ) : ℝ) * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ := by
    intro x
    refine iSup_le (fun j => ?_)
    have hsp : (h j : ℝ → ℂ) x
        = ∑' m : ℤ, ψ (x - ((m : ℤ) : ℝ)) * (h j : ℝ → ℂ) ((m : ℤ) : ℝ) :=
      sampling_reproducing c0 hc0 hc0' ψ (h j) hψ1 hψs (hband j) x
    calc ‖(h j : ℝ → ℂ) x‖ₑ
        = ‖∑' m : ℤ, ψ (x - ((m : ℤ) : ℝ)) * (h j : ℝ → ℂ) ((m : ℤ) : ℝ)‖ₑ := by rw [hsp]
      _ ≤ ∑' m : ℤ, ‖ψ (x - ((m : ℤ) : ℝ)) * (h j : ℝ → ℂ) ((m : ℤ) : ℝ)‖ₑ :=
            enorm_tsum_le_tsum_enorm
      _ = ∑' m : ℤ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ * ‖(h j : ℝ → ℂ) ((m : ℤ) : ℝ)‖ₑ := by
            apply tsum_congr; intro m; rw [enorm_mul]
      _ ≤ ∑' m : ℤ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ * G ((m : ℤ) : ℝ) := by
            apply ENNReal.tsum_le_tsum; intro m
            exact mul_le_mul_of_nonneg_left
              (le_iSup (fun j => ‖(h j : ℝ → ℂ) ((m : ℤ) : ℝ)‖ₑ) j) bot_le
      _ = ∑' m : ℤ, G ((m : ℤ) : ℝ) * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ := by
            apply tsum_congr; intro m; rw [mul_comm]
  have hmain : ∀ x : ℝ, G x ^ p
      ≤ (∑' m : ℤ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) ^ (p - 1) *
          ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ := by
    intro x
    have hf : AEMeasurable (fun m : ℤ => G ((m : ℤ) : ℝ)) (Measure.count : Measure ℤ) :=
      (measurable_of_countable _).aemeasurable
    have hw : AEMeasurable (fun m : ℤ => ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) (Measure.count : Measure ℤ) :=
      (measurable_of_countable _).aemeasurable
    have h1 := lintegral_mul_rpow_le_rpow_mul_lintegral_measure (Measure.count : Measure ℤ) hp hf hw
    rw [lintegral_count, lintegral_count, lintegral_count] at h1
    exact (ENNReal.rpow_le_rpow (hsample x) (by linarith : (0:ℝ) ≤ p)).trans h1
  have hstep1 : ∫⁻ x : ℝ, G x ^ p ∂volume
      ≤ ∫⁻ x : ℝ, (∑' m : ℤ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) ^ (p - 1) *
          ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ ∂volume :=
    lintegral_mono hmain
  have hstep2 : ∫⁻ x : ℝ, (∑' m : ℤ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) ^ (p - 1) *
        ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ ∂volume
      ≤ ∫⁻ x : ℝ, ENNReal.ofReal A ^ (p - 1) *
          ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ ∂volume := by
    apply lintegral_mono; intro x
    exact mul_le_mul_of_nonneg_right (ENNReal.rpow_le_rpow (hWt x) hp1) bot_le
  have hmeasc : ∀ m : ℤ, AEMeasurable
      (fun x : ℝ => G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) volume := by
    intro m
    have h2 : AEMeasurable (fun x : ℝ => ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ) volume :=
      (((ψ.continuous.comp (continuous_id.sub continuous_const)).measurable).enorm).aemeasurable
    exact aemeasurable_const.mul h2
  calc ∫⁻ x : ℝ, G x ^ p ∂volume
      ≤ ∫⁻ x : ℝ, ENNReal.ofReal A ^ (p - 1) *
          ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ ∂volume :=
        hstep1.trans hstep2
    _ = ENNReal.ofReal A ^ (p - 1) *
          ∫⁻ x : ℝ, ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ ∂volume := by
        rw [lintegral_const_mul'' _ (AEMeasurable.tsum hmeasc)]
    _ = ENNReal.ofReal A ^ (p - 1) *
          ∑' m : ℤ, ∫⁻ x : ℝ, G ((m : ℤ) : ℝ) ^ p * ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ ∂volume := by
        rw [lintegral_tsum hmeasc]
    _ = ENNReal.ofReal A ^ (p - 1) *
          ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * ∫⁻ x : ℝ, ‖ψ (x - ((m : ℤ) : ℝ))‖ₑ ∂volume := by
        congr 1
        apply tsum_congr; intro m
        exact lintegral_const_mul'' _ (by
          exact (((ψ.continuous.comp (continuous_id.sub continuous_const)).measurable).enorm).aemeasurable)
    _ = ENNReal.ofReal A ^ (p - 1) * ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p * W := by
        congr 1
        apply tsum_congr; intro m
        rw [hWx m]
    _ = ENNReal.ofReal A ^ (p - 1) * (W * ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p) := by
        congr 1
        rw [ENNReal.tsum_mul_right, mul_comm]
    _ = ENNReal.ofReal A ^ (p - 1) * W * ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p := by rw [mul_assoc]
    _ = ENNReal.ofReal (A ^ (p - 1) * (∫ x : ℝ, ‖ψ x‖)) *
          ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p := by
        rw [hW_eq, ENNReal.ofReal_rpow_of_nonneg hApos.le hp1,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hApos.le _)]
    _ ≤ ENNReal.ofReal (A ^ (p - 1) * (∫ x : ℝ, ‖ψ x‖) + 1) *
          ∑' m : ℤ, G ((m : ℤ) : ℝ) ^ p := by
        apply mul_le_mul_of_nonneg_right _ bot_le
        exact ENNReal.ofReal_le_ofReal (by linarith)

end
end Commons.Analysis.Fourier

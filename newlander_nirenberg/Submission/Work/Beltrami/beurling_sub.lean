import Mathlib
import Submission.Work.Beltrami.Cauchy

namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff
open Work.Beltrami

noncomputable section

set_option linter.style.haveILetI false

/-- Cast of the cutoff to `ℂ` is measurable. -/
private lemma measurable_bumpC : Measurable (fun w : ℂ => (bumpC w : ℂ)) :=
  (Complex.continuous_ofReal.comp bumpC_contDiff.continuous).measurable

/-- **Integrability of the Beurling integrand.**  If `h` is bounded by `M`, `α`-Hölder
with `0 < α < 1`, and supported in the disc of radius `R`, then for every `z` the function
`ζ ↦ (h ζ - χ(ζ - z) h z) (ζ - z)⁻²` (with `χ = bumpC` the cutoff in the definition of
`beurling`) is absolutely integrable.

This is the measure-theoretic content behind the linearity of the Beurling transform: the
subtraction of `χ(ζ - z) h z` makes the kernel compactly supported, and the Hölder
regularity of `h` makes the `(ζ - z)⁻²` singularity integrable in the plane. -/
theorem integrable_beurling_integrand {h : ℂ → ℂ} {α M K R : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (hR : 0 ≤ R) (hM : ∀ z, ‖h z‖ ≤ M)
    (hK : ∀ x y : ℂ, ‖h x - h y‖ ≤ K * ‖x - y‖ ^ α)
    (hsup : ∀ z, R < ‖z‖ → h z = 0) (z : ℂ) :
    Integrable (fun ζ : ℂ => (h ζ - (bumpC (ζ - z) : ℂ) * h z) * ((ζ - z) ^ 2)⁻¹) volume := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (h 0)) (hM 0)
  -- Replace `K` by `K' = max K 0 ≥ 0`; the Hölder bound survives.
  set K' : ℝ := max K 0 with hK'def
  have hK'0 : 0 ≤ K' := by rw [hK'def]; exact le_max_right _ _
  have hK'le : K ≤ K' := by rw [hK'def]; exact le_max_left _ _
  have hK' : ∀ x y : ℂ, ‖h x - h y‖ ≤ K' * ‖x - y‖ ^ α := fun x y =>
    le_trans (hK x y) (mul_le_mul_of_nonneg_right hK'le (Real.rpow_nonneg (norm_nonneg _) α))
  -- A Hölder function of positive order is continuous, hence measurable.
  have hcont : Continuous h := by
    rw [Metric.continuous_iff]
    intro x ε hε
    have hK1 : (0 : ℝ) < K' + 1 := by linarith
    refine ⟨(ε / (K' + 1)) ^ (1 / α), Real.rpow_pos_of_pos (div_pos hε hK1) _, ?_⟩
    intro y hy
    rw [dist_eq_norm]
    have hy' : ‖y - x‖ < (ε / (K' + 1)) ^ (1 / α) := by
      simpa [dist_eq_norm] using hy
    have hbase : 0 < ε / (K' + 1) := div_pos hε hK1
    have hpow : ((ε / (K' + 1)) ^ (1 / α)) ^ α = ε / (K' + 1) := by
      rw [← Real.rpow_mul hbase.le]
      rw [show 1 / α * α = 1 by field_simp]
      rw [Real.rpow_one]
    have hle : ‖y - x‖ ^ α ≤ ε / (K' + 1) := by
      have h1 : ‖y - x‖ ^ α ≤ ((ε / (K' + 1)) ^ (1 / α)) ^ α :=
        Real.rpow_le_rpow (norm_nonneg _) hy'.le hα.le
      rwa [hpow] at h1
    calc ‖h y - h x‖ ≤ K' * ‖y - x‖ ^ α := hK' y x
      _ ≤ K' * (ε / (K' + 1)) := mul_le_mul_of_nonneg_left hle hK'0
      _ < (K' + 1) * (ε / (K' + 1)) := mul_lt_mul_of_pos_right (by linarith) hbase
      _ = ε := by rw [mul_comm, div_mul_cancel₀ ε (ne_of_gt hK1)]
  -- The majorant constant.
  set C : ℝ := max K' (max (8 * M) 0) with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hK'C : K' ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hC8M : 8 * M ≤ C := by
    rw [hCdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hMC : M ≤ C := le_trans (by linarith) hC8M
  -- The support radius for the translated integrand.
  set ρ : ℝ := R + ‖z‖ + 1 with hρdef
  have hsupp : ∀ w : ℂ, ρ ≤ ‖w‖ → (h (z + w) - (bumpC w : ℂ) * h z) * (w ^ 2)⁻¹ = 0 := by
    intro w hw
    have h1 : h (z + w) = 0 := by
      apply hsup
      have h2 : ‖w‖ ≤ ‖z + w‖ + ‖z‖ := by
        have := norm_sub_le (z + w) z
        rwa [add_sub_cancel_left] at this
      have h3 : R + ‖z‖ + 1 ≤ ‖w‖ := by rw [← hρdef]; exact hw
      linarith
    have h4 : (bumpC w : ℂ) = 0 := by
      rw [bumpC_eq_zero (by
        have h1ρ : (1 : ℝ) ≤ ρ := by rw [hρdef]; linarith [norm_nonneg z]
        linarith : (1 : ℝ) ≤ ‖w‖)]
      norm_num
    rw [h1, h4]; simp
  -- Measurability of the translated integrand.
  have hmeas : AEStronglyMeasurable
      (fun w : ℂ => (h (z + w) - (bumpC w : ℂ) * h z) * (w ^ 2)⁻¹) volume := by
    have h1 : Measurable (fun w : ℂ => h (z + w)) :=
      hcont.measurable.comp (continuous_const.add continuous_id).measurable
    have h3 : Measurable (fun w : ℂ => (w ^ 2)⁻¹) := (measurable_id.pow_const 2).inv
    exact ((h1.sub (measurable_bumpC.mul measurable_const)).mul h3).aestronglyMeasurable
  -- Global pointwise domination by `C ‖w‖^(α-2)`.
  have hbound : ∀ w : ℂ,
      ‖(h (z + w) - (bumpC w : ℂ) * h z) * (w ^ 2)⁻¹‖ ≤ C * ‖w‖ ^ (α - 2) := by
    intro w
    by_cases hw0 : w = 0
    · subst hw0
      have hz0 : (h (z + 0) - (bumpC (0 : ℂ) : ℂ) * h z) * ((0 : ℂ) ^ 2)⁻¹ = 0 := by
        rw [bumpC_eq_one (by simp : ‖(0 : ℂ)‖ ≤ 1 / 2)]; simp
      rw [hz0, norm_zero]
      exact mul_nonneg hC0 (Real.rpow_nonneg (le_refl 0) _)
    · have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hker : ‖(w ^ 2)⁻¹‖ = ‖w‖ ^ (-2 : ℝ) := by
        have h2 : (‖w‖ : ℝ) ^ (-2 : ℝ) = ((‖w‖ : ℝ) ^ 2)⁻¹ := by
          rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num,
            Real.rpow_neg (norm_nonneg w), Real.rpow_natCast]
        rw [norm_inv, norm_pow, h2]
      have hb1 : ‖(bumpC w : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (bumpC_nonneg w)]
        exact bumpC_le_one w
      by_cases hle : ‖w‖ ≤ 1 / 2
      · -- small ball: the cutoff is `1` and the Hölder estimate applies.
        have hbump : (bumpC w : ℂ) = 1 := by
          rw [bumpC_eq_one hle]; norm_num
        rw [hbump, one_mul]
        have hnum : ‖h (z + w) - h z‖ ≤ K' * ‖w‖ ^ α := by
          have := hK' (z + w) z
          rwa [add_sub_cancel_left] at this
        calc ‖(h (z + w) - h z) * (w ^ 2)⁻¹‖
            = ‖h (z + w) - h z‖ * ‖w‖ ^ (-2 : ℝ) := by rw [norm_mul, hker]
          _ ≤ (K' * ‖w‖ ^ α) * ‖w‖ ^ (-2 : ℝ) :=
              mul_le_mul_of_nonneg_right hnum (Real.rpow_nonneg (norm_nonneg w) _)
          _ = K' * ‖w‖ ^ (α - 2) := by
              rw [mul_assoc, ← Real.rpow_add hwpos, show α + (-2 : ℝ) = α - 2 from by ring]
          _ ≤ C * ‖w‖ ^ (α - 2) :=
              mul_le_mul_of_nonneg_right hK'C (Real.rpow_nonneg (norm_nonneg w) _)
      · have hhalf : 1 / 2 < ‖w‖ := lt_of_not_ge hle
        by_cases hle1 : ‖w‖ ≤ 1
        · -- shell: numerator bounded by `2M`, kernel by `4`.
          have hnum : ‖h (z + w) - (bumpC w : ℂ) * h z‖ ≤ 2 * M := by
            calc ‖h (z + w) - (bumpC w : ℂ) * h z‖
                ≤ ‖h (z + w)‖ + ‖(bumpC w : ℂ) * h z‖ := norm_sub_le _ _
              _ = ‖h (z + w)‖ + ‖(bumpC w : ℂ)‖ * ‖h z‖ := by rw [norm_mul]
              _ ≤ M + 1 * M := add_le_add (hM (z + w))
                  (mul_le_mul hb1 (hM z) (norm_nonneg _) (by norm_num))
              _ = 2 * M := by ring
          have hker2 : ‖(w ^ 2)⁻¹‖ ≤ 4 := by
            rw [norm_inv, norm_pow]
            rw [inv_le_comm₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
            rw [show (4 : ℝ)⁻¹ = 1 / 4 by norm_num]
            have : (1 / 4 : ℝ) ≤ ‖w‖ ^ 2 := by nlinarith [hhalf, norm_nonneg w]
            linarith
          calc ‖(h (z + w) - (bumpC w : ℂ) * h z) * (w ^ 2)⁻¹‖
              = ‖h (z + w) - (bumpC w : ℂ) * h z‖ * ‖(w ^ 2)⁻¹‖ := norm_mul _ _
            _ ≤ (2 * M) * 4 := mul_le_mul hnum hker2 (norm_nonneg _) (by linarith)
            _ = 8 * M := by ring
            _ ≤ C * ‖w‖ ^ (α - 2) := by
                have h1 : (1 : ℝ) ≤ ‖w‖ ^ (α - 2) := by
                  have hneg : α - 2 ≤ 0 := by linarith
                  have := Real.rpow_le_rpow_of_nonpos hwpos hle1 hneg
                  simpa using this
                calc 8 * M ≤ C * 1 := by nlinarith
                  _ ≤ C * ‖w‖ ^ (α - 2) := mul_le_mul_of_nonneg_left h1 hC0
        · -- outside the unit disc: the cutoff vanishes.
          have hge1 : 1 ≤ ‖w‖ := le_of_lt (lt_of_not_ge hle1)
          have hbump0 : (bumpC w : ℂ) = 0 := by
            rw [bumpC_eq_zero hge1]; norm_num
          rw [hbump0, zero_mul, sub_zero]
          have hone : (1 : ℝ) ≤ ‖w‖ ^ α := Real.one_le_rpow hge1 hα.le
          have hMC' : M ≤ C * ‖w‖ ^ α := by
            calc M ≤ C * 1 := by nlinarith
              _ ≤ C * ‖w‖ ^ α := mul_le_mul_of_nonneg_left hone hC0
          calc ‖h (z + w) * (w ^ 2)⁻¹‖
              = ‖h (z + w)‖ * ‖w‖ ^ (-2 : ℝ) := by rw [norm_mul, hker]
            _ ≤ M * ‖w‖ ^ (-2 : ℝ) :=
                mul_le_mul_of_nonneg_right (hM (z + w)) (Real.rpow_nonneg (norm_nonneg w) _)
            _ ≤ (C * ‖w‖ ^ α) * ‖w‖ ^ (-2 : ℝ) :=
                mul_le_mul_of_nonneg_right hMC' (Real.rpow_nonneg (norm_nonneg w) _)
            _ = C * ‖w‖ ^ (α - 2) := by
                rw [mul_assoc, ← Real.rpow_add hwpos, show α + (-2 : ℝ) = α - 2 from by ring]
  -- Integrability on a disc, from the domination and `α - 2 > -2`.
  have hint : IntegrableOn
      (fun w : ℂ => (h (z + w) - (bumpC w : ℂ) * h z) * (w ^ 2)⁻¹) (Metric.ball 0 ρ) volume := by
    refine integrableOn_ball_of_norm_le_rpow (E := ℂ) (F := ℂ) (μ := volume)
      (f := fun w : ℂ => (h (z + w) - (bumpC w : ℂ) * h z) * (w ^ 2)⁻¹)
      (C := C) (α := 2 - α) (r := ρ) ?_ ?_ ?_ hmeas
    · rw [Complex.finrank_real_complex]; norm_num
    · rw [Complex.finrank_real_complex]; norm_num; linarith
    · filter_upwards with w
      rw [show -(2 - α) = α - 2 from by ring]
      exact hbound w
  have hintfull : Integrable
      (fun w : ℂ => (h (z + w) - (bumpC w : ℂ) * h z) * (w ^ 2)⁻¹) volume :=
    IntegrableOn.integrable_of_forall_notMem_eq_zero hint (by
      intro w hw
      rw [Metric.mem_ball, dist_zero_right, not_lt] at hw
      exact hsupp w hw)
  -- Translate back to the original variable `ζ = z + w`.
  haveI : (volume : Measure ℂ).IsAddRightInvariant := IsAddLeftInvariant.isAddRightInvariant
  refine (hintfull.comp_sub_right z).congr ?_
  filter_upwards with ζ
  simp only [add_sub_cancel]

/-- **Linearity of the Beurling transform.**  For bounded, `α`-Hölder functions `f`, `g` with
support in the disc of radius `R`, the Beurling transform is additive:
`beurling (f - g) = beurling f - beurling g` (as functions). -/
theorem beurling_sub (α : ℝ) (hα : 0 < α) (hα1 : α < 1) (f g : ℂ → ℂ) (M K R : ℝ)
    (hR : 0 ≤ R) (hMf : ∀ z, ‖f z‖ ≤ M) (hMg : ∀ z, ‖g z‖ ≤ M)
    (hKf : ∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α)
    (hKg : ∀ x y : ℂ, ‖g x - g y‖ ≤ K * ‖x - y‖ ^ α)
    (hsf : ∀ z, R < ‖z‖ → f z = 0) (hsg : ∀ z, R < ‖z‖ → g z = 0) :
    beurling (f - g) = beurling f - beurling g := by
  funext z
  simp only [Pi.sub_apply]
  have hfint : Integrable
      (fun ζ : ℂ => (f ζ - (bumpC (ζ - z) : ℂ) * f z) * ((ζ - z) ^ 2)⁻¹) volume :=
    integrable_beurling_integrand hα hα1 hR hMf hKf hsf z
  have hgint : Integrable
      (fun ζ : ℂ => (g ζ - (bumpC (ζ - z) : ℂ) * g z) * ((ζ - z) ^ 2)⁻¹) volume :=
    integrable_beurling_integrand hα hα1 hR hMg hKg hsg z
  have hkey : (fun ζ : ℂ => ((f - g) ζ - (bumpC (ζ - z) : ℂ) * (f - g) z) * ((ζ - z) ^ 2)⁻¹)
      = (fun ζ : ℂ => (f ζ - (bumpC (ζ - z) : ℂ) * f z) * ((ζ - z) ^ 2)⁻¹
          - (g ζ - (bumpC (ζ - z) : ℂ) * g z) * ((ζ - z) ^ 2)⁻¹) := by
    funext ζ
    simp only [Pi.sub_apply]
    rw [show f ζ - g ζ - (bumpC (ζ - z) : ℂ) * (f z - g z)
        = (f ζ - (bumpC (ζ - z) : ℂ) * f z) - (g ζ - (bumpC (ζ - z) : ℂ) * g z) from by
          ring]
    rw [sub_mul]
  rw [beurling_apply, beurling_apply, beurling_apply, hkey, integral_sub hfint hgint, smul_sub]

end

end Work.Beltrami

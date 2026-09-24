import Mathlib
import Submission.Work.GM.Affine.nearcorr_defs
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.rho_kernel_domination

/-!
# Vanishing of the smoothed profile outside the support interval (GM §9)

The smoothed profile is `Afun f M₂ K T v = ∫ u, Hprof f M₂ (v - s u) ψ(u) du` with
`s = smScale K T M₂ = M₂/(2KT)` and

`Hprof f M₂ x = Σ_{m₂ ∈ R2 M₂} f (x / m₂)`, `R2 M₂ = {m ∈ ℤ : M₂ < m ≤ 2 M₂}`.

Since `f` is supported in `[1/C₀, C₀]` and `ψ = psiSmooth` is supported in `|u| ≤ 1/4`,
a non-zero value of the integrand for some `u` forces

`v - s u ∈ [M₂/C₀, 2 C₀ M₂]` and `|s u| ≤ s/4`,

hence `v ∈ [M₂/C₀ - s/4, 2 C₀ M₂ + s/4]`.  Consequently `Afun f M₂ K T` vanishes outside
that interval: `Afun f M₂ K T` is supported in the interval of the statement.
-/

namespace Work.GM.Affine

theorem nearcorr_Afun_eq_zero_of_notMem {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {f : ℝ → ℝ} (hsup : SuppHyp C₀ f)
    {M₂ K T : ℝ} (hM₂ : 0 < M₂) (hK : 0 < K) (hT : 0 < T) {v : ℝ}
    (hv : v ∉ Set.Icc (M₂ / C₀ - smScale K T M₂ / 4) (2 * C₀ * M₂ + smScale K T M₂ / 4)) :
    Afun f M₂ K T v = 0 := by
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hs : 0 < smScale K T M₂ := smScale_pos hK hT hM₂
  rw [Afun]
  have hzero : ∀ u, Hprof f M₂ (v - smScale K T M₂ * u) * psiSmooth u = 0 := by
    intro u
    by_cases hpsi : psiSmooth u = 0
    · rw [hpsi, mul_zero]
    · -- `ψ` is supported in `|u| < 1/4`
      have hu : |u| < 1 / 4 := by
        by_contra h
        exact hpsi (rho_psiSmooth_zero_of_quarter_le_abs (not_lt.mp h))
      have hu1 : -(1 / 4 : ℝ) < u := (abs_lt.mp hu).1
      have hu2 : u < 1 / 4 := (abs_lt.mp hu).2
      rw [Hprof, Finset.sum_mul]
      refine Finset.sum_eq_zero fun m hm => ?_
      by_cases hf : f ((v - smScale K T M₂ * u) / (m : ℝ)) = 0
      · rw [hf, zero_mul]
      · -- a non-vanishing term forces `v` into the forbidden interval
        exfalso
        have hmem := hsup _ hf
        rw [Set.mem_Icc] at hmem
        obtain ⟨hm1, hm2⟩ := hmem
        have hmpos : (0 : ℝ) < (m : ℝ) := R2_pos' hm
        have hmgt : M₂ < (m : ℝ) := (Finset.mem_filter.mp hm).2
        have hmle : (m : ℝ) ≤ 2 * M₂ := R2_le' hm
        have hlow : M₂ / C₀ < v - smScale K T M₂ * u := by
          have h1 : (m : ℝ) * (1 / C₀) ≤ (v - smScale K T M₂ * u) := by
            have h := mul_le_mul_of_nonneg_left hm1 hmpos.le
            rwa [mul_div_cancel₀ _ (ne_of_gt hmpos)] at h
          have h2 : M₂ / C₀ < (m : ℝ) * (1 / C₀) := by
            rw [mul_one_div]
            exact (div_lt_div_iff_of_pos_right hC₀pos).mpr hmgt
          linarith
        have hhigh : v - smScale K T M₂ * u ≤ 2 * C₀ * M₂ := by
          have h1 : (v - smScale K T M₂ * u) ≤ (m : ℝ) * C₀ := by
            have h := mul_le_mul_of_nonneg_left hm2 hmpos.le
            rwa [mul_div_cancel₀ _ (ne_of_gt hmpos)] at h
          have h2 : (m : ℝ) * C₀ ≤ 2 * M₂ * C₀ :=
            mul_le_mul_of_nonneg_right hmle hC₀pos.le
          linarith
        have hsle : smScale K T M₂ * u ≤ smScale K T M₂ / 4 := by
          have h := mul_lt_mul_of_pos_left hu2 hs
          linarith
        have hsge : -(smScale K T M₂ / 4) ≤ smScale K T M₂ * u := by
          have h := mul_lt_mul_of_pos_left hu1 hs
          linarith
        have hsplit : (v - smScale K T M₂ * u) + smScale K T M₂ * u = v := by ring
        have hvlow : M₂ / C₀ - smScale K T M₂ / 4 < v := by
          have h := add_lt_add_of_lt_of_le hlow hsge
          linarith
        have hvhigh : v ≤ 2 * C₀ * M₂ + smScale K T M₂ / 4 := by
          have h := add_le_add hhigh hsle
          linarith
        exact hv ⟨le_of_lt hvlow, hvhigh⟩
  simp only [hzero, MeasureTheory.integral_zero]

end Work.GM.Affine

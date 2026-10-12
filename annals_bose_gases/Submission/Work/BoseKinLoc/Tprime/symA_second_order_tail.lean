import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.OneBodyKin.integrable_fsKinCoeff_shift_mul_profHat_sq
import Submission.Work.OneBodyKin.profHat_sq_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Tprime.symA_second_order_tail`

The **tail-threshold version** of the second-order bound for the unprojected symbol
`symA 1 F ρ = (2π)⁻³ ∫_p F ‖ρ + p‖ · profHat(p)² dp` at the FS cut-off
`fsKinCoeff C = [·−C]₊²`:

    `symA 1 (fsKinCoeff C) ρ − symA 1 (fsKinCoeff C) 0
       ≤ 4 (2π)⁻³ · (∫_{‖p‖ > C/6} profHat(p)² dp) · ‖ρ‖²`   for `‖ρ‖ ≤ (5/6) C`.

This is the form in which the two-regime symbol bound of Brietzke–Solovej `lm:kinloc` consumes
the second-order behaviour of `symA`: on the near region `‖q‖ < (5/6)σ⁻¹` (i.e. `C = σ⁻¹`,
`ρ = q`) the tail cut-off sits at `C/6`, *not* at `C/2` as in
`Work.OneBodyKin.symA_second_order_bound`.

## The mechanism

Exactly as for `symA_second_order_bound`: `profHat` is even, so symmetrising the difference of
the two integrals gives

    `symA 1 F ρ − symA 1 F 0 = (2π)⁻³ · ½ ∫_p (F‖ρ+p‖ + F‖ρ−p‖ − 2F‖p‖) · profHat(p)² dp`,

and the pointwise factor obeys a two-regime bound:

* **near** (`‖p‖ ≤ C/6`): `‖ρ ± p‖ ≤ ‖ρ‖ + ‖p‖ ≤ (5/6)C + C/6 = C` and `‖p‖ ≤ C`, so all three
  coefficients vanish;
* **far** (`‖p‖ > C/6`): the factor is at most `8‖ρ‖²` — **unconditionally**, with no hypothesis
  on `‖ρ‖` or `‖p‖`.  Writing `u = ‖p+ρ‖`, `v = ‖p−ρ‖`, `x = ‖p‖`, `r = ‖ρ‖` and splitting on
  `C + r ≤ x`:
  * if `x ≥ C + r` then `u, v ≥ x − r ≥ C`, so with the parallelogram identity
    `u² + v² = 2x² + 2r²` and `u + v ≥ 2x`,
    `(u−C)² + (v−C)² − 2(x−C)² = 2r² − 2C(u+v−2x) ≤ 2r²`;
  * otherwise `u, v ≤ x + r < C + 2r`, hence `max(u−C,0), max(v−C,0) ≤ 2r`, giving
    `[u−C]₊² + [v−C]₊² ≤ 4r² + 4r² = 8r²` (the third term is `≥ 0`).

Hence the integrand is dominated by `8‖ρ‖² profHat(p)² 1_{‖p‖ > C/6}` and the claim follows by
monotonicity of the integral.

(`Work.OneBodyKin.symA_key_pointwise_far` states the far bound with the extra hypotheses
`‖ρ‖ ≤ C/2`, `C/2 ≤ ‖p‖`; the proof here — `symA_key_pointwise_uncond` — records that neither
is needed, which is what allows the tail threshold `C/6` with `‖ρ‖ ≤ 5C/6`.)
-/

noncomputable section

namespace Work.BoseKinLoc.Tprime

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open Work.OneBodyKin

set_option maxHeartbeats 800000

/-! ## 1. The hypothesis-free pointwise second-difference bound -/

/-- **The pointwise second-difference bound for the FS cut-off, with no smallness hypotheses.**

With `fsKinCoeff C r = [r − C]₊²`, for every `ρ` and `p`,

    `[‖p+ρ‖ − C]₊² + [‖p−ρ‖ − C]₊² − 2[‖p‖ − C]₊² ≤ 8‖ρ‖²`.

(Compare `Work.OneBodyKin.symA_key_pointwise_far`, which assumes `‖ρ‖ ≤ C/2` and `C/2 ≤ ‖p‖`;
the proof below shows neither hypothesis is used.) -/
theorem symA_key_pointwise_uncond (C : ℝ) (hC : 0 < C) (ρ p : ℝ³) :
    fsKinCoeff C ‖p + ρ‖ + fsKinCoeff C ‖p - ρ‖ - 2 * fsKinCoeff C ‖p‖ ≤ 8 * ‖ρ‖ ^ 2 := by
  have hr0 : 0 ≤ ‖ρ‖ := norm_nonneg _
  have hu_le : ‖p + ρ‖ ≤ ‖p‖ + ‖ρ‖ := norm_add_le p ρ
  have hv_le : ‖p - ρ‖ ≤ ‖p‖ + ‖ρ‖ := norm_sub_le p ρ
  have hu_abs := abs_norm_sub_norm_le (p + ρ) p
  rw [show (p + ρ) - p = ρ from by abel] at hu_abs
  have hv_abs := abs_norm_sub_norm_le (p - ρ) p
  rw [show (p - ρ) - p = -ρ from by abel, norm_neg] at hv_abs
  by_cases hA : C + ‖ρ‖ ≤ ‖p‖
  · -- far case: `‖p‖ ≥ C + ‖ρ‖`, so all three norms are at least `C`
    have hCu : C ≤ ‖p + ρ‖ := by have := (abs_le.mp hu_abs).1; linarith
    have hCv : C ≤ ‖p - ρ‖ := by have := (abs_le.mp hv_abs).1; linarith
    have hCx : C ≤ ‖p‖ := by linarith
    have hgu : fsKinCoeff C ‖p + ρ‖ = (‖p + ρ‖ - C) ^ 2 := by
      rw [fsKinCoeff, max_eq_left (by linarith)]
    have hgv : fsKinCoeff C ‖p - ρ‖ = (‖p - ρ‖ - C) ^ 2 := by
      rw [fsKinCoeff, max_eq_left (by linarith)]
    have hgx : fsKinCoeff C ‖p‖ = (‖p‖ - C) ^ 2 := by
      rw [fsKinCoeff, max_eq_left (by linarith)]
    have hsq : ‖p + ρ‖ ^ 2 + ‖p - ρ‖ ^ 2 = 2 * ‖p‖ ^ 2 + 2 * ‖ρ‖ ^ 2 := by
      rw [norm_add_sq_real, norm_sub_sq_real]; ring
    have htri : 2 * ‖p‖ ≤ ‖p + ρ‖ + ‖p - ρ‖ := by
      have h := norm_add_le (p + ρ) (p - ρ)
      rw [show (p + ρ) + (p - ρ) = (2 : ℝ) • p from by module, norm_smul] at h
      rw [Real.norm_ofNat, mul_comm] at h
      linarith
    rw [hgu, hgv, hgx]
    nlinarith [hsq, htri, hC, sq_nonneg ‖ρ‖]
  · -- near-far case: `‖p‖ < C + ‖ρ‖`, so `‖p ± ρ‖ < C + 2‖ρ‖`
    rw [not_le] at hA
    have hgu : fsKinCoeff C ‖p + ρ‖ ≤ 4 * ‖ρ‖ ^ 2 := by
      rw [fsKinCoeff]
      have h1 : max (‖p + ρ‖ - C) 0 ≤ 2 * ‖ρ‖ := max_le (by linarith) (by linarith)
      calc (max (‖p + ρ‖ - C) 0) ^ 2 ≤ (2 * ‖ρ‖) ^ 2 :=
            pow_le_pow_left₀ (le_max_right _ _) h1 2
        _ = 4 * ‖ρ‖ ^ 2 := by ring
    have hgv : fsKinCoeff C ‖p - ρ‖ ≤ 4 * ‖ρ‖ ^ 2 := by
      rw [fsKinCoeff]
      have h1 : max (‖p - ρ‖ - C) 0 ≤ 2 * ‖ρ‖ := max_le (by linarith) (by linarith)
      calc (max (‖p - ρ‖ - C) 0) ^ 2 ≤ (2 * ‖ρ‖) ^ 2 :=
            pow_le_pow_left₀ (le_max_right _ _) h1 2
        _ = 4 * ‖ρ‖ ^ 2 := by ring
    nlinarith [hgu, hgv, fsKinCoeff_nonneg C ‖p‖, sq_nonneg ‖ρ‖]

/-! ## 2. The requested tail bound -/

theorem symA_second_order_tail (C : ℝ) (hC : 0 < C) (ρ : EuclideanSpace ℝ (Fin 3)) (hρ : ‖ρ‖ ≤ (5 / 6) * C) :
    Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) ρ
      - Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) 0
      ≤ 4 * ((2 * Real.pi) ^ 3)⁻¹
        * (∫ p in {p : EuclideanSpace ℝ (Fin 3) | C / 6 < ‖p‖}, (Work.OneBodyKin.profHat p) ^ 2)
        * ‖ρ‖ ^ 2 := by
  -- the three profile-weighted symbols
  set A : ℝ³ → ℝ := fun p => fsKinCoeff C ‖ρ + p‖ * (profHat p) ^ 2 with hA
  set B : ℝ³ → ℝ := fun p => fsKinCoeff C ‖ρ - p‖ * (profHat p) ^ 2 with hB
  set Z : ℝ³ → ℝ := fun p => fsKinCoeff C ‖p‖ * (profHat p) ^ 2 with hZ
  have hAi : Integrable A := by
    rw [hA]; exact integrable_fsKinCoeff_shift_mul_profHat_sq C ρ
  have hBi : Integrable B := by
    have hfe : (fun p : ℝ³ => fsKinCoeff C ‖-ρ + p‖ * (profHat p) ^ 2)
        = fun p : ℝ³ => fsKinCoeff C ‖ρ - p‖ * (profHat p) ^ 2 := by
      funext p
      rw [show -ρ + p = -(ρ - p) by abel, norm_neg]
    rw [hB, ← hfe]
    exact integrable_fsKinCoeff_shift_mul_profHat_sq C (-ρ)
  have hZi : Integrable Z := by
    rw [hZ]
    simpa using integrable_fsKinCoeff_shift_mul_profHat_sq C (0 : ℝ³)
  have hRi : Integrable (fun q : ℝ³ => (profHat q) ^ 2) := by
    have h := integrable_profHat_sq_mul_norm_pow 0 (by norm_num)
    simpa using h
  -- `symA` is the `(2π)⁻³`-multiple of the integral of the symbol
  have hsym1 : Work.OneBodyKin.symA 1 (fsKinCoeff C) ρ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, A p := by
    rw [hA]; unfold Work.OneBodyKin.symA; simp
  have hsym0 : Work.OneBodyKin.symA 1 (fsKinCoeff C) 0 = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, Z p := by
    rw [hZ]; unfold Work.OneBodyKin.symA; simp
  -- the profile is even, so the two shifted integrals agree
  have hsymAB : (∫ p : ℝ³, A p) = ∫ p : ℝ³, B p := by
    have h := integral_neg_eq_self A volume
    rw [← h]
    apply integral_congr_ae
    filter_upwards with p
    simp only [hA, hB]
    rw [show ρ + -p = ρ - p by abel, profHat_even]
  have hkey : (∫ p : ℝ³, A p + B p - 2 * Z p) = 2 * ((∫ p : ℝ³, A p) - ∫ p : ℝ³, Z p) := by
    have h1 : (∫ p : ℝ³, A p + B p - 2 * Z p) = (∫ p : ℝ³, A p + B p) - (∫ p : ℝ³, 2 * Z p) :=
      integral_sub (hAi.add hBi) (hZi.const_mul 2)
    have h2 : (∫ p : ℝ³, A p + B p) = (∫ p : ℝ³, A p) + ∫ p : ℝ³, B p := integral_add hAi hBi
    have h3 : (∫ p : ℝ³, 2 * Z p) = 2 * ∫ p : ℝ³, Z p := integral_const_mul 2 Z
    rw [h1, h2, h3, hsymAB]
    ring
  have hW : (∫ p : ℝ³, A p + B p - 2 * Z p)
      = ∫ p : ℝ³, (fsKinCoeff C ‖ρ + p‖ + fsKinCoeff C ‖ρ - p‖ - 2 * fsKinCoeff C ‖p‖)
          * (profHat p) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with p
    simp only [hA, hB, hZ]
    ring
  have hsymAeq : Work.OneBodyKin.symA 1 (fsKinCoeff C) ρ - Work.OneBodyKin.symA 1 (fsKinCoeff C) 0
      = ((2 * Real.pi) ^ 3)⁻¹ * ((1 / 2) * ∫ p : ℝ³, A p + B p - 2 * Z p) := by
    rw [hsym1, hsym0, ← mul_sub]
    congr 1
    have hhalf : (∫ p : ℝ³, A p) - (∫ p : ℝ³, Z p) = (1 / 2) * ∫ p : ℝ³, A p + B p - 2 * Z p := by
      rw [hkey]; ring
    exact hhalf
  -- the pointwise bounds, in the orientation used by `A`, `B`, `Z`
  have hfar' : ∀ p : ℝ³, C / 6 < ‖p‖ →
      fsKinCoeff C ‖ρ + p‖ + fsKinCoeff C ‖ρ - p‖ - 2 * fsKinCoeff C ‖p‖ ≤ 8 * ‖ρ‖ ^ 2 := by
    intro p hp
    simpa only [add_comm p ρ, norm_sub_rev] using symA_key_pointwise_uncond C hC ρ p
  have hnear' : ∀ p : ℝ³, ‖p‖ ≤ C / 6 →
      fsKinCoeff C ‖ρ + p‖ + fsKinCoeff C ‖ρ - p‖ - 2 * fsKinCoeff C ‖p‖ = 0 := by
    intro p hp
    have hsum : ‖ρ‖ + ‖p‖ ≤ C := by linarith
    have h1 : fsKinCoeff C ‖ρ + p‖ = 0 :=
      fsKinCoeff_of_le (le_trans (norm_add_le ρ p) hsum)
    have h2 : fsKinCoeff C ‖ρ - p‖ = 0 :=
      fsKinCoeff_of_le (le_trans (norm_sub_le ρ p) hsum)
    have h0 : fsKinCoeff C ‖p‖ = 0 := fsKinCoeff_of_le (by linarith)
    rw [h1, h2, h0]; ring
  have hSmeas : MeasurableSet {p : ℝ³ | C / 6 < ‖p‖} :=
    measurableSet_lt measurable_const measurable_norm
  have hptW : ∀ p : ℝ³,
      (fsKinCoeff C ‖ρ + p‖ + fsKinCoeff C ‖ρ - p‖ - 2 * fsKinCoeff C ‖p‖) * (profHat p) ^ 2
        ≤ Set.indicator {p : ℝ³ | C / 6 < ‖p‖} (fun q => 8 * ‖ρ‖ ^ 2 * (profHat q) ^ 2) p := by
    intro p
    by_cases hp : C / 6 < ‖p‖
    · have hpmem : p ∈ {q : ℝ³ | C / 6 < ‖q‖} := hp
      rw [Set.indicator_of_mem hpmem]
      exact mul_le_mul_of_nonneg_right (hfar' p hp) (sq_nonneg _)
    · have hpmem : p ∉ {q : ℝ³ | C / 6 < ‖q‖} := hp
      rw [Set.indicator_of_notMem hpmem]
      have hp' : ‖p‖ ≤ C / 6 := not_lt.mp hp
      rw [hnear' p hp', zero_mul]
  have hWi : Integrable (fun p : ℝ³ =>
      (fsKinCoeff C ‖ρ + p‖ + fsKinCoeff C ‖ρ - p‖ - 2 * fsKinCoeff C ‖p‖)
        * (profHat p) ^ 2) := by
    have heq : (fun p : ℝ³ =>
        (fsKinCoeff C ‖ρ + p‖ + fsKinCoeff C ‖ρ - p‖ - 2 * fsKinCoeff C ‖p‖)
          * (profHat p) ^ 2)
        = fun p : ℝ³ => A p + B p - 2 * Z p := by
      funext p; simp only [hA, hB, hZ]; ring
    rw [heq]
    exact (hAi.add hBi).sub (hZi.const_mul 2)
  have hRhsi : Integrable (Set.indicator {p : ℝ³ | C / 6 < ‖p‖}
      (fun q => 8 * ‖ρ‖ ^ 2 * (profHat q) ^ 2)) :=
    (hRi.const_mul (8 * ‖ρ‖ ^ 2)).indicator hSmeas
  have hmono : (∫ p : ℝ³,
        (fsKinCoeff C ‖ρ + p‖ + fsKinCoeff C ‖ρ - p‖ - 2 * fsKinCoeff C ‖p‖)
          * (profHat p) ^ 2)
      ≤ ∫ p : ℝ³, Set.indicator {p : ℝ³ | C / 6 < ‖p‖}
          (fun q => 8 * ‖ρ‖ ^ 2 * (profHat q) ^ 2) p :=
    integral_mono hWi hRhsi hptW
  have hrhs : (∫ p : ℝ³, Set.indicator {p : ℝ³ | C / 6 < ‖p‖}
        (fun q => 8 * ‖ρ‖ ^ 2 * (profHat q) ^ 2) p)
      = 8 * ‖ρ‖ ^ 2 * (∫ p in {p : ℝ³ | C / 6 < ‖p‖}, (profHat p) ^ 2) := by
    have h1 : (∫ p : ℝ³, Set.indicator {p : ℝ³ | C / 6 < ‖p‖}
          (fun q => 8 * ‖ρ‖ ^ 2 * (profHat q) ^ 2) p)
        = ∫ p : ℝ³, 8 * ‖ρ‖ ^ 2
            * (Set.indicator {p : ℝ³ | C / 6 < ‖p‖} (fun q => (profHat q) ^ 2) p) := by
      apply integral_congr_ae
      filter_upwards with p
      by_cases h : p ∈ {p : ℝ³ | C / 6 < ‖p‖}
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
    rw [h1, integral_const_mul, integral_indicator hSmeas]
  calc Work.OneBodyKin.symA 1 (fsKinCoeff C) ρ - Work.OneBodyKin.symA 1 (fsKinCoeff C) 0
      = ((2 * Real.pi) ^ 3)⁻¹ * ((1 / 2) * ∫ p : ℝ³, A p + B p - 2 * Z p) := hsymAeq
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ((1 / 2) * ∫ p : ℝ³,
          (fsKinCoeff C ‖ρ + p‖ + fsKinCoeff C ‖ρ - p‖ - 2 * fsKinCoeff C ‖p‖)
            * (profHat p) ^ 2) := by
        rw [hW]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          ((1 / 2) * (8 * ‖ρ‖ ^ 2 * (∫ p in {p : ℝ³ | C / 6 < ‖p‖}, (profHat p) ^ 2))) := by
        have h := hmono
        rw [hrhs] at h
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h (by norm_num)) (by positivity)
    _ = 4 * ((2 * Real.pi) ^ 3)⁻¹ * (∫ p in {p : ℝ³ | C / 6 < ‖p‖}, (profHat p) ^ 2)
          * ‖ρ‖ ^ 2 := by ring

end Work.BoseKinLoc.Tprime

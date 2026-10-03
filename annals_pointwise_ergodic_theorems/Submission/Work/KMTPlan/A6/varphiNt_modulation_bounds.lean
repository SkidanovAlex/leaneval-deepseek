/-
# Uniform `L¹` bounds for the modulated bump and its second derivative

For a fixed `C^2` compactly supported `u : ℝ → ℂ` and a frequency `c = N·t` ranging over
`t ∈ [1/2, 1]` (so `|c| ≤ N`), the two quantities

* `∫ ‖u y · e(c y)‖ dy` and
* `∫ ‖(u · e(c·))''(y)‖ dy`

are bounded by a single constant `S` depending only on `u` and `N`.  This is the elementary
"price of the modulation" estimate: since `‖e(c y)‖ = 1` the first integral is just `∫‖u‖`, while
the second is controlled by `∫‖u''‖`, `2πN ∫‖u'‖` and `(2πN)² ∫‖u‖`.

The pointwise Leibniz bound on the second derivative and the derivative of `e(c·)` are provided by
`Work.KMTAreas.A7.varphiNt_bounds`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.varphiNt_bounds

namespace Work.KMTPlan.A6

open MeasureTheory

/-! ## Compact support and integrability of the derivatives -/

private lemma hcs_iteratedDeriv (u : ℝ → ℂ) (hcs : HasCompactSupport u) (m : ℕ) (hm : m ≤ 2) :
    HasCompactSupport (iteratedDeriv m u) := by
  interval_cases m
  · rw [iteratedDeriv_zero]; exact hcs
  · rw [iteratedDeriv_one]; exact hcs.deriv
  · rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    exact hcs.deriv.deriv

private lemma integrable_iteratedDeriv_norm (u : ℝ → ℂ) (hu : ContDiff ℝ 2 u)
    (hcs : HasCompactSupport u) (m : ℕ) (hm : m ≤ 2) :
    Integrable (fun y => ‖iteratedDeriv m u y‖) := by
  have hcont : Continuous (iteratedDeriv m u) :=
    hu.continuous_iteratedDeriv m (by exact_mod_cast hm)
  exact (hcont.integrable_of_hasCompactSupport (hcs_iteratedDeriv u hcs m hm)).norm

/-- The modulated bump `u · e(c·)` still has compact support (its support is contained in that
of `u`). -/
private lemma hasCompactSupport_modulated (u : ℝ → ℂ) (c : ℝ) (hcs : HasCompactSupport u) :
    HasCompactSupport (fun ξ : ℝ => u ξ * Work.KMTAreas.A7.ee (c * ξ)) := by
  have h : HasCompactSupport (u * fun ξ : ℝ => Work.KMTAreas.A7.ee (c * ξ)) :=
    hcs.mul_right (f' := fun ξ : ℝ => Work.KMTAreas.A7.ee (c * ξ))
  have heq : (u * fun ξ : ℝ => Work.KMTAreas.A7.ee (c * ξ)) =
      (fun ξ : ℝ => u ξ * Work.KMTAreas.A7.ee (c * ξ)) := rfl
  rwa [heq] at h

/-- The modulus of the second derivative of the modulated bump is integrable. -/
private lemma integrable_modulated_deriv_two (u : ℝ → ℂ) (c : ℝ) (hu : ContDiff ℝ 2 u)
    (hcs : HasCompactSupport u) :
    Integrable (fun y => ‖iteratedDeriv 2 (fun ξ : ℝ => u ξ * Work.KMTAreas.A7.ee (c * ξ)) y‖) := by
  have hF_cd : ContDiff ℝ 2 (fun ξ : ℝ => u ξ * Work.KMTAreas.A7.ee (c * ξ)) :=
    hu.mul (Work.KMTAreas.A7.contDiff_ee_const_mul 2 c)
  have hF_cont : Continuous (iteratedDeriv 2 (fun ξ : ℝ => u ξ * Work.KMTAreas.A7.ee (c * ξ))) :=
    hF_cd.continuous_iteratedDeriv 2 le_rfl
  have hF_hcs :
      HasCompactSupport (iteratedDeriv 2 (fun ξ : ℝ => u ξ * Work.KMTAreas.A7.ee (c * ξ))) := by
    have h2 : iteratedDeriv 2 (fun ξ : ℝ => u ξ * Work.KMTAreas.A7.ee (c * ξ)) =
        deriv (deriv (fun ξ : ℝ => u ξ * Work.KMTAreas.A7.ee (c * ξ))) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [h2]
    exact (hasCompactSupport_modulated u c hcs).deriv.deriv
  exact (hF_cont.integrable_of_hasCompactSupport hF_hcs).norm

/-! ## The uniform bound -/

theorem varphiNt_modulation_bounds (N : ℕ) (u : ℝ → ℂ) (hu : ContDiff ℝ 2 u)
    (hcs : HasCompactSupport u) :
    ∃ S : ℝ, 0 ≤ S ∧ ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      (∫ y, ‖u y * Work.KMTAreas.A7.ee (((N : ℝ) * t) * y)‖ ∂MeasureTheory.volume) ≤ S ∧
      (∫ y, ‖iteratedDeriv 2 (fun ξ : ℝ => u ξ * Work.KMTAreas.A7.ee (((N : ℝ) * t) * ξ)) y‖
        ∂MeasureTheory.volume) ≤ S := by
  set A : ℝ := ∫ y, ‖u y‖ with hA
  set B : ℝ := ∫ y, ‖iteratedDeriv 1 u y‖ with hB
  set C : ℝ := ∫ y, ‖iteratedDeriv 2 u y‖ with hC
  set S : ℝ := A + (2 * (2 * Real.pi * (N : ℝ))) * B
    + (2 * Real.pi * (N : ℝ)) ^ 2 * A + C + 1 with hS
  have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg (fun y => norm_nonneg _)
  have hB0 : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun y => norm_nonneg _)
  have hC0 : 0 ≤ C := by rw [hC]; exact integral_nonneg (fun y => norm_nonneg _)
  have hcoef1 : 0 ≤ 2 * (2 * Real.pi * (N : ℝ)) := by positivity
  have hcoef2 : 0 ≤ (2 * Real.pi * (N : ℝ)) ^ 2 := by positivity
  have hT1 : 0 ≤ (2 * (2 * Real.pi * (N : ℝ))) * B := mul_nonneg hcoef1 hB0
  have hT2 : 0 ≤ (2 * Real.pi * (N : ℝ)) ^ 2 * A := mul_nonneg hcoef2 hA0
  refine ⟨S, ?_, ?_⟩
  · rw [hS]; linarith
  · intro t ht
    refine ⟨?_, ?_⟩
    · have hcongr : (fun y => ‖u y * Work.KMTAreas.A7.ee (((N : ℝ) * t) * y)‖) =
          fun y => ‖u y‖ := by
        funext y
        rw [norm_mul, Work.KMTAreas.A7.norm_ee, mul_one]
      rw [hcongr, ← hA, hS]
      linarith
    · have ht0 : 0 ≤ t := le_trans (by norm_num) ht.1
      have hcle : |(N : ℝ) * t| ≤ (N : ℝ) := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N), abs_of_nonneg ht0]
        exact mul_le_of_le_one_right (Nat.cast_nonneg N) ht.2
      have hpt : ∀ y, ‖iteratedDeriv 2
            (fun ξ : ℝ => u ξ * Work.KMTAreas.A7.ee (((N : ℝ) * t) * ξ)) y‖ ≤
          ‖iteratedDeriv 2 u y‖ + (2 * (2 * Real.pi * (N : ℝ))) * ‖iteratedDeriv 1 u y‖
            + (2 * Real.pi * (N : ℝ)) ^ 2 * ‖u y‖ := by
        intro y
        have h := Work.KMTAreas.A7.norm_iteratedDeriv_two_mul_ee_le u ((N : ℝ) * t) hu y
        have hshape : (u * fun ξ : ℝ => Work.KMTAreas.A7.ee (((N : ℝ) * t) * ξ)) =
            (fun ξ : ℝ => u ξ * Work.KMTAreas.A7.ee (((N : ℝ) * t) * ξ)) := rfl
        rw [hshape] at h
        have h1 : 2 * (2 * Real.pi * |(N : ℝ) * t|) * ‖iteratedDeriv 1 u y‖ ≤
            (2 * (2 * Real.pi * (N : ℝ))) * ‖iteratedDeriv 1 u y‖ := by gcongr
        have h2 : (2 * Real.pi * |(N : ℝ) * t|) ^ 2 * ‖u y‖ ≤
            (2 * Real.pi * (N : ℝ)) ^ 2 * ‖u y‖ := by gcongr
        linarith
      have hI1 : Integrable (fun y => ‖iteratedDeriv 2 u y‖) :=
        integrable_iteratedDeriv_norm u hu hcs 2 le_rfl
      have hI2 : Integrable (fun y => (2 * (2 * Real.pi * (N : ℝ))) *
          ‖iteratedDeriv 1 u y‖) :=
        (integrable_iteratedDeriv_norm u hu hcs 1 (by norm_num)).const_mul _
      have hI3 : Integrable (fun y => (2 * Real.pi * (N : ℝ)) ^ 2 * ‖u y‖) :=
        (integrable_iteratedDeriv_norm u hu hcs 0 (by norm_num)).const_mul _
      have hI12 : Integrable (fun y => ‖iteratedDeriv 2 u y‖ +
          (2 * (2 * Real.pi * (N : ℝ))) * ‖iteratedDeriv 1 u y‖) := hI1.add hI2
      have hLint : Integrable (fun y => ‖iteratedDeriv 2
          (fun ξ : ℝ => u ξ * Work.KMTAreas.A7.ee (((N : ℝ) * t) * ξ)) y‖) :=
        integrable_modulated_deriv_two u ((N : ℝ) * t) hu hcs
      have hmono := integral_mono hLint (hI12.add hI3) hpt
      have heq : (∫ y, ‖iteratedDeriv 2 u y‖
            + (2 * (2 * Real.pi * (N : ℝ))) * ‖iteratedDeriv 1 u y‖
            + (2 * Real.pi * (N : ℝ)) ^ 2 * ‖u y‖)
          = C + (2 * (2 * Real.pi * (N : ℝ))) * B + (2 * Real.pi * (N : ℝ)) ^ 2 * A := by
        rw [integral_add hI12 hI3, integral_add hI1 hI2, integral_const_mul, integral_const_mul,
          ← hA, ← hB, ← hC]
      have hfinal : (∫ y, ‖iteratedDeriv 2
            (fun ξ : ℝ => u ξ * Work.KMTAreas.A7.ee (((N : ℝ) * t) * ξ)) y‖)
          ≤ C + (2 * (2 * Real.pi * (N : ℝ))) * B + (2 * Real.pi * (N : ℝ)) ^ 2 * A :=
        le_trans hmono (le_of_eq heq)
      rw [hS]
      linarith

end Work.KMTPlan.A6

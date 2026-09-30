import Mathlib
import Submission.Work.BMF.mr_direct.goodSet_bound_range_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral Finset
open scoped BigOperators

/-!
# Per-`j` good-set bound, in the range-generalised setting

For a single `j`, the `L²` norm of `primePoly c K j · remPolyR b P Q K X₁ X₂ j` over a set
`u ⊆ [-S,S]`, where `primePoly` is small (`‖primePoly c K j t‖ ≤ e^{-αj/K}` for `t ∈ u`),
is bounded by `C_W (2S + winHi + 1) e^{-2αj/K} winE`.

The proof is the mean value (Montgomery–Vaughan) estimate `window_mean_value` applied to the
window `[winLo K X₁ j, winHi K X₂ j]` of the remainder polynomial, combined with the trivial
pointwise bound coming from the hypothesis on `primePoly`.
-/

theorem goodSet_range_perj_bound :
    ∃ C_W : ℝ, 0 < C_W ∧
      ∀ (X₁ X₂ K P Q S α : ℝ) (b c : ℕ → ℂ) (u : Set ℝ) (j : ℕ),
        0 < X₁ → 0 ≤ S → 0 < α → u ⊆ Set.Icc (-S) S →
        (∀ t ∈ u, ‖Work.BMF.mrDirect.primePoly c K j t‖ ≤
            Real.exp (-(α * (j : ℝ) / K))) →
        ∫ t in u, ‖Work.BMF.mrDirect.primePoly c K j t *
              Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2
          ≤ C_W * (2 * S + (Work.BMF.mr_direct.winHi K X₂ j + 1)) *
              (Real.exp (-(2 * α * (j : ℝ) / K)) *
                Work.BMF.mr_direct.winE b P Q K X₁ X₂ j) := by
  obtain ⟨C, hCpos, hC⟩ := window_mean_value
  refine ⟨C, hCpos, ?_⟩
  intro X₁ X₂ K P Q S α b c u j hX1 hS _hα hu hbound
  -- notation
  set E : ℝ := Real.exp (-(2 * α * (j : ℝ) / K)) with hE
  set d : ℕ → ℂ := fun m =>
    b m * ((((Work.BMF.mrDirect.omegaCount P Q m : ℕ) + 1 : ℕ)) : ℂ)⁻¹ with hd
  have hEnn : 0 ≤ E := by rw [hE]; positivity
  have hApos : 0 < winLo K X₁ j := mul_pos hX1 (Real.exp_pos _)
  have hcontRP : Continuous fun t : ℝ => Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t :=
    continuous_remPolyR b P Q K X₁ X₂ j hX1
  have hcontPP : Continuous fun t : ℝ => Work.BMF.mrDirect.primePoly c K j t :=
    continuous_primePoly c K j
  -- the pointwise bound on `u`
  have hpoint : ∀ t ∈ u, ‖Work.BMF.mrDirect.primePoly c K j t *
        Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2
      ≤ E * ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 := by
    intro t ht
    have h1 : ‖Work.BMF.mrDirect.primePoly c K j t‖ ≤ Real.exp (-(α * (j : ℝ) / K)) :=
      hbound t ht
    have h2 : ‖Work.BMF.mrDirect.primePoly c K j t‖ ^ 2
        ≤ (Real.exp (-(α * (j : ℝ) / K))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (Real.exp (-(α * (j : ℝ) / K))) ^ 2 = E := by
      rw [hE, sq, ← Real.exp_add]
      congr 1
      ring
    rw [h3] at h2
    calc ‖Work.BMF.mrDirect.primePoly c K j t *
            Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2
        = ‖Work.BMF.mrDirect.primePoly c K j t‖ ^ 2 *
            ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 := by
          rw [norm_mul, mul_pow]
      _ ≤ E * ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  -- step 1: monotonicity of the set integral
  have hstep2 : ∫ t in u, ‖Work.BMF.mrDirect.primePoly c K j t *
        Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2
      ≤ ∫ t in u, E * ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 := by
    refine setIntegral_mono_of_le_on ?_ ?_ ?_ (fun x => sq_nonneg _) hpoint
    · exact ((hcontPP.mul hcontRP).norm.pow 2).measurable
    · exact (continuous_const.mul (hcontRP.norm.pow 2)).measurable
    · exact ((continuous_const.mul (hcontRP.norm.pow 2)).continuousOn.integrableOn_Icc).mono_set hu
  -- step 2: pull the constant out
  have hstep3 : ∫ t in u, E * ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2
      = E * ∫ t in u, ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 :=
    MeasureTheory.integral_const_mul E _
  -- step 3: enlarge `u` to `[-S,S]`
  have hstep5 : ∫ t in u, ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2
      ≤ ∫ t in (-S)..S, ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 :=
    setIntegral_le_intervalIntegral hS hu (hcontRP.norm.pow 2) (fun x _ => sq_nonneg _)
  -- step 4: the mean value bound on the window
  have hWE : (∑ m ∈ Work.BMF.natIcc (winLo K X₁ j) (winHi K X₂ j),
        ‖d m‖ ^ 2 / (m : ℝ) ^ 2) = winE b P Q K X₁ X₂ j := by
    rw [winE]
  have hInt : ∫ t in (-S)..S, ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2
      = ∫ t in (-S)..S, ‖∑ m ∈ Work.BMF.natIcc (winLo K X₁ j) (winHi K X₂ j),
            d m * (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    rw [remPolyR_eq_sum]
  have hstep4 : ∫ t in (-S)..S, ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2
      ≤ C * (2 * S + (winHi K X₂ j + 1)) * winE b P Q K X₁ X₂ j := by
    rw [hInt]
    calc ∫ t in (-S)..S, ‖∑ m ∈ Work.BMF.natIcc (winLo K X₁ j) (winHi K X₂ j),
            d m * (m : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2
        ≤ C * (2 * S + (winHi K X₂ j + 1)) *
            ∑ m ∈ Work.BMF.natIcc (winLo K X₁ j) (winHi K X₂ j),
              ‖d m‖ ^ 2 / (m : ℝ) ^ 2 :=
          hC (winLo K X₁ j) (winHi K X₂ j) S d hApos hS
      _ = C * (2 * S + (winHi K X₂ j + 1)) * winE b P Q K X₁ X₂ j := by rw [hWE]
  -- assembly
  calc ∫ t in u, ‖Work.BMF.mrDirect.primePoly c K j t *
        Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2
      ≤ ∫ t in u, E * ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 := hstep2
    _ = E * ∫ t in u, ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 := hstep3
    _ ≤ E * ∫ t in (-S)..S, ‖Work.BMF.mrDirect.remPolyR b P Q K X₁ X₂ j t‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hstep5 hEnn
    _ ≤ E * (C * (2 * S + (winHi K X₂ j + 1)) * winE b P Q K X₁ X₂ j) :=
        mul_le_mul_of_nonneg_left hstep4 hEnn
    _ = C * (2 * S + (winHi K X₂ j + 1)) *
          (Real.exp (-(2 * α * (j : ℝ) / K)) * winE b P Q K X₁ X₂ j) := by
        rw [hE]; ring

end Work.BMF.mr_direct

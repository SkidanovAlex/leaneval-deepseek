import Mathlib
import Submission.Work.FIArea4.Vflip.sep_defs

open MeasureTheory
open scoped FourierTransform

namespace Work.FIArea4.Vflip

/-- **Decay of the critical-line Mellin transform `sepG ψ`.**

`sepG ψ t = 𝓕 (fun u => ψ (Real.exp u)) t` is the Mellin transform of `ψ` on the critical line,
expressed as the Fourier transform of `ψ(e^·)`.  If `ψ` is smooth and supported in `[1/2, 5/2]`
(as in the Friedlander–Iwaniec majorant), then `sepG ψ` decays faster than any polynomial; here:
there is `C > 0` with `‖sepG ψ t‖ ≤ C (1+|t|)^{-4}` for all `t`.

Suggested route: `u ↦ ψ (Real.exp u)` is `C^∞` with compact support (supported in
`[Real.log (1/2), Real.log (5/2)]`), hence has temperate decay, so its Fourier transform is
integrable/Schwartz; the stated bound follows from `HasCompactSupport.toSchwartzMap` together with
`SchwartzMap.decay` (or from `Commons.Analysis.Fourier.fourierTransform_iteratedDeriv_decay`, which
gives `C/|t|^j` for `t ≠ 0`, combined with the trivial bound `‖𝓕 f t‖ ≤ ∫ ‖f‖` for `|t| ≤ 1`). -/
theorem sepG_decay {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsupp : ∀ y : ℝ, (y ≤ 1 / 2 ∨ 5 / 2 ≤ y) → ψ y = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖Work.FIArea4.Vflip.sepG ψ t‖ ≤ C * (1 + |t|) ^ (-(4 : ℝ)) := by
  -- `f u = ψ (e ^ u)` is the function whose Fourier transform is `sepG ψ`.
  set f : ℝ → ℂ := fun u => (ψ (Real.exp u) : ℂ) with hf_def
  -- `f` is smooth ...
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f := by
    rw [hf_def]
    exact Complex.ofRealCLM.contDiff.comp (hψ.comp Real.contDiff_exp)
  -- ... and compactly supported, with support in `[log (1/2), log (5/2)]`.
  have hf_supp : HasCompactSupport f := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (Real.log (1 / 2)) (Real.log (5 / 2))) isCompact_Icc ?_
    rw [Function.support_subset_iff]
    intro u hu
    rw [Set.mem_Icc]
    refine ⟨?_, ?_⟩
    · by_contra hcon
      rw [not_le] at hcon
      have hlt : Real.exp u < 1 / 2 := by
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]
        exact (Real.exp_lt_exp).mpr hcon
      exact hu (by rw [hf_def]; simp [hsupp (Real.exp u) (Or.inl hlt.le)])
    · by_contra hcon
      rw [not_le] at hcon
      have hlt : 5 / 2 < Real.exp u := by
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 5 / 2)]
        exact (Real.exp_lt_exp).mpr hcon
      exact hu (by rw [hf_def]; simp [hsupp (Real.exp u) (Or.inr hlt.le)])
  -- Package `f` as a Schwartz function.
  set F : SchwartzMap ℝ ℂ := hf_supp.toSchwartzMap hf_smooth with hF_def
  have hFcoe : (F : ℝ → ℂ) = f := rfl
  -- Its Fourier transform `G = 𝓕 F` is again a Schwartz function.
  set G : SchwartzMap ℝ ℂ := 𝓕 F with hG_def
  have hGt : ∀ t : ℝ, (G t : ℂ) = Work.FIArea4.Vflip.sepG ψ t := by
    intro t
    rw [hG_def, SchwartzMap.fourier_coe, hFcoe, hf_def]
    rfl
  -- The Schwartz seminorm controlling `(1+|t|)^4 ‖G t‖`.
  set S : ℝ := ((Finset.Iic ((4 : ℕ), (0 : ℕ))).sup
    (fun m => SchwartzMap.seminorm ℂ m.1 m.2) G) with hS_def
  refine ⟨max (2 ^ 4 * S) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun t => ?_⟩
  have hkey := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
    (m := ((4 : ℕ), (0 : ℕ))) (k := 4) (n := 0) le_rfl le_rfl G t
  rw [norm_iteratedFDeriv_zero] at hkey
  simp only [Real.norm_eq_abs] at hkey
  rw [← hS_def] at hkey
  have hrpow : (1 + |t|) ^ (-(4 : ℝ)) = ((1 + |t|) ^ 4)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
    simp
  have step1 : ‖G t‖ ≤ (2 ^ 4 * S) * ((1 + |t|) ^ 4)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    rw [mul_comm]
    exact hkey
  calc ‖Work.FIArea4.Vflip.sepG ψ t‖ = ‖G t‖ := by rw [← hGt t]
    _ ≤ (2 ^ 4 * S) * ((1 + |t|) ^ 4)⁻¹ := step1
    _ ≤ max (2 ^ 4 * S) 1 * ((1 + |t|) ^ 4)⁻¹ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ = max (2 ^ 4 * S) 1 * (1 + |t|) ^ (-(4 : ℝ)) := by rw [hrpow]

end Work.FIArea4.Vflip

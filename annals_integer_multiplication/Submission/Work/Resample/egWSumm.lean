import Mathlib
import Submission.Work.Resample.sliceB1defs
import Submission.Work.Resample.buErow
import Submission.Work.ResMath.resE_row

/-!
# Summability of the Gaussian weight series `Σ_h egW s t α ℓ h · u (ℓ+h)`

`egW s t α ℓ h = exp (-(π α² (((t h)/s + β_ℓ)² - β_{ℓ+h}²)))` is the true real weight of the
shift `h` in row `ℓ` of the resampling map `E` (paper: Harvey–van der Hoeven, *Integer
multiplication in time* `O(n log n)`, Annals 193 (2021), §4.2).  This file proves that the row
series of `E` — and its absolute-value series — converge, under the *bare* hypotheses of the
paper's setting (`0 < s`, `s < t`, `0 < α`); no fixed-point parameter `p` or size constraint is
needed, only the elementary decay estimate

  `|egW s t α ℓ h| ≤ exp (-(π α² / (2 s)) h²)`   (`egW_gaussBound_aux`),

obtained from `Work.ResMath.quad_ineq` together with `t/s - 1 ≥ 1/s` and
`(|h| - 1/2)² ≥ h²/4` for `|h| ≥ 1`.  Comparison with the theta series
`Work.ResMath.summable_exp_neg_mul_sq_int` gives absolute summability, and the factor
`u : Fin s → ℂ` is harmless since its domain is finite.
-/

namespace Work.Resample

/-- Summability of `h ↦ (f h : ℂ) * u (g h)` when `∑ |f h|` converges and `u` has finite domain
(so `u` is bounded in norm).  Reduces the row series of `E` to the absolute summability of the
Gaussian weights. -/
theorem summable_ofReal_mul_comp (s : ℕ) (u : Fin s → ℂ) (g : ℤ → Fin s) (f : ℤ → ℝ)
    (hf : Summable (fun h : ℤ => |f h|)) :
    Summable (fun h : ℤ => ((f h : ℝ) : ℂ) * u (g h)) := by
  set C : ℝ := ∑ k : Fin s, ‖u k‖ with hC
  have hbound : ∀ k : Fin s, ‖u k‖ ≤ C := fun k =>
    Finset.single_le_sum (fun i _ => norm_nonneg _) (Finset.mem_univ k)
  refine Summable.of_norm_bounded (g := fun h : ℤ => C * |f h|) (hf.mul_left C) ?_
  intro h
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |f h| * ‖u (g h)‖ ≤ |f h| * C :=
        mul_le_mul_of_nonneg_left (hbound (g h)) (abs_nonneg _)
    _ = C * |f h| := by ring

/-- Pointwise Gaussian decay of the weights `egW`, with the (deliberately lossy) rate
`π α² / (2 s)`: with `(t h)/s + β_ℓ = x`, `β_{ℓ+h} = y` one has
`egW = exp (-(π α² (x² - y²)))`, and `x² - y² ≥ h²/(2s)` because
`x² - y² ≥ 2 (t/s - 1) (|h| - 1/2)²` (`Work.ResMath.quad_ineq`),
`t/s - 1 ≥ 1/s` (as `t ≥ s+1`) and `(|h| - 1/2)² ≥ h²/4` (as `|h| ≥ 1`; for `h = 0` both
sides of the bound equal `1`). -/
theorem egW_gaussBound_aux (s t α : ℕ) (hs : 0 < s) (hst : s < t) (hα : 0 < α) (ℓ : Fin s)
    (h : ℤ) :
    |Work.Resample.egW s t α (ℓ : ℤ) h| ≤
      Real.exp (-(Real.pi * (α : ℝ) ^ 2 / (2 * (s : ℝ))) * (h : ℝ) ^ 2) := by
  rcases eq_or_ne h 0 with rfl | hh
  · have hz : Work.Resample.egW s t α (ℓ : ℤ) 0 = 1 := by
      rw [Work.Resample.egW]
      simp
    rw [hz, abs_one]
    simp
  · have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
    have hm1 : (1 : ℝ) ≤ |(h : ℝ)| := by
      have : (1 : ℤ) ≤ |h| := Int.one_le_abs hh
      rw [← Int.cast_abs]; exact_mod_cast this
    set m : ℝ := |(h : ℝ)| with hmdef
    set x : ℝ := (t : ℝ) * (h : ℝ) / (s : ℝ) + Work.ResMath.betaI s t (ℓ : ℤ) with hxdef
    set y : ℝ := Work.ResMath.betaI s t ((ℓ : ℤ) + h) with hydef
    have hts : (s : ℝ) + 1 ≤ (t : ℝ) := by
      have : s + 1 ≤ t := hst
      exact_mod_cast this
    have hθ1 : (1 : ℝ) ≤ (t : ℝ) - (s : ℝ) := by linarith
    have hθ : (1 : ℝ) / (s : ℝ) ≤ (t : ℝ) / (s : ℝ) - 1 := by
      have he : (t : ℝ) / (s : ℝ) - 1 = ((t : ℝ) - (s : ℝ)) / (s : ℝ) := by
        field_simp
      rw [he]
      exact div_le_div_of_nonneg_right hθ1 (le_of_lt hsR)
    have hquad := Work.ResMath.quad_ineq s t hs hst ℓ h hh
    have hquad' : 2 * ((t : ℝ) / (s : ℝ) - 1) * (m - 1 / 2) ^ 2 ≤ x ^ 2 - y ^ 2 := by
      simpa [x, y, m, hmdef, hxdef, hydef] using hquad
    have hA1 : 2 * ((1 : ℝ) / (s : ℝ)) * (m - 1 / 2) ^ 2
        ≤ 2 * ((t : ℝ) / (s : ℝ) - 1) * (m - 1 / 2) ^ 2 :=
      mul_le_mul_of_nonneg_right
        (by linarith : 2 * ((1 : ℝ) / (s : ℝ)) ≤ 2 * ((t : ℝ) / (s : ℝ) - 1)) (sq_nonneg _)
    have hbtm : m ^ 2 ≤ 2 * (s : ℝ) * (2 * ((1 : ℝ) / (s : ℝ)) * (m - 1 / 2) ^ 2) := by
      have hmul : 2 * (s : ℝ) * (2 * ((1 : ℝ) / (s : ℝ)) * (m - 1 / 2) ^ 2) = 4 * (m - 1 / 2) ^ 2 := by
        field_simp
        ring
      rw [hmul]
      nlinarith [hm1, mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * m - 1)
        (by linarith : (0 : ℝ) ≤ m - 1)]
    have hbound2 : (h : ℝ) ^ 2 ≤ 2 * (s : ℝ) * (x ^ 2 - y ^ 2) := by
      have h1 : (h : ℝ) ^ 2 = m ^ 2 := by rw [hmdef, sq_abs]
      rw [h1]
      calc m ^ 2 ≤ 2 * (s : ℝ) * (2 * ((1 : ℝ) / (s : ℝ)) * (m - 1 / 2) ^ 2) := hbtm
        _ ≤ 2 * (s : ℝ) * (x ^ 2 - y ^ 2) :=
            mul_le_mul_of_nonneg_left (le_trans hA1 hquad') (by positivity)
    have hgoal : Real.pi * (α : ℝ) ^ 2 / (2 * (s : ℝ)) * (h : ℝ) ^ 2
        ≤ Real.pi * (α : ℝ) ^ 2 * (x ^ 2 - y ^ 2) := by
      have h1 : Real.pi * (α : ℝ) ^ 2 / (2 * (s : ℝ)) * (h : ℝ) ^ 2 =
          Real.pi * (α : ℝ) ^ 2 * ((h : ℝ) ^ 2 / (2 * (s : ℝ))) := by ring
      rw [h1]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (s : ℝ))]
      linarith [hbound2]
    have hW : Work.Resample.egW s t α (ℓ : ℤ) h =
        Real.exp (-(Real.pi * (α : ℝ) ^ 2 * (x ^ 2 - y ^ 2))) := by
      rw [Work.Resample.egW, ← hxdef, ← hydef]
    rw [hW, abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_exp.mpr
    linarith [hgoal]

theorem egWSumm (s t α : ℕ) (hs : 0 < s) (hst : s < t) (hα : 0 < α) (ℓ : Fin s) (u : Fin s → ℂ) :
    Summable (fun h : ℤ => ((Work.Resample.egW s t α (ℓ : ℤ) h : ℝ) : ℂ) * u (Work.Resample.egIdx s hs ((ℓ : ℤ) + h))) ∧
    Summable (fun h : ℤ => |Work.Resample.egW s t α (ℓ : ℤ) h|) := by
  have hc : 0 < Real.pi * (α : ℝ) ^ 2 / (2 * (s : ℝ)) := by
    have hsR : (0 : ℝ) < s := by exact_mod_cast hs
    have hαR : (0 : ℝ) < α := by exact_mod_cast hα
    positivity
  have hsecond : Summable (fun h : ℤ => |Work.Resample.egW s t α (ℓ : ℤ) h|) := by
    refine Summable.of_norm_bounded (g := fun h : ℤ =>
      Real.exp (-(Real.pi * (α : ℝ) ^ 2 / (2 * (s : ℝ))) * (h : ℝ) ^ 2))
      (Work.ResMath.summable_exp_neg_mul_sq_int hc) ?_
    intro h
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact egW_gaussBound_aux s t α hs hst hα ℓ h
  exact ⟨summable_ofReal_mul_comp s u (fun h => Work.Resample.egIdx s hs ((ℓ : ℤ) + h))
    (fun h => Work.Resample.egW s t α (ℓ : ℤ) h) hsecond, hsecond⟩

end Work.Resample

import Mathlib
import Submission.Work.CKFinal.EngineDefs
import Submission.Work.CKFinal.scale_bound_strip
import Submission.Work.CKFinal.shift_bounds_strip

namespace Work.CKFinal

noncomputable section

/-!
### Constants in the strip bounds for `shiftB` and `shiftA`

`strip_constants` records only that the constants in the strip bounds for
`shiftB f = f(τ+1) - f τ` and `shiftA f = f τ - τ (f(τ+1) - f τ)` depend on `C` and `N`
alone.  The two estimates needed are proved separately and are reused here:

* `Work.CKFinal.scale_bound_strip` : on the strip `im τ ≥ 3/2` the growth hypothesis
  `C * scale τ ^ N` is dominated by `K * (1 + ‖τ‖) ^ A`;
* `Work.CKFinal.shift_bounds_strip` : the two shifts gain at most a factor `2 ^ A + 1`
  (`shiftB`) resp. one extra power of `1 + ‖τ‖` (`shiftA`) over the bound for `f`.

What remains is the bookkeeping on the compact piece `im τ = 3/2`, `|re τ| ≤ 1/2` of the
strip, where `1 + ‖τ‖ ≤ 3`.
-/

section Helpers

open UpperHalfPlane

/-- On the compact piece `im τ = 3/2`, `|re τ| ≤ 1/2` of the strip we have `‖τ‖ ≤ 2`. -/
private lemma norm_coe_le_two (τ : ℍ) (him : τ.im = 3 / 2) (hre : |τ.re| ≤ 1 / 2) :
    ‖(τ : ℂ)‖ ≤ 2 := by
  have h := Complex.norm_le_abs_re_add_abs_im (τ : ℂ)
  rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, him,
      abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at h
  linarith

end Helpers

theorem strip_constants (C N : ℝ) :
    (∃ Ke A : ℝ, 0 ≤ Ke ∧ 0 ≤ A ∧ ∀ (f : UpperHalfPlane → ℂ),
        (∀ τ : UpperHalfPlane, ‖f τ‖ ≤ C * (Work.Kernels.scale τ) ^ N) →
        ∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im →
          ‖Work.CKFinal.shiftB f τ‖ ≤ Ke * (1 + ‖(τ : ℂ)‖) ^ A) ∧
    (∃ Ke A : ℝ, 0 ≤ Ke ∧ 0 ≤ A ∧ ∀ (f : UpperHalfPlane → ℂ),
        (∀ τ : UpperHalfPlane, ‖f τ‖ ≤ C * (Work.Kernels.scale τ) ^ N) →
        ∀ τ : UpperHalfPlane, 3 / 2 ≤ τ.im →
          ‖Work.CKFinal.shiftA f τ‖ ≤ Ke * (1 + ‖(τ : ℂ)‖) ^ A) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ (f : UpperHalfPlane → ℂ),
        (∀ τ : UpperHalfPlane, ‖f τ‖ ≤ C * (Work.Kernels.scale τ) ^ N) →
        ∀ τ : UpperHalfPlane, τ.im = 3 / 2 → |τ.re| ≤ 1 / 2 → ‖Work.CKFinal.shiftB f τ‖ ≤ M) ∧
    (∃ M : ℝ, 0 ≤ M ∧ ∀ (f : UpperHalfPlane → ℂ),
        (∀ τ : UpperHalfPlane, ‖f τ‖ ≤ C * (Work.Kernels.scale τ) ^ N) →
        ∀ τ : UpperHalfPlane, τ.im = 3 / 2 → |τ.re| ≤ 1 / 2 → ‖Work.CKFinal.shiftA f τ‖ ≤ M) := by
  obtain ⟨K, A, hK, hA, hscale⟩ := scale_bound_strip C N
  have hK2 : 0 ≤ K * (2 ^ A + 1) := mul_nonneg hK (by positivity)
  have hMt : 0 ≤ K * (2 ^ A + 1) * 3 ^ A := mul_nonneg hK2 (Real.rpow_nonneg (by norm_num) A)
  have hMtA : 0 ≤ K * (2 ^ A + 1) * 3 ^ (A + 1) :=
    mul_nonneg hK2 (Real.rpow_nonneg (by norm_num) (A + 1))
  refine ⟨⟨K * (2 ^ A + 1), A, hK2, hA, ?_⟩, ⟨K * (2 ^ A + 1), A + 1, hK2, by linarith, ?_⟩,
    ⟨K * (2 ^ A + 1) * 3 ^ A, hMt, ?_⟩, ⟨K * (2 ^ A + 1) * 3 ^ (A + 1), hMtA, ?_⟩⟩
  · intro f hf τ hτ
    exact (shift_bounds_strip K A hK hA f
      (fun σ hσ => le_trans (hf σ) (hscale σ hσ))).1 τ hτ
  · intro f hf τ hτ
    exact (shift_bounds_strip K A hK hA f
      (fun σ hσ => le_trans (hf σ) (hscale σ hσ))).2 τ hτ
  · intro f hf τ him hre
    have hτ : 3 / 2 ≤ τ.im := by linarith
    have hb := (shift_bounds_strip K A hK hA f
      (fun σ hσ => le_trans (hf σ) (hscale σ hσ))).1 τ hτ
    have hp : (1 + ‖(τ : ℂ)‖) ^ A ≤ 3 ^ A :=
      Real.rpow_le_rpow (by positivity) (by linarith [norm_coe_le_two τ him hre]) hA
    calc ‖Work.CKFinal.shiftB f τ‖ ≤ K * (2 ^ A + 1) * (1 + ‖(τ : ℂ)‖) ^ A := hb
      _ ≤ K * (2 ^ A + 1) * 3 ^ A := mul_le_mul_of_nonneg_left hp hK2
  · intro f hf τ him hre
    have hτ : 3 / 2 ≤ τ.im := by linarith
    have hb := (shift_bounds_strip K A hK hA f
      (fun σ hσ => le_trans (hf σ) (hscale σ hσ))).2 τ hτ
    have hp : (1 + ‖(τ : ℂ)‖) ^ (A + 1) ≤ 3 ^ (A + 1) :=
      Real.rpow_le_rpow (by positivity) (by linarith [norm_coe_le_two τ him hre]) (by linarith)
    calc ‖Work.CKFinal.shiftA f τ‖ ≤ K * (2 ^ A + 1) * (1 + ‖(τ : ℂ)‖) ^ (A + 1) := hb
      _ ≤ K * (2 ^ A + 1) * 3 ^ (A + 1) := mul_le_mul_of_nonneg_left hp hK2

end

end Work.CKFinal

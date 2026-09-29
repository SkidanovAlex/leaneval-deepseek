import Mathlib
import Submission.Work.Resample.sliceB1defs

namespace Work.Resample

/-- A tail bound on the Gaussian weights controls the norm of the corresponding tail of the
resampling sum applied to a bounded vector: the `h`-tail of `Σ_h egW(ℓ,h)·u(ℓ+h)`, restricted
to `|h| > m`, is bounded by `3/2^p` whenever the absolute tail of the weights is. -/
theorem egWtailNorm (s t α p : ℕ) (hs : 0 < s) (m : ℕ) (ℓ : Fin s) (u : Fin s → ℂ)
    (hgsumm : Summable (fun h : ℤ => if m < h.natAbs then |Work.Resample.egW s t α (ℓ : ℤ) h| else 0))
    (htail : ∑' h : ℤ, (if m < h.natAbs then |Work.Resample.egW s t α (ℓ : ℤ) h| else 0) ≤ 3 / (2 : ℝ) ^ p)
    (hu : ∀ j, ‖u j‖ ≤ 1) :
    ‖∑' h : ℤ, (if m < h.natAbs then ((Work.Resample.egW s t α (ℓ : ℤ) h : ℝ) : ℂ)
      * u (Work.Resample.egIdx s hs ((ℓ : ℤ) + h)) else 0)‖ ≤ 3 / (2 : ℝ) ^ p := by
  set g : ℤ → ℝ := fun h => if m < h.natAbs then |Work.Resample.egW s t α (ℓ : ℤ) h| else 0 with hg
  set f : ℤ → ℂ := fun h => if m < h.natAbs then ((Work.Resample.egW s t α (ℓ : ℤ) h : ℝ) : ℂ)
      * u (Work.Resample.egIdx s hs ((ℓ : ℤ) + h)) else 0 with hf
  have hgs : Summable g := by rw [hg]; exact hgsumm
  have hbound : ∀ h, ‖f h‖ ≤ g h := by
    intro h
    rw [hf, hg]
    simp only
    split_ifs with hc
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (hu _)
    · simp
  have hfs : Summable f := Summable.of_norm_bounded hgs hbound
  have hns : Summable (fun h => ‖f h‖) :=
    Summable.of_nonneg_of_le (fun h => norm_nonneg _) hbound hgs
  calc ‖∑' h, f h‖ ≤ ∑' h, ‖f h‖ := norm_tsum_le_tsum_norm hns
    _ ≤ ∑' h, g h := hns.tsum_le_tsum hbound hgs
    _ ≤ 3 / (2 : ℝ) ^ p := by rw [hg]; exact htail

end Work.Resample

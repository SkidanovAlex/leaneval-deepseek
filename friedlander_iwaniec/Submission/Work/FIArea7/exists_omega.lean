import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Work.FIArea7.FIsymbols

namespace Work.FIArea7

/-- **Existence of the `ω` of *FI* (19.1)/(19.7)/(22.7)** — the square root of `-1` modulo `|w|²`
attached to a primary primitive `w`:

  `∃ ω : ℤ, ω² + 1 ≡ 0 (mod |w|²)` and `ω·w.re ≡ -w.im (mod |w|²)`.

Take `ω` to be the representative of `-w.im · w.re⁻¹ (mod |w|²)`: `w.re` is invertible modulo
`|w|² = w.re² + w.im²` (as `IsCoprime w.re w.im`), and then
`ω² ≡ w.im²·w.re⁻² ≡ -1` because `w.im² ≡ -w.re² (mod |w|²)`.
Both congruences are the hypotheses of `Work.FIArea7.dirichletSym_eq_jacobiSym_omega` and
`Work.FIArea7.jacobiSym_omega_shift`, which evaluate the Dirichlet symbol in *FI* §22. -/
theorem exists_omega (w : GaussianInt) (hw : Work.FIPlan.IsPrimary w)
    (hcop : IsCoprime w.re w.im) :
    ∃ ω : ℤ, (ω ^ 2 + 1) ≡ 0 [ZMOD ((Work.FIPlan.gnorm w : ℕ) : ℤ)] ∧
      (ω * w.re ≡ -w.im [ZMOD ((Work.FIPlan.gnorm w : ℕ) : ℤ)]) := by
  -- `w.re` is invertible mod `|w|² = w.re² + w.im²`: `IsCoprime w.re (w.re * w.re + w.im ^ 2)`
  -- by `IsCoprime.mul_add_left_right`, then `norm_eq`.
  have hcop' : IsCoprime w.re ((Work.FIPlan.gnorm w : ℕ) : ℤ) := by
    have h2 : IsCoprime w.re (w.im ^ 2) := hcop.pow_right
    have h4 := h2.mul_add_left_right w.re
    have h5 : w.re * w.re + w.im ^ 2 = ((Work.FIPlan.gnorm w : ℕ) : ℤ) := by
      rw [Work.FIArea7.norm_eq]; ring
    rwa [h5] at h4
  -- Bézout: `x * w.re + y * |w|² = 1`; take `ω = -w.im · x`.
  obtain ⟨x, y, hxy⟩ := hcop'
  have hxre : x * w.re = 1 - y * ((Work.FIPlan.gnorm w : ℕ) : ℤ) := by linarith
  refine ⟨-(w.im * x), ?_, ?_⟩
  · -- `ω² + 1 = w.im²x² + 1 ≡ w.im²x² + (x·w.re)² = x²·|w|² ≡ 0`
    have hdvd : ((Work.FIPlan.gnorm w : ℕ) : ℤ) ∣ (-(w.im * x)) ^ 2 + 1 := by
      have hsq : (-(w.im * x)) ^ 2 = (w.im * x) ^ 2 := by ring
      rw [hsq]
      have hA : ((Work.FIPlan.gnorm w : ℕ) : ℤ)
          ∣ (w.im * x) ^ 2 + (x * w.re) ^ 2 := by
        have h : (w.im * x) ^ 2 + (x * w.re) ^ 2
            = ((Work.FIPlan.gnorm w : ℕ) : ℤ) * x ^ 2 := by
          rw [Work.FIArea7.norm_eq]; ring
        rw [h]; exact dvd_mul_right _ _
      have hB : ((Work.FIPlan.gnorm w : ℕ) : ℤ) ∣ 1 - (x * w.re) ^ 2 := by
        refine ⟨y * (1 + x * w.re), ?_⟩
        rw [hxre]; ring
      have hsum := dvd_add hA hB
      have heq : (w.im * x) ^ 2 + (x * w.re) ^ 2 + (1 - (x * w.re) ^ 2)
          = (w.im * x) ^ 2 + 1 := by ring
      rwa [heq] at hsum
    rw [Int.modEq_iff_dvd]
    simpa using dvd_neg.mpr hdvd
  · -- `ω·w.re + w.im = w.im·(1 - x·w.re) ≡ 0`
    rw [Int.modEq_iff_dvd]
    refine ⟨-(w.im * y), ?_⟩
    have hkey : (-(w.im * x)) * w.re
        = -(w.im * (1 - y * ((Work.FIPlan.gnorm w : ℕ) : ℤ))) := by
      rw [neg_mul, mul_assoc, hxre]
    rw [hkey]; ring

end Work.FIArea7

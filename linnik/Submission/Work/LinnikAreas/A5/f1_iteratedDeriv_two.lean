import Mathlib
import Submission.Work.LinnikAreas.A5.Basic

namespace Work.LinnikAreas.A5

/-- `f₁` agrees with `sinh((K-t)λ)` on `(-∞,K)`. -/
private lemma f1_eventuallyEq_sinh (K lam : ℝ) {t : ℝ} (ht : t < K) :
    f1 K lam =ᶠ[nhds t] (fun s : ℝ => Real.sinh ((K - s) * lam)) := by
  filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
  exact f1_of_le hs.le

/-- First derivative of `t ↦ sinh((K-t)λ)`. -/
private lemma deriv_sinh_sub (K lam : ℝ) :
    deriv (fun s : ℝ => Real.sinh ((K - s) * lam))
      = fun s => -lam * Real.cosh ((K - s) * lam) := by
  funext s
  have h1 : HasDerivAt (fun s : ℝ => (K - s) * lam) (-lam) s := by
    have h0 : HasDerivAt (fun s : ℝ => (K - s) * lam) ((0 - 1) * lam) s :=
      ((hasDerivAt_const (x := s) K).sub (hasDerivAt_id s)).mul_const lam
    simpa using h0
  have h : HasDerivAt (fun s : ℝ => Real.sinh ((K - s) * lam))
      (Real.cosh ((K - s) * lam) * (-lam)) s := by
    simpa using h1.sinh
  rw [h.deriv]; ring

/-- Second derivative of `t ↦ sinh((K-t)λ)`. -/
private lemma deriv_deriv_sinh_sub (K lam : ℝ) (t : ℝ) :
    deriv (fun s : ℝ => -lam * Real.cosh ((K - s) * lam)) t
      = lam ^ 2 * Real.sinh ((K - t) * lam) := by
  have h1 : HasDerivAt (fun s : ℝ => (K - s) * lam) (-lam) t := by
    have h0 : HasDerivAt (fun s : ℝ => (K - s) * lam) ((0 - 1) * lam) t :=
      ((hasDerivAt_const (x := t) K).sub (hasDerivAt_id t)).mul_const lam
    simpa using h0
  have hcosh : HasDerivAt (fun s : ℝ => Real.cosh ((K - s) * lam))
      (Real.sinh ((K - t) * lam) * (-lam)) t := by
    simpa using h1.cosh
  have h : HasDerivAt (fun s : ℝ => -lam * Real.cosh ((K - s) * lam))
      (-lam * (Real.sinh ((K - t) * lam) * (-lam))) t := hcosh.const_mul (-lam)
  rw [h.deriv]; ring

/-- The second derivative of HB's test function `f₁` on `(0,K)` is `λ² sinh((K-t)λ)`. -/
theorem f1_iteratedDeriv_two (K lam : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) K) :
    iteratedDeriv 2 (Work.LinnikAreas.A5.f1 K lam) t = lam ^ 2 * Real.sinh ((K - t) * lam) := by
  have hlt : t < K := ht.2
  rw [(f1_eventuallyEq_sinh K lam hlt).iteratedDeriv_eq 2]
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    deriv_sinh_sub, deriv_deriv_sinh_sub]

end Work.LinnikAreas.A5

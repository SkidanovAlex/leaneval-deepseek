import Mathlib

namespace Work.Analysis.Calculus

theorem hasDerivAt_polarMap {f : ℝ → ℝ} {t : ℝ}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Set.Ioo (-1 : ℝ) 1))
    (ht : t ∈ Set.Ioo (-1 : ℝ) 1)
    (hne : t ^ 2 + (f t) ^ 2 ≠ 0) :
    HasDerivAt (fun x : ℝ => x / Real.sqrt (x ^ 2 + (f x) ^ 2))
      (f t * (f t - t * deriv f t) / (Real.sqrt (t ^ 2 + (f t) ^ 2)) ^ 3) t := by
  have hf : HasDerivAt f (deriv f t) t :=
    ((hsm.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds ht)).hasDerivAt
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
    have h : HasDerivAt (id ^ 2 : ℝ → ℝ) (2 * t) t := by simpa using (hasDerivAt_id t).pow 2
    exact h
  have h2 : HasDerivAt (fun x : ℝ => (f x) ^ 2) (2 * (f t * deriv f t)) t := by
    have h : HasDerivAt (f ^ 2 : ℝ → ℝ) (2 * (f t * deriv f t)) t := by
      have hh := hf.pow 2
      simp only [mul_assoc, pow_one, Nat.reduceSub] at hh
      exact hh
    exact h
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2 + (f x) ^ 2)
      (2 * t + 2 * (f t * deriv f t)) t :=
    h1.add h2
  have hsqrt : HasDerivAt (fun x : ℝ => Real.sqrt (x ^ 2 + (f x) ^ 2))
      (1 / (2 * Real.sqrt (t ^ 2 + (f t) ^ 2)) * (2 * t + 2 * (f t * deriv f t))) t :=
    (Real.hasDerivAt_sqrt hne).comp t hsq
  have hsne : Real.sqrt (t ^ 2 + (f t) ^ 2) ≠ 0 := by positivity
  have hfull : HasDerivAt (fun x : ℝ => x / Real.sqrt (x ^ 2 + (f x) ^ 2))
      ((1 * Real.sqrt (t ^ 2 + (f t) ^ 2)
          - t * (1 / (2 * Real.sqrt (t ^ 2 + (f t) ^ 2))
              * (2 * t + 2 * (f t * deriv f t))))
        / (Real.sqrt (t ^ 2 + (f t) ^ 2)) ^ 2) t :=
    (hasDerivAt_id t).div hsqrt hsne
  refine hfull.congr_deriv ?_
  have h0 : 0 ≤ t ^ 2 + (f t) ^ 2 := by positivity
  field_simp
  rw [Real.sq_sqrt h0]
  ring

end Work.Analysis.Calculus

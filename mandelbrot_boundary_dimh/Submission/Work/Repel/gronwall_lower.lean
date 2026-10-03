import Mathlib

namespace Work.Repel

/-- **Grönwall lower bound, differential form.**  If `y` is continuous on `[a,b]` with derivative
`y'` on `(a,b)`, `A` is continuous on `[a,b]` with `A' = K` on `(a,b)` (in the weak `HasDerivAt`
sense, so `K` is an arbitrary choice of a derivative of `A`), and `y' ≥ -K·y` on `(a,b)`, then
`y a · exp(-(A b - A a)) ≤ y b`.

Proof: the function `g t = y t · exp(A t)` has derivative `exp(A t)·(y' t + K t · y t) ≥ 0` on
`(a,b)`, hence is monotone, so `y a · exp(A a) ≤ y b · exp(A b)`; multiply by `exp(-A b) > 0`. -/
theorem gronwall_lower {y y' A K : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hy : ContinuousOn y (Set.Icc a b))
    (hyd : ∀ t ∈ Set.Ioo a b, HasDerivAt y (y' t) t)
    (hA : ContinuousOn A (Set.Icc a b))
    (hAd : ∀ t ∈ Set.Ioo a b, HasDerivAt A (K t) t)
    (hineq : ∀ t ∈ Set.Ioo a b, -(K t) * y t ≤ y' t) :
    y a * Real.exp (-(A b - A a)) ≤ y b := by
  have hderiv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt (fun s => y s * Real.exp (A s)) (Real.exp (A t) * (y' t + K t * y t)) t := by
    intro t ht
    convert (hyd t ht).mul (hAd t ht).exp using 1
    ring
  have hcont : ContinuousOn (fun s => y s * Real.exp (A s)) (Set.Icc a b) :=
    hy.mul (Real.continuous_exp.comp_continuousOn hA)
  have hdiff : DifferentiableOn ℝ (fun s => y s * Real.exp (A s)) (interior (Set.Icc a b)) := by
    intro t ht
    rw [interior_Icc] at ht
    exact (hderiv t ht).differentiableAt.differentiableWithinAt
  have hpos : ∀ t ∈ interior (Set.Icc a b),
      0 ≤ deriv (fun s => y s * Real.exp (A s)) t := by
    intro t ht
    rw [interior_Icc] at ht
    rw [(hderiv t ht).deriv]
    apply mul_nonneg (Real.exp_pos _).le
    nlinarith [hineq t ht]
  have hmono : MonotoneOn (fun s => y s * Real.exp (A s)) (Set.Icc a b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont hdiff hpos
  have hmain : y a * Real.exp (A a) ≤ y b * Real.exp (A b) :=
    hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have h2 := mul_le_mul_of_nonneg_right hmain (Real.exp_pos (-(A b))).le
  calc y a * Real.exp (-(A b - A a))
      = (y a * Real.exp (A a)) * Real.exp (-(A b)) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf
    _ ≤ (y b * Real.exp (A b)) * Real.exp (-(A b)) := h2
    _ = y b := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

end Work.Repel

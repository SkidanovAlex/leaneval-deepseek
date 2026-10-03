import Mathlib
import Submission.Work.Repel.V10.chain_v9_src
import Submission.Work.Repel.V10.lift_dist_half
import Submission.Work.Repel.V10.chain_v9_diff

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

/-- **The derivative of the explicit lift.**

`V.lift j k n u = w_c + n + log (φ₁ u / φ₁ (u_c + k)) / (2πi)` is, as a function of `u`,
a constant plus `log ∘ (φ₁ · / φ₁(u_c + k)) / (2πi)`; the chain rule gives

  `deriv (lift) u = (φ₁' u / φ₁(u_c + k)) / (φ₁ u / φ₁(u_c + k)) / (2πi) = φ₁' u / (φ₁ u · 2πi)`,

whose modulus is `‖φ₁' u‖ / (2π ‖φ₁ u‖)`.  The relevant point is that the ratio
`φ₁ u / φ₁(u_c + k)` lies in the `1/2`-ball around `1` (`phi_div_sub_one_le`), hence in the
slit plane, so `Complex.log` is genuinely differentiable there and `HasDerivAt.clog` applies. -/
theorem lift_deriv (V : Work.Repel.V10) {j : ℕ} {k n : ℤ} (hSm : V.fib j k ⊆ V.Sm1) {u : ℂ}
    (hu : u ∈ V.fib j k) :
    ‖deriv (V.lift j k n) u‖ = ‖deriv V.P₁.φ u‖ / (2 * Real.pi * ‖V.P₁.φ u‖) := by
  have hC : V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) ≠ 0 :=
    V10.phi_ne_zero_of_mem_fib V hSm (V.uc_fib j k)
  have huφ : V.P₁.φ u ≠ 0 := V10.phi_ne_zero_of_mem_fib V hSm hu
  -- the ratio `φ₁ u / φ₁(u_c + k)` is in the `1/2`-ball around `1`, hence in the slit plane
  have hmem : V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    have h1 : ‖V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) - 1‖ ≤ 1 / 2 :=
      V10.phi_div_sub_one_le V hSm hu (V.uc_fib j k)
    have h2 : -(‖V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) - 1‖)
        ≤ (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) - 1).re :=
      (abs_le.mp (Complex.abs_re_le_norm _)).1
    simp only [Complex.sub_re, Complex.one_re] at h2
    linarith
  have hdφ : HasDerivAt V.P₁.φ (deriv V.P₁.φ u) u :=
    (V.P₁.φ_holo.differentiableAt (V.P₁.Dφ_open.mem_nhds (V.Sm1_sub_Dφ (hSm hu)))).hasDerivAt
  have h1 : HasDerivAt (fun u => V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)))
      (deriv V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))) u := hdφ.div_const _
  have h2 : HasDerivAt (fun u => Complex.log (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))))
      ((deriv V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))) /
        (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)))) u := h1.clog hmem
  have h3 := h2.div_const (2 * Real.pi * Complex.I)
  have h4 : HasDerivAt (V.lift j k n)
      (((deriv V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))) /
        (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)))) / (2 * Real.pi * Complex.I)) u := by
    have hsum : HasDerivAt ((fun _ : ℂ => V.wc j k + ((n : ℤ) : ℂ)) +
        fun x => Complex.log (V.P₁.φ x / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))) /
          (2 * Real.pi * Complex.I))
        (0 + ((deriv V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))) /
          (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)))) / (2 * Real.pi * Complex.I)) u :=
      (hasDerivAt_const (x := u) (V.wc j k + ((n : ℤ) : ℂ))).add h3
    have hfun : V.lift j k n = (fun _ : ℂ => V.wc j k + ((n : ℤ) : ℂ)) +
        fun x => Complex.log (V.P₁.φ x / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))) /
          (2 * Real.pi * Complex.I) := by
      ext x
      simp [V10.lift, Pi.add_apply]
    rw [hfun]
    simpa only [zero_add] using hsum
  rw [h4.deriv]
  rw [show (deriv V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ)) /
        (V.P₁.φ u / V.P₁.φ (V.uc j + ((k : ℤ) : ℂ))) / (2 * Real.pi * Complex.I))
      = deriv V.P₁.φ u / V.P₁.φ u / (2 * Real.pi * Complex.I) from by
        field_simp]
  rw [norm_div, norm_div]
  have hA : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hA, div_div]
  ring

end Work.Repel

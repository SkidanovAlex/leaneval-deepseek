import Mathlib
import Submission.Work.BourgainPlan.Oscillation.Lacunary.defs

/-!
# The Poisson kernel on `ℤ` and its Fourier series

`mmClosed ρ i θ = (1-λ)² / (1 - 2λ cos(2πθ) + λ²)` with `λ = lam ρ i = exp(-2πρ^{-i})` is the
closed form of the circle multiplier whose (discrete) convolution kernel is the normalized
Poisson kernel `kap ρ i z = (1-λ)/(1+λ) · λ^{|z|}`.  This file proves the identity

`mmClosed ρ i θ = ∑_{z ∈ ℤ} kap ρ i z · e(2πi z θ)`,

equivalently the classical Poisson-kernel Fourier series
`∑_{z∈ℤ} λ^{|z|} e(2πi z θ) = (1-λ²)/(1 - 2λ cos(2πθ) + λ²)` for `0 ≤ λ < 1`.

The proof splits the `ℤ`-sum at `0` (`tsum_of_nat_of_neg_add_one`), evaluates the two
geometric series `∑_{n≥0} (λ e^{±2πiθ})^n = (1 - λ e^{±2πiθ})⁻¹`, and performs the resulting
algebra with `ξ = λ e^{2πiθ}`, `η = λ e^{-2πiθ}`: `ξη = λ²`, `ξ + η = 2λ cos(2πθ)`.
-/

open scoped BigOperators

namespace Work.BourgainPlan.Oscillation.Lacunary

/-- Algebra of the two geometric series: for `0 ≤ r < 1` and `‖c‖ = 1` with
`c + c⁻¹ = 2 cos φ`,
`(1 - rc)⁻¹ + rc⁻¹ (1 - rc⁻¹)⁻¹ = (1 - r²)/(1 - 2r cos φ + r²)`. -/
theorem geom_pair_eq (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (φ : ℝ) (c : ℂ)
    (hc : ‖c‖ = 1) (hcos : c + c⁻¹ = ((2 * Real.cos φ : ℝ) : ℂ)) :
    (1 - (r:ℂ)*c)⁻¹ + ((r:ℂ)*c⁻¹) * (1 - (r:ℂ)*c⁻¹)⁻¹
      = (((1 - r^2)/(1 - 2*r*Real.cos φ + r^2) : ℝ) : ℂ) := by
  set A : ℂ := (r:ℂ)*c with hA
  set B : ℂ := (r:ℂ)*c⁻¹ with hB
  have hcne : c ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; exact one_ne_zero hc.symm
  have hnA : ‖A‖ = r := by
    rw [hA, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hc, mul_one]
  have hnB : ‖B‖ = r := by
    rw [hB, norm_mul, norm_inv, hc, inv_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
  have h0 : (1 : ℂ) - A ≠ 0 := by
    intro h
    have h3 : (1:ℂ) = A := sub_eq_zero.mp h
    have h4 := congrArg norm h3
    rw [norm_one, hnA] at h4
    exact absurd h4.symm (ne_of_lt hr1)
  have h0' : (1 : ℂ) - B ≠ 0 := by
    intro h
    have h3 : (1:ℂ) = B := sub_eq_zero.mp h
    have h4 := congrArg norm h3
    rw [norm_one, hnB] at h4
    exact absurd h4.symm (ne_of_lt hr1)
  have hAB : A * B = ((r:ℂ))^2 := by
    rw [hA, hB, mul_mul_mul_comm, mul_inv_cancel₀ hcne, mul_one, sq]
  have hAplusB : A + B = (2 * (r:ℂ)) * ((Real.cos φ : ℝ) : ℂ) := by
    rw [hA, hB, ← mul_add, hcos]; push_cast; ring
  have hprod : (1 - A) * (1 - B) = ((1 - 2*r*Real.cos φ + r^2 : ℝ) : ℂ) := by
    have : (1 - A) * (1 - B) = 1 - (A + B) + A*B := by ring
    rw [this, hAplusB, hAB]; push_cast; ring
  have hnum : (1 : ℂ) - A * B = ((1 - r^2 : ℝ) : ℂ) := by
    rw [hAB]; push_cast; ring
  rw [Complex.ofReal_div, ← hnum, ← hprod, div_eq_mul_inv]
  field_simp
  ring

/-- The Fourier series of the Poisson kernel on `ℤ`, in the form `∑_z λ^{|z|} w^z` for a
unimodular `w` whose two-sided character sum is `2 cos φ`. -/
theorem lam_poisson_aux (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (φ : ℝ) (w : ℂ)
    (hwnorm : ‖w‖ = 1) (hwc : w + w⁻¹ = ((2 * Real.cos φ : ℝ) : ℂ)) :
    ∑' z : ℤ, ((r : ℂ) ^ z.natAbs) * w ^ z
      = (((1 - r^2) / (1 - 2*r*Real.cos φ + r^2) : ℝ) : ℂ) := by
  have hξlt : ‖(r:ℂ)*w‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hwnorm, mul_one]
    exact hr1
  have hηlt : ‖(r:ℂ)*w⁻¹‖ < 1 := by
    rw [norm_mul, norm_inv, hwnorm, inv_one, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    exact hr1
  have hfun1 : (fun n : ℕ => (r:ℂ) ^ ((n:ℤ).natAbs) * w ^ (n:ℤ)) = fun n : ℕ => ((r:ℂ)*w)^n := by
    funext n; rw [Int.natAbs_natCast, zpow_natCast, ← mul_pow]
  have hfun2 : (fun n : ℕ => (r:ℂ) ^ ((-(↑n + 1) : ℤ).natAbs) * w ^ (-(↑n + 1) : ℤ))
      = fun n : ℕ => ((r:ℂ)*w⁻¹)^(n+1) := by
    funext n
    rw [show (-(↑n + 1) : ℤ) = Int.negSucc n by simp [Int.negSucc_eq], Int.natAbs_negSucc,
      zpow_negSucc, ← inv_pow, ← mul_pow]
  have hmulη : (fun n : ℕ => ((r:ℂ)*w⁻¹)^(n+1)) = fun n : ℕ => ((r:ℂ)*w⁻¹) * ((r:ℂ)*w⁻¹)^n := by
    funext n; rw [pow_succ, mul_comm]
  have hsum1 : Summable (fun n : ℕ => (r:ℂ) ^ ((n:ℤ).natAbs) * w ^ (n:ℤ)) := by
    rw [hfun1]; exact summable_geometric_of_norm_lt_one hξlt
  have hsum2 : Summable (fun n : ℕ => (r:ℂ) ^ ((-(↑n + 1) : ℤ).natAbs) * w ^ (-(↑n + 1) : ℤ)) := by
    rw [hfun2, hmulη]
    exact (summable_geometric_of_norm_lt_one hηlt).mul_left _
  have hsplit := tsum_of_nat_of_neg_add_one
    (f := fun z : ℤ => (r:ℂ) ^ z.natAbs * w ^ z) hsum1 hsum2
  rw [hsplit]
  have e1 : (∑' n : ℕ, (r:ℂ) ^ ((n:ℤ).natAbs) * w ^ (n:ℤ)) = (1 - (r:ℂ)*w)⁻¹ := by
    rw [hfun1, tsum_geometric_of_norm_lt_one hξlt]
  have e2 : (∑' n : ℕ, (r:ℂ) ^ ((-(↑n + 1) : ℤ).natAbs) * w ^ (-(↑n + 1) : ℤ))
      = ((r:ℂ)*w⁻¹) * (1 - (r:ℂ)*w⁻¹)⁻¹ := by
    rw [hfun2, hmulη, tsum_mul_left, tsum_geometric_of_norm_lt_one hηlt]
  rw [e1, e2]
  exact geom_pair_eq r hr0 hr1 φ w hwnorm hwc

/-- `e(t) + e(t)⁻¹ = 2 cos t` for the circle character `e(t) = exp(2πi t)`. -/
theorem exp_add_inv_exp (θ : ℝ) :
    Complex.exp (2*Real.pi*Complex.I*(θ:ℂ)) + (Complex.exp (2*Real.pi*Complex.I*(θ:ℂ)))⁻¹
      = ((2 * Real.cos (2*Real.pi*θ) : ℝ) : ℂ) := by
  have hw : Complex.exp (2*Real.pi*Complex.I*(θ:ℂ)) = Complex.exp (((2*Real.pi*θ:ℝ):ℂ) * Complex.I) := by
    congr 1; push_cast; ring
  have harg : -(((2*Real.pi*θ:ℝ):ℂ) * Complex.I) = (((-(2*Real.pi*θ)) : ℝ):ℂ) * Complex.I := by
    push_cast; ring
  rw [hw, ← Complex.exp_neg, harg, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I,
    Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- The classical Fourier series of the Poisson kernel on `ℤ`:
`∑_{z∈ℤ} λ^{|z|} e(2πi z θ) = (1-λ²)/(1 - 2λ cos(2πθ) + λ²)` for `0 ≤ λ < 1`. -/
theorem lam_poisson_tsum (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    ∑' z : ℤ, ((r : ℂ) ^ z.natAbs) * Complex.exp (2 * Real.pi * Complex.I * (z:ℂ) * (θ:ℂ))
      = (((1 - r^2) / (1 - 2*r*Real.cos (2*Real.pi*θ) + r^2) : ℝ) : ℂ) := by
  have hcongr : (∑' z : ℤ, ((r:ℂ)^z.natAbs) * Complex.exp (2*Real.pi*Complex.I*(z:ℂ)*(θ:ℂ)))
      = (∑' z : ℤ, (r:ℂ)^z.natAbs * (Complex.exp (2 * Real.pi * Complex.I * (θ:ℂ)))^z) := by
    apply tsum_congr
    intro z
    rw [← Complex.exp_int_mul]
    ring_nf
  rw [hcongr]
  refine lam_poisson_aux r hr0 hr1 (2*Real.pi*θ) _ ?_ ?_
  · have hw : Complex.exp (2*Real.pi*Complex.I*(θ:ℂ))
        = Complex.exp (((2*Real.pi*θ:ℝ):ℂ) * Complex.I) := by
      congr 1; push_cast; ring
    rw [hw]; exact Complex.norm_exp_ofReal_mul_I _
  · exact exp_add_inv_exp θ

/-- **The closed form of the Poisson multiplier is the Fourier series of the Poisson
kernel.**  With `λ = lam ρ i`, `mmClosed ρ i θ = (1-λ)²/(1-2λ cos(2πθ)+λ²)` equals
`∑_{z∈ℤ} kap ρ i z · e(2πi z θ)`, where `kap ρ i z = (1-λ)/(1+λ) λ^{|z|}`. -/
theorem mmClosed_series (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) (θ : ℝ) :
    ((Work.BourgainPlan.Oscillation.Lacunary.mmClosed ρ i θ : ℝ) : ℂ)
      = ∑' z : ℤ, (Work.BourgainPlan.Oscillation.Lacunary.kap ρ i z : ℂ)
          * Complex.exp (2 * Real.pi * Complex.I * ((z : ℤ) : ℂ) * (θ : ℂ)) := by
  have hρ0 : 0 < ρ := by linarith
  have hl0 : 0 ≤ lam ρ i := lam_nonneg hρ0 i
  have hl1 : lam ρ i < 1 := lam_lt_one hρ0 i
  have hpt : ∀ z : ℤ,
      ((kap ρ i z : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((z:ℤ):ℂ) * (θ:ℂ))
      = (((1 - lam ρ i)/(1 + lam ρ i) : ℝ) : ℂ)
          * (((lam ρ i : ℂ)^z.natAbs)
              * Complex.exp (2 * Real.pi * Complex.I * ((z:ℤ):ℂ) * (θ:ℂ))) := by
    intro z
    simp only [kap]
    push_cast
    ring
  have hsumcongr :
      (∑' z : ℤ, ((kap ρ i z : ℝ) : ℂ)
          * Complex.exp (2 * Real.pi * Complex.I * ((z:ℤ):ℂ) * (θ:ℂ)))
      = ∑' z : ℤ, (((1 - lam ρ i)/(1 + lam ρ i) : ℝ) : ℂ)
          * (((lam ρ i : ℂ)^z.natAbs)
              * Complex.exp (2 * Real.pi * Complex.I * ((z:ℤ):ℂ) * (θ:ℂ))) :=
    tsum_congr hpt
  have hmul : (∑' z : ℤ, (((1 - lam ρ i)/(1 + lam ρ i) : ℝ) : ℂ)
        * (((lam ρ i : ℂ)^z.natAbs)
            * Complex.exp (2 * Real.pi * Complex.I * ((z:ℤ):ℂ) * (θ:ℂ))))
      = (((1 - lam ρ i)/(1 + lam ρ i) : ℝ) : ℂ)
          * ∑' z : ℤ, ((lam ρ i : ℂ)^z.natAbs)
              * Complex.exp (2 * Real.pi * Complex.I * (z:ℂ) * (θ:ℂ)) := by
    rw [tsum_mul_left]
  have hkey : ((1 - lam ρ i)/(1 + lam ρ i))
        * ((1 - (lam ρ i)^2)/(1 - 2*lam ρ i*Real.cos (2*Real.pi*θ) + (lam ρ i)^2))
      = mmClosed ρ i θ := by
    unfold mmClosed
    rw [show (1 - (lam ρ i)^2) = (1 - lam ρ i)*(1 + lam ρ i) by ring]
    have h1 : (1 + lam ρ i) ≠ 0 := by linarith
    have h2 : (1 - 2*lam ρ i * Real.cos (2*Real.pi*θ) + (lam ρ i)^2) ≠ 0 :=
      ne_of_gt (mmClosed_denom_pos hρ0 i θ)
    field_simp
  rw [hsumcongr, hmul, lam_poisson_tsum (lam ρ i) hl0 hl1 θ, ← Complex.ofReal_mul, hkey]

end Work.BourgainPlan.Oscillation.Lacunary

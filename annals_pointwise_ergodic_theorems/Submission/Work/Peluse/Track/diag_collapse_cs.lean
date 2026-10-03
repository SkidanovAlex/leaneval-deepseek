import Mathlib
import Submission.Work.Peluse.PET.tsum_cubeShiftSum_norm_sq_le

/-!
# The diagonal collapse `diag_collapse_cs`

Elementary Cauchy–Schwarz step of the "diagonal collapse" in the Peluse-track reduction:
if `F0` is supported in `[-N,N]` and `‖F0 x‖ ≤ 1` everywhere, then for every `W : ℤ → ℂ` the
normalised correlation `(1/(NM)) ∑_x F0 x * W x` can be converted into an `ℓ²` bound for `W`
on the window `[-N,N]`:

`‖(1/(NM)) ∑' x, F0 x * W x‖² * N² * M² ≤ (2N+1) * ∑_{x ∈ [-N,N]} ‖W x‖²`.

Indeed the summand `F0 x * W x` vanishes off the finite window `[-N,N]` of cardinality `2N+1`, so
Cauchy–Schwarz bounds the squared modulus of the `tsum` by `#[-N,N] · ∑ ‖F0 x * W x‖²`, and each
term is at most `‖W x‖²` because `‖F0 x‖ ≤ 1`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Track

noncomputable section

/-- A function supported in `[-N,N]` in the sense of `Work.Peluse.SupportIn` vanishes off the
`Finset` `Work.Peluse.symIcc N`. -/
lemma supportIn_off_symIcc {N : ℕ} {F0 : ℤ → ℂ} (h : Work.Peluse.SupportIn F0 N) :
    ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → F0 x = 0 := by
  intro x hx
  apply h
  rw [Work.Peluse.PET.mem_symIcc_iff_abs] at hx
  have h2 : (N : ℤ) < |x| := not_le.mp hx
  rw [← Int.natCast_natAbs] at h2
  exact_mod_cast h2

/-- The arithmetic of the normalising factor: for `N, M > 0` and any `S : ℂ`,
`‖((N M)⁻¹) * S‖² * N² * M² = ‖S‖²` (where `N`, `M` on the right of the complex factor are the
real numbers). -/
lemma coeff_norm_sq_mul {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (S : ℂ) :
    ‖((N : ℂ) * (M : ℂ))⁻¹ * S‖ ^ 2 * (N : ℝ) ^ 2 * (M : ℝ) ^ 2 = ‖S‖ ^ 2 := by
  have hN0 : ((N : ℝ)) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  have hM0 : ((M : ℝ)) ≠ 0 := by exact_mod_cast (ne_of_gt hM)
  have hcn : ‖(((N : ℂ) * (M : ℂ))⁻¹)‖ = ((N : ℝ) * (M : ℝ))⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have hcoef : ((N : ℝ) * (M : ℝ))⁻¹ ^ 2 * (N : ℝ) ^ 2 * (M : ℝ) ^ 2 = 1 := by
    rw [mul_inv, mul_pow]
    field_simp
  rw [norm_mul, hcn, mul_pow]
  calc (((N : ℝ) * (M : ℝ))⁻¹ ^ 2 * ‖S‖ ^ 2) * (N : ℝ) ^ 2 * (M : ℝ) ^ 2
      = ‖S‖ ^ 2 * (((N : ℝ) * (M : ℝ))⁻¹ ^ 2 * (N : ℝ) ^ 2 * (M : ℝ) ^ 2) := by ring
    _ = ‖S‖ ^ 2 := by rw [hcoef, mul_one]

/-- The Cauchy–Schwarz bound: if `F0` vanishes off `[-N,N]` and `‖F0 x‖ ≤ 1`, then the squared
modulus of `∑' x, F0 x * W x` is at most `(2N+1)` times the `ℓ²` mass of `W` on `[-N,N]`. -/
lemma norm_tsum_mul_sq_le {N : ℕ} {F0 W : ℤ → ℂ} (hF0 : ∀ x, ‖F0 x‖ ≤ 1)
    (h0 : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → F0 x = 0) :
    ‖∑' x : ℤ, F0 x * W x‖ ^ 2
      ≤ (2 * (N : ℝ) + 1) * ∑ x ∈ Work.Peluse.symIcc N, ‖W x‖ ^ 2 := by
  have hf : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → F0 x * W x = 0 :=
    fun x hx => by rw [h0 x hx, zero_mul]
  have h1 := Work.Peluse.PET.norm_tsum_sq_le_card_mul (f := fun x : ℤ => F0 x * W x)
    (S := Work.Peluse.symIcc N) hf
  have h2 : ∑' x : ℤ, ‖F0 x * W x‖ ^ 2 ≤ ∑ x ∈ Work.Peluse.symIcc N, ‖W x‖ ^ 2 := by
    rw [tsum_eq_sum (fun x hx => by rw [h0 x hx, zero_mul, norm_zero]; norm_num)]
    refine Finset.sum_le_sum fun x _ => ?_
    have hle : ‖F0 x‖ * ‖W x‖ ≤ ‖W x‖ := by
      simpa using mul_le_mul_of_nonneg_right (hF0 x) (norm_nonneg (W x))
    have hn : 0 ≤ ‖F0 x‖ * ‖W x‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    calc ‖F0 x * W x‖ ^ 2 = (‖F0 x‖ * ‖W x‖) ^ 2 := by rw [norm_mul]
      _ ≤ ‖W x‖ ^ 2 := pow_le_pow_left₀ hn hle 2
  have hcard : ((Work.Peluse.symIcc N).card : ℝ) = 2 * (N : ℝ) + 1 := by
    rw [Work.Peluse.PET.card_symIcc N]
    push_cast
    ring
  calc ‖∑' x : ℤ, F0 x * W x‖ ^ 2
      ≤ ((Work.Peluse.symIcc N).card : ℝ) * ∑' x : ℤ, ‖F0 x * W x‖ ^ 2 := h1
    _ ≤ ((Work.Peluse.symIcc N).card : ℝ) * ∑ x ∈ Work.Peluse.symIcc N, ‖W x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (2 * (N : ℝ) + 1) * ∑ x ∈ Work.Peluse.symIcc N, ‖W x‖ ^ 2 := by rw [hcard]

theorem diag_collapse_cs {N M : ℕ} (hN : 0 < N) (hM : 0 < M) {F0 W : ℤ → ℂ} {γ : ℝ}
    (hsupp : Work.Peluse.SupportIn F0 N) (hF0 : ∀ x, ‖F0 x‖ ≤ 1)
    (hLam : γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F0 x * W x‖ ^ 2) :
    γ * (N : ℝ) ^ 2 * (M : ℝ) ^ 2
      ≤ (2 * (N : ℝ) + 1) * ∑ x ∈ Work.Peluse.symIcc N, ‖W x‖ ^ 2 := by
  have h0 := supportIn_off_symIcc hsupp
  have hbound := norm_tsum_mul_sq_le (N := N) (W := W) hF0 h0
  have hmul : γ * (N : ℝ) ^ 2 * (M : ℝ) ^ 2
      ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F0 x * W x‖ ^ 2 * (N : ℝ) ^ 2 * (M : ℝ) ^ 2 := by
    have h : (0 : ℝ) ≤ (N : ℝ) ^ 2 * (M : ℝ) ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hLam h
    nlinarith [this]
  rw [coeff_norm_sq_mul hN hM (∑' x : ℤ, F0 x * W x)] at hmul
  exact le_trans hmul hbound

end

end Work.Peluse.Track

import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.KdevA4j
import Submission.Work.Asymptotics.KhatE1.KdevA4Book

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane

noncomputable section

open Work.Kernels

/-!
# The `j⁰`-coefficient of the `E(z)⁴`-residual is polynomially bounded on the funnel

`KdevA4j0 ℓ τ z = 3456π·tailC⁻¹·Phi4j0 ℓ τ z + BRj0 ℓ τ z` is the `j(τ)⁰`-part of
`KdevA4num = 3456π·KdevA4` (`KdevA4j`).  Unlike `j¹` and `j²` it contains no `Δ(τ)⁻¹`, hence no
inverse powers of `q(τ)`: every atom is `O((scale τ)^N)` in `τ`, and the `z`-dependence is a
polynomial of degree `2` in `z`, bounded by `(1+t)^2` on the strip `-1 ≤ Re z ≤ 2`, `Im z = t`.

We record this with a small calculus `BigT M f` of bounds
`‖f τ z‖ ≤ C (scale τ)^N (1+t)^M`, uniform over the funnel with `t ≥ Im τ + 1`.
-/

/-- `BigT M f` records that `‖f τ z‖ = O((scale τ)^N (1+t)^M)` uniformly over the funnel with
`-1 ≤ Re z ≤ 2`, `Im z = t`, `t ≥ Im τ + 1`. -/
def BigT (M : ℕ) (f : ℍ → ℍ → ℂ) : Prop :=
  ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ →
    τ.im + 1 ≤ t → -1 ≤ z.re → z.re ≤ 2 → z.im = t →
    ‖f τ z‖ ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M

/-- `(6i/π)`, the constant appearing in the `Phi4` expansions. -/
private noncomputable def C6pi : ℂ := 6 * Complex.I / (Real.pi : ℂ)

namespace BigT

/-- `1 ≤ 1 + t` on the funnel window. -/
lemma one_le_T {τ : ℍ} {t : ℝ} (h : τ.im + 1 ≤ t) : (1 : ℝ) ≤ 1 + t := by
  have := τ.im_pos; linarith

/-- `BigT` is monotone in the exponent. -/
lemma mono_exp {M₁ M₂ : ℕ} {f : ℍ → ℍ → ℂ} (h : M₁ ≤ M₂) (hf : BigT M₁ f) : BigT M₂ f := by
  obtain ⟨C, N, hC, hN, hb⟩ := hf
  refine ⟨C, N, hC, hN, fun τ z t hτ ht hz1 hz2 hzt => ?_⟩
  refine le_trans (hb τ z t hτ ht hz1 hz2 hzt) ?_
  have hT1 : (1 : ℝ) ≤ 1 + t := one_le_T ht
  have hS0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N :=
    Real.rpow_nonneg (Work.Kernels.scale_pos τ).le N
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC.le hS0)
  exact pow_le_pow_right₀ hT1 h

/-- Rewriting a `BigT` bound along pointwise equal functions. -/
lemma congr {M : ℕ} {f g : ℍ → ℍ → ℂ} (hf : BigT M f) (h : ∀ τ z, f τ z = g τ z) :
    BigT M g := by
  obtain ⟨C, N, hC, hN, hb⟩ := hf
  exact ⟨C, N, hC, hN, fun τ z t hτ ht hz1 hz2 hzt => by
    rw [← h τ z]; exact hb τ z t hτ ht hz1 hz2 hzt⟩

/-- Rewriting a `BigT` bound along pointwise equal functions (with the window hypotheses). -/
lemma congr_on {M : ℕ} {f g : ℍ → ℍ → ℂ} (hf : BigT M f)
    (h : ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
      -1 ≤ z.re → z.re ≤ 2 → z.im = t → f τ z = g τ z) : BigT M g := by
  obtain ⟨C, N, hC, hN, hb⟩ := hf
  exact ⟨C, N, hC, hN, fun τ z t hτ ht hz1 hz2 hzt => by
    rw [← h τ z t hτ ht hz1 hz2 hzt]; exact hb τ z t hτ ht hz1 hz2 hzt⟩

/-- A constant is `BigT 0`. -/
lemma const (c : ℂ) : BigT 0 (fun _ _ : ℍ => c) := by
  refine ⟨‖c‖ + 1, 0, by positivity, le_rfl, fun τ z t _ _ _ _ _ => ?_⟩
  rw [Real.rpow_zero, pow_zero, mul_one, mul_one]
  linarith [norm_nonneg c]

/-- `τ` is `O(scale τ)`. -/
lemma tau : BigT 0 (fun (τ : ℍ) (_ : ℍ) => (τ : ℂ)) := by
  refine ⟨1, 1, one_pos, zero_le_one, fun τ z t _ _ _ _ _ => ?_⟩
  rw [Real.rpow_one, pow_zero, mul_one, one_mul]
  exact Work.Kernels.coe_norm_le_scale τ

/-- `z` is `O(1+t)` on the strip. -/
lemma z : BigT 1 (fun (_ : ℍ) (z : ℍ) => (z : ℂ)) := by
  refine ⟨2, 0, by norm_num, le_rfl, fun τ z t _ _ hz1 hz2 hzt => ?_⟩
  simpa [Real.rpow_zero, pow_one] using
    Work.Asymptotics.KhatE1.kdevA4_norm_z_le z t hz1 hz2 hzt

lemma neg {M : ℕ} {f : ℍ → ℍ → ℂ} (hf : BigT M f) : BigT M (fun τ z => - f τ z) := by
  obtain ⟨C, N, hC, hN, hb⟩ := hf
  exact ⟨C, N, hC, hN, fun τ z t hτ ht hz1 hz2 hzt => by
    rw [norm_neg]; exact hb τ z t hτ ht hz1 hz2 hzt⟩

/-- Sum of two `BigT` bounds. -/
lemma add {M₁ M₂ : ℕ} {f g : ℍ → ℍ → ℂ} (hf : BigT M₁ f) (hg : BigT M₂ g) :
    BigT (max M₁ M₂) (fun τ z => f τ z + g τ z) := by
  obtain ⟨C₁, N₁, hC₁, hN₁, hf⟩ := hf
  obtain ⟨C₂, N₂, hC₂, hN₂, hg⟩ := hg
  refine ⟨C₁ + C₂, N₁ + N₂, by positivity, by positivity,
    fun τ z t hτ ht hz1 hz2 hzt => ?_⟩
  have hT1 : (1 : ℝ) ≤ 1 + t := one_le_T ht
  have hS1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hS0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_trans zero_le_one hS1
  have hT0 : (0 : ℝ) ≤ 1 + t := le_trans zero_le_one hT1
  have hSN1 : (Work.Kernels.scale τ) ^ N₁ ≤ (Work.Kernels.scale τ) ^ (N₁ + N₂) :=
    Real.rpow_le_rpow_of_exponent_le hS1 (by linarith)
  have hSN2 : (Work.Kernels.scale τ) ^ N₂ ≤ (Work.Kernels.scale τ) ^ (N₁ + N₂) :=
    Real.rpow_le_rpow_of_exponent_le hS1 (by linarith)
  have hTM1 : (1 + t) ^ M₁ ≤ (1 + t) ^ max M₁ M₂ :=
    pow_le_pow_right₀ hT1 (le_max_left _ _)
  have hTM2 : (1 + t) ^ M₂ ≤ (1 + t) ^ max M₁ M₂ :=
    pow_le_pow_right₀ hT1 (le_max_right _ _)
  have h1 : C₁ * (Work.Kernels.scale τ) ^ N₁ * (1 + t) ^ M₁
      ≤ C₁ * (Work.Kernels.scale τ) ^ (N₁ + N₂) * (1 + t) ^ max M₁ M₂ :=
    mul_le_mul (mul_le_mul_of_nonneg_left hSN1 hC₁.le) hTM1 (pow_nonneg hT0 _)
      (mul_nonneg hC₁.le (Real.rpow_nonneg hS0 _))
  have h2 : C₂ * (Work.Kernels.scale τ) ^ N₂ * (1 + t) ^ M₂
      ≤ C₂ * (Work.Kernels.scale τ) ^ (N₁ + N₂) * (1 + t) ^ max M₁ M₂ :=
    mul_le_mul (mul_le_mul_of_nonneg_left hSN2 hC₂.le) hTM2 (pow_nonneg hT0 _)
      (mul_nonneg hC₂.le (Real.rpow_nonneg hS0 _))
  calc ‖f τ z + g τ z‖ ≤ ‖f τ z‖ + ‖g τ z‖ := norm_add_le _ _
    _ ≤ C₁ * (Work.Kernels.scale τ) ^ N₁ * (1 + t) ^ M₁
          + C₂ * (Work.Kernels.scale τ) ^ N₂ * (1 + t) ^ M₂ :=
        add_le_add (hf τ z t hτ ht hz1 hz2 hzt) (hg τ z t hτ ht hz1 hz2 hzt)
    _ ≤ C₁ * (Work.Kernels.scale τ) ^ (N₁ + N₂) * (1 + t) ^ max M₁ M₂
          + C₂ * (Work.Kernels.scale τ) ^ (N₁ + N₂) * (1 + t) ^ max M₁ M₂ := add_le_add h1 h2
    _ = (C₁ + C₂) * (Work.Kernels.scale τ) ^ (N₁ + N₂) * (1 + t) ^ max M₁ M₂ := by ring

/-- Difference of two `BigT` bounds. -/
lemma sub {M₁ M₂ : ℕ} {f g : ℍ → ℍ → ℂ} (hf : BigT M₁ f) (hg : BigT M₂ g) :
    BigT (max M₁ M₂) (fun τ z => f τ z - g τ z) :=
  BigT.congr (add hf (neg hg)) (fun τ z => by simp [sub_eq_add_neg])

/-- Product of two `BigT` bounds. -/
lemma mul {M₁ M₂ : ℕ} {f g : ℍ → ℍ → ℂ} (hf : BigT M₁ f) (hg : BigT M₂ g) :
    BigT (M₁ + M₂) (fun τ z => f τ z * g τ z) := by
  obtain ⟨C₁, N₁, hC₁, hN₁, hf⟩ := hf
  obtain ⟨C₂, N₂, hC₂, hN₂, hg⟩ := hg
  refine ⟨C₁ * C₂, N₁ + N₂, by positivity, by positivity,
    fun τ z t hτ ht hz1 hz2 hzt => ?_⟩
  have h1 := hf τ z t hτ ht hz1 hz2 hzt
  have h2 := hg τ z t hτ ht hz1 hz2 hzt
  have hS0 : (0 : ℝ) ≤ Work.Kernels.scale τ := (Work.Kernels.scale_pos τ).le
  have hT0 : (0 : ℝ) ≤ 1 + t := by have := one_le_T ht; linarith
  have hq1 : (0 : ℝ) ≤ C₁ * (Work.Kernels.scale τ) ^ N₁ * (1 + t) ^ M₁ :=
    mul_nonneg (mul_nonneg hC₁.le (Real.rpow_nonneg hS0 _)) (pow_nonneg hT0 _)
  rw [norm_mul]
  refine le_trans (mul_le_mul h1 h2 (norm_nonneg _) hq1) (le_of_eq ?_)
  rw [Real.rpow_add (Work.Kernels.scale_pos τ), pow_add]
  ring

/-- Scalar multiple of a `BigT` bound. -/
lemma const_mul (c : ℂ) {M : ℕ} {f : ℍ → ℍ → ℂ} (hf : BigT M f) :
    BigT M (fun τ z => c * f τ z) := by
  obtain ⟨C, N, hC, hN, hb⟩ := hf
  refine ⟨(‖c‖ + 1) * C, N, by positivity, hN, fun τ z t hτ ht hz1 hz2 hzt => ?_⟩
  rw [norm_mul]
  calc ‖c‖ * ‖f τ z‖
      ≤ (‖c‖ + 1) * (C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M) :=
        mul_le_mul (by linarith [norm_nonneg c]) (hb τ z t hτ ht hz1 hz2 hzt)
          (norm_nonneg _) (by positivity)
    _ = ((‖c‖ + 1) * C) * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by ring

/-- Rewriting along `ring`-equal targets. -/
lemma congr_ring {M : ℕ} {f : ℍ → ℍ → ℂ} (hf : BigT M f) (g : ℍ → ℍ → ℂ)
    (h : ∀ τ z, f τ z = g τ z) : BigT M g := hf.congr h

/-- `E₂` is bounded on the funnel. -/
lemma E2Fun : BigT 0 (fun (τ : ℍ) (_ : ℍ) => Work.Kernels.E2Fun τ) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.E2Fun_bound
  refine ⟨C, 0, hC, le_rfl, fun τ z t hτ _ _ _ _ => ?_⟩
  have h1 : (1 : ℝ) ≤ τ.im := le_trans (by norm_num) hτ.2
  simpa [Real.rpow_zero, pow_zero] using h τ h1

/-- `E₄` is bounded on the funnel. -/
lemma E4Fun : BigT 0 (fun (τ : ℍ) (_ : ℍ) => Work.Kernels.E4Fun τ) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.KhatE1.kdevA4_norm_E4_le
  refine ⟨C, 0, hC, le_rfl, fun τ z t hτ _ _ _ _ => ?_⟩
  simpa [Real.rpow_zero, pow_zero] using h τ hτ

/-- `E₆` is bounded on the funnel. -/
lemma E6Fun : BigT 0 (fun (τ : ℍ) (_ : ℍ) => Work.Kernels.E6Fun τ) := by
  obtain ⟨C, hC, h⟩ := Work.Asymptotics.KhatE1.kdevA4_norm_E6_le
  refine ⟨C, 0, hC, le_rfl, fun τ z t hτ _ _ _ _ => ?_⟩
  simpa [Real.rpow_zero, pow_zero] using h τ hτ

/-- `ψ₄` is `O((scale τ)^N)` on the funnel. -/
lemma psi4 (ℓ : Work.Kernels.LogLambdaData) :
    BigT 0 (fun (τ : ℍ) (_ : ℍ) => Work.Kernels.psi4 ℓ τ) := by
  obtain ⟨C, N, hC, hN, h⟩ := Work.Asymptotics.KhatE1.kdevA4_norm_psi_le ℓ
  refine ⟨C, N, hC, hN, fun τ z t hτ _ _ _ _ => ?_⟩
  simpa [pow_zero, mul_one] using (h τ hτ).2

/-- `Xc ℓ z = πi z + cuspC ℓ` is `O(1+t)` on the strip. -/
lemma Xc (ℓ : Work.Kernels.LogLambdaData) :
    BigT 1 (fun (_ : ℍ) (z : ℍ) => Work.Asymptotics.Compact.Xc ℓ z) := by
  refine ⟨2 * Real.pi + ‖Work.Asymptotics.Compact.cuspC ℓ‖, 0, by positivity, le_rfl,
    fun τ z t _ ht hz1 hz2 hzt => ?_⟩
  have hz := Work.Asymptotics.KhatE1.kdevA4_norm_z_le z t hz1 hz2 hzt
  have hT1 : (1 : ℝ) ≤ 1 + t := one_le_T ht
  have hc : ‖Work.Asymptotics.Compact.cuspC ℓ‖
      ≤ ‖Work.Asymptotics.Compact.cuspC ℓ‖ * (1 + t) := by
    calc ‖Work.Asymptotics.Compact.cuspC ℓ‖ = ‖Work.Asymptotics.Compact.cuspC ℓ‖ * 1 := by ring
      _ ≤ ‖Work.Asymptotics.Compact.cuspC ℓ‖ * (1 + t) :=
          mul_le_mul_of_nonneg_left hT1 (norm_nonneg _)
  have hcn : ‖(Real.pi : ℂ) * Complex.I * (z : ℂ)‖ = Real.pi * ‖(z : ℂ)‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hmain : ‖Work.Asymptotics.Compact.Xc ℓ z‖
      ≤ (2 * Real.pi + ‖Work.Asymptotics.Compact.cuspC ℓ‖) * (1 + t) := by
    calc ‖Work.Asymptotics.Compact.Xc ℓ z‖
        = ‖(Real.pi : ℂ) * Complex.I * (z : ℂ) + Work.Asymptotics.Compact.cuspC ℓ‖ := by
          rfl
      _ ≤ ‖(Real.pi : ℂ) * Complex.I * (z : ℂ)‖ + ‖Work.Asymptotics.Compact.cuspC ℓ‖ :=
          norm_add_le _ _
      _ = Real.pi * ‖(z : ℂ)‖ + ‖Work.Asymptotics.Compact.cuspC ℓ‖ := by rw [hcn]
      _ ≤ Real.pi * (2 * (1 + t)) + ‖Work.Asymptotics.Compact.cuspC ℓ‖ * (1 + t) :=
          add_le_add (mul_le_mul_of_nonneg_left hz Real.pi_pos.le) hc
      _ = (2 * Real.pi) * (1 + t) + ‖Work.Asymptotics.Compact.cuspC ℓ‖ * (1 + t) := by ring
      _ = (2 * Real.pi + ‖Work.Asymptotics.Compact.cuspC ℓ‖) * (1 + t) := by ring
  simpa [Real.rpow_zero, pow_one] using hmain

end BigT

/-! ## The assembly -/

/-- **`Phi4j0` is `O((scale τ)^N (1+t)²)` on the funnel window.** -/
private lemma bigT_Phi4j0 (ℓ : Work.Kernels.LogLambdaData) :
    BigT 2 (fun τ z => Phi4j0 ℓ τ z) := by
  have hC0 : BigT 0 (fun _ _ : ℍ => C6pi) := BigT.const C6pi
  have hE2 : BigT 0 (fun (τ : ℍ) (_ : ℍ) => Work.Kernels.E2Fun τ) := BigT.E2Fun
  have hE4 : BigT 0 (fun (τ : ℍ) (_ : ℍ) => Work.Kernels.E4Fun τ) := BigT.E4Fun
  have hE6 : BigT 0 (fun (τ : ℍ) (_ : ℍ) => Work.Kernels.E6Fun τ) := BigT.E6Fun
  have hTau : BigT 0 (fun (τ : ℍ) (_ : ℍ) => (τ : ℂ)) := BigT.tau
  have hZ : BigT 1 (fun (_ : ℍ) (z : ℍ) => (z : ℂ)) := BigT.z
  have m1 : BigT 2 (fun τ z =>
      (-55440 : ℂ) * (Work.Kernels.E6Fun τ * C6pi * C6pi * (τ : ℂ))) :=
    BigT.mono_exp (show (0 : ℕ) ≤ 2 by norm_num)
      (BigT.congr (BigT.const_mul (-55440)
        (BigT.mul (BigT.mul (BigT.mul hE6 hC0) hC0) hTau)) (fun τ z => by ring))
  have m2 : BigT 2 (fun τ z =>
      (122256 : ℂ) * ((z : ℂ) * Work.Kernels.E6Fun τ * C6pi * (τ : ℂ))) :=
    BigT.mono_exp (show (1 : ℕ) ≤ 2 by norm_num)
      (BigT.congr (BigT.const_mul 122256
        (BigT.mul (BigT.mul (BigT.mul hZ hE6) hC0) hTau)) (fun τ z => by ring))
  have m3 : BigT 2 (fun τ z =>
      (-787536 : ℂ) * ((z : ℂ) * Work.Kernels.E4Fun τ * C6pi * (τ : ℂ)
        * Work.Kernels.E2Fun τ)) :=
    BigT.mono_exp (show (1 : ℕ) ≤ 2 by norm_num)
      (BigT.congr (BigT.const_mul (-787536)
        (BigT.mul (BigT.mul (BigT.mul (BigT.mul hZ hE4) hC0) hTau) hE2))
        (fun τ z => by ring))
  have m4 : BigT 2 (fun τ z =>
      (393768 : ℂ) * ((z : ℂ) * Work.Kernels.E4Fun τ * C6pi * C6pi)) :=
    BigT.mono_exp (show (1 : ℕ) ≤ 2 by norm_num)
      (BigT.congr (BigT.const_mul 393768
        (BigT.mul (BigT.mul (BigT.mul hZ hE4) hC0) hC0)) (fun τ z => by ring))
  have m5 : BigT 2 (fun τ z =>
      (-67392 : ℂ) * ((z : ℂ) * (z : ℂ) * Work.Kernels.E6Fun τ * (τ : ℂ))) :=
    BigT.congr (BigT.const_mul (-67392)
      (BigT.mul (BigT.mul (BigT.mul hZ hZ) hE6) hTau)) (fun τ z => by ring)
  have m6 : BigT 2 (fun τ z =>
      (834624 : ℂ) * ((z : ℂ) * (z : ℂ) * Work.Kernels.E4Fun τ * (τ : ℂ)
        * Work.Kernels.E2Fun τ)) :=
    BigT.congr (BigT.const_mul 834624
      (BigT.mul (BigT.mul (BigT.mul (BigT.mul hZ hZ) hE4) hTau) hE2))
      (fun τ z => by ring)
  have m7 : BigT 2 (fun τ z =>
      (-417312 : ℂ) * ((z : ℂ) * (z : ℂ) * Work.Kernels.E4Fun τ * C6pi)) :=
    BigT.congr (BigT.const_mul (-417312)
      (BigT.mul (BigT.mul (BigT.mul hZ hZ) hE4) hC0)) (fun τ z => by ring)
  have hsum := BigT.add m1 (BigT.add m2 (BigT.add m3 (BigT.add m4 (BigT.add m5 (BigT.add m6 m7)))))
  exact hsum.congr_on (fun τ z t _ _ _ _ _ => by simp only [Phi4j0, C6pi]; ring)

/-- **`BRj0` is `O((scale τ)^N (1+t))` on the funnel window.** -/
private lemma bigT_BRj0 (ℓ : Work.Kernels.LogLambdaData) :
    BigT 1 (fun τ z => BRj0 ℓ τ z) := by
  have hE4 : BigT 0 (fun (τ : ℍ) (_ : ℍ) => Work.Kernels.E4Fun τ) := BigT.E4Fun
  have b1 : BigT 0 (fun τ z => (85888512 : ℂ) * Work.Kernels.psi4 ℓ τ) :=
    BigT.const_mul 85888512 (BigT.psi4 ℓ)
  have b2 : BigT 0 (fun τ z => (40787712 : ℂ) * Work.Kernels.E4Fun τ) :=
    BigT.const_mul 40787712 hE4
  have b3 : BigT 1 (fun τ z => (1360862208 : ℂ)
      * (Work.Asymptotics.Compact.Xc ℓ z * Work.Kernels.E4Fun τ)) :=
    BigT.const_mul 1360862208 (BigT.mul (BigT.Xc ℓ) hE4)
  exact (BigT.sub (BigT.add b1 b2) b3).congr_on
    (fun τ z t _ _ _ _ _ => by simp only [BRj0])

/-- **`KdevA4j0` is `O((scale τ)^N (1+t)²)` on the funnel window.** -/
private lemma bigT_KdevA4j0 (ℓ : Work.Kernels.LogLambdaData) :
    BigT 2 (fun τ z => KdevA4j0 ℓ τ z) := by
  have h := BigT.add
    (BigT.const_mul (((3456 : ℂ) * (Real.pi : ℂ)) * Work.Asymptotics.Compact.tailC⁻¹)
      (bigT_Phi4j0 ℓ))
    (BigT.mono_exp (show (1 : ℕ) ≤ 2 by norm_num) (bigT_BRj0 ℓ))
  exact h.congr (fun τ z => by simp only [KdevA4j0])

/-- **The `j⁰`-coefficient of the `E(z)⁴`-residual is polynomially bounded on the funnel.** -/
theorem KdevA4j0_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.KdevA4j0 ℓ τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨C, N, hC, hN, hb⟩ := bigT_KdevA4j0 ℓ
  refine ⟨C, N, 2, hC, hN, by norm_num, fun τ z t hτ ht hz1 hz2 hzt => ?_⟩
  simpa [Real.rpow_natCast] using hb τ z t hτ ht hz1 hz2 hzt

end

end Work.Asymptotics.KhatE1Core

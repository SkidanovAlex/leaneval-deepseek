import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpArcDefs

/-!
# The `ℓ² → ℓ^∞` bound for a Fourier multiplier with summable coefficient kernel

Source: T. Bourgain's polynomial ergodic theorem / the Ionescu–Wainger multiplier theorem; the
`p = ∞` endpoint of Tao's `ortho-apply`(ii): a Fourier multiplier `Op_Φ` on `ℓ²(ℤ)`, whose symbol
`Φ ∈ L^∞(𝕋)` has **summable** Fourier coefficients `K`, is bounded from `ℓ²(ℤ)` to `ℓ^∞(ℤ)` with
operator norm at most `Σ_m ‖K m‖`.

In the `ℓ²(ℤ) ≅ L²(𝕋)` picture of `OpArcDefs.lean` the multiplier `opMul Φ f hf` is defined by
`𝓕(Op_Φ f) = Φ · 𝓕f`, so its `n`-th coefficient is `⟪e_n, Φ • 𝓕f⟫`.  Writing `Φ`'s coefficients as
the kernel `K_m = ∫_𝕋 Φ(ξ) · conj(e_m(ξ)) dξ` (the hypothesis `hker` of the main theorem), the
multiplier is the **convolution with the kernel**:

`opMul Φ f hf n = Σ_k f k · K (n - k)`

(`opMul_eq_tsum_kernel`), and the announced bound is the triangle inequality together with the
reindexing `Σ_k ‖K (n-k)‖ = Σ_m ‖K m‖` (`norm_tsum_mul_shift_le`).

The two ingredients of the coefficient computation are:

* `inner_lpSMul_star`: the adjunction identity `⟪A, Ψ • B⟫ = ⟪star Ψ • A, B⟫` for `Ψ ∈ L^∞`,
  `A, B ∈ L²` (the `L^∞`-multiplier is "self-adjoint up to `star`"), which moves the symbol from
  the second to the first slot of the inner product;
* `inner_fourierBasis_star_lpSMul`: `⟪e_k, star Φ • e_n⟫ = conj (K (n - k))`, an immediate
  consequence of the definition of `K` and of the character identity
  `e_n · conj(e_k) = e_{n-k}` (`fourier_mul_star_fourier`).

The `ℓ²`-expansion `Σ_k ⟪H, e_k⟫ · ⟪e_k, G⟫ = ⟪H, G⟫` is Mathlib's
`HilbertBasis.tsum_inner_mul_inner`.
-/

open MeasureTheory
open scoped lp BigOperators ENNReal

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

noncomputable section

/-- **Character identity**: `e_n(ξ) · conj (e_k(ξ)) = e_{n-k}(ξ)` on `𝕋 = ℝ/ℤ`. -/
lemma fourier_mul_star_fourier (n k : ℤ) (ξ : Circle) :
    fourier n ξ * star (fourier k ξ) = fourier (n - k) ξ := by
  have h1 : star (fourier k ξ) = fourier (-k) ξ := (fourier_neg (n := k) (x := ξ)).symm
  rw [h1, ← fourier_add, sub_eq_add_neg]

/-- **Adjunction for the `L^∞`-multiplier**: for `Ψ ∈ L^∞(𝕋)` and `A, B ∈ L²(𝕋)`,

`⟪A, Ψ • B⟫ = ⟪star Ψ • A, B⟫`. -/
theorem inner_lpSMul_star {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (Ψ : Lp ℂ ⊤ μ) (A B : Lp ℂ 2 μ) :
    inner ℂ A (Ψ • B : Lp ℂ 2 μ) = inner ℂ (star Ψ • A : Lp ℂ 2 μ) B := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) Ψ B,
    Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) (star Ψ) A, Lp.coeFn_star Ψ]
    with ξ h1 h2 h3
  rw [h1, h2]
  simp only [smul_eq_mul, Pi.mul_apply]
  rw [h3]
  simp only [starRingEnd_apply, Pi.star_apply, RCLike.inner_apply, star_mul, star_star]
  ring

/-- **The coefficient of the translated symbol**: if the Fourier coefficients of the `L^∞`-symbol
`Φ` are the sequence `K` (`∫ Φ · conj e_m = K m`), then the `k`-th coefficient of
`star Φ • e_n` is `conj (K (n - k))`. -/
theorem inner_fourierBasis_star_lpSMul (Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)))
    {K : ℤ → ℂ}
    (hker : ∀ m : ℤ, ∫ ξ : Circle, (Φ : Circle → ℂ) ξ * star (fourier m ξ)
      ∂(AddCircle.haarAddCircle (T := 1)) = K m) (n k : ℤ) :
    inner ℂ (fourierBasis (T := 1) k) (star Φ • fourierBasis (T := 1) n : Lp ℂ 2 _)
      = star (K (n - k)) := by
  rw [L2.inner_def]
  have hpt : (fun ξ : Circle => inner ℂ ((fourierBasis (T := 1) k : Lp ℂ 2 _) ξ)
        ((star Φ • fourierBasis (T := 1) n : Lp ℂ 2 _) ξ))
      =ᵐ[AddCircle.haarAddCircle (T := 1)]
        fun ξ => star ((Φ : Circle → ℂ) ξ * star (fourier (n - k) ξ)) := by
    have h3 : (fun ξ : Circle => (fourierBasis (T := 1) k : Lp ℂ 2 _) ξ)
        =ᵐ[AddCircle.haarAddCircle (T := 1)] ⇑(fourier k) := by
      simpa using coeFn_fourierLp (T := 1) 2 (n := k)
    have h4 : (fun ξ : Circle => (fourierBasis (T := 1) n : Lp ℂ 2 _) ξ)
        =ᵐ[AddCircle.haarAddCircle (T := 1)] ⇑(fourier n) := by
      simpa using coeFn_fourierLp (T := 1) 2 (n := n)
    filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) (star Φ)
        (fourierBasis (T := 1) n), Lp.coeFn_star Φ, h3, h4] with ξ h1 h2 h3 h4
    rw [h1]
    simp only [smul_eq_mul, Pi.mul_apply]
    rw [h2, h3, h4]
    simp only [starRingEnd_apply, Pi.star_apply, RCLike.inner_apply, star_mul, star_star]
    rw [← fourier_mul_star_fourier n k ξ]
    ring
  rw [integral_congr_ae hpt]
  have hconj : (∫ a : Circle, star ((Φ : Circle → ℂ) a * star (fourier (n - k) a))
        ∂(AddCircle.haarAddCircle (T := 1)))
      = star (∫ a : Circle, (Φ : Circle → ℂ) a * star (fourier (n - k) a)
        ∂(AddCircle.haarAddCircle (T := 1))) := by
    simpa only [RCLike.star_def] using (integral_conj (μ := AddCircle.haarAddCircle (T := 1))
      (f := fun a : Circle => (Φ : Circle → ℂ) a * star (fourier (n - k) a)))
  rw [hconj, hker]

/-- **The convolution identity**: a multiplier whose symbol has coefficient kernel `K` acts as the
convolution with `K`, i.e. `Op_Φ f (n) = Σ_k f k · K (n - k)`.  No summability of `K` is needed
for the identity itself. -/
theorem opMul_eq_tsum_kernel (Φ : Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1))) (f : ℤ → ℂ)
    (hf : Memℓp f 2) {K : ℤ → ℂ}
    (hker : ∀ m : ℤ, ∫ ξ : Circle, (Φ : Circle → ℂ) ξ * star (fourier m ξ)
      ∂(AddCircle.haarAddCircle (T := 1)) = K m) (n : ℤ) :
    opMul Φ f hf n = ∑' k : ℤ, f k * K (n - k) := by
  rw [opMul_apply, opMulLp]
  rw [inner_lpSMul_star Φ (fourierBasis (T := 1) n) (ftLp f hf)]
  rw [← HilbertBasis.tsum_inner_mul_inner (fourierBasis (T := 1))
    (star Φ • fourierBasis (T := 1) n) (ftLp f hf)]
  refine tsum_congr fun k => ?_
  rw [← inner_conj_symm, ftLp_coeff hf k, inner_fourierBasis_star_lpSMul Φ hker n k]
  simp only [starRingEnd_apply, star_star]
  ring

/-- **The `ℓ¹`-kernel bound**: the convolution with a summable kernel `K` maps the bounded sequences
into `ℓ^∞`, with the bound `Σ_m ‖K m‖` times the sup-norm. -/
theorem norm_tsum_mul_shift_le {f K : ℤ → ℂ} (hK : Summable fun m : ℤ => ‖K m‖) {C : ℝ}
    (hC : ∀ m : ℤ, ‖f m‖ ≤ C) (n : ℤ) :
    ‖∑' k : ℤ, f k * K (n - k)‖ ≤ (∑' m : ℤ, ‖K m‖) * C := by
  have hshift : Summable fun k : ℤ => ‖K (n - k)‖ := by
    have h := (Equiv.summable_iff (Equiv.subLeft n)).mpr hK
    rw [show ((fun m : ℤ => ‖K m‖) ∘ ⇑(Equiv.subLeft n)) = (fun k : ℤ => ‖K (n - k)‖) from
      funext (fun k => by rw [Function.comp_apply, Equiv.subLeft_apply])] at h
    exact h
  have hB : Summable fun k : ℤ => C * ‖K (n - k)‖ := hshift.mul_left C
  have hA : Summable fun k : ℤ => ‖f k‖ * ‖K (n - k)‖ :=
    Summable.of_nonneg_of_le (f := fun k : ℤ => C * ‖K (n - k)‖)
      (g := fun k : ℤ => ‖f k‖ * ‖K (n - k)‖)
      (fun k => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun k => mul_le_mul_of_nonneg_right (hC k) (norm_nonneg _)) hB
  have hnorm : Summable fun k : ℤ => ‖f k * K (n - k)‖ := by
    simpa using hA
  have hreindex : (∑' k : ℤ, ‖K (n - k)‖) = ∑' m : ℤ, ‖K m‖ := by
    rw [← Equiv.tsum_eq (Equiv.subLeft n) (fun m : ℤ => ‖K m‖)]
    exact tsum_congr (fun k => by rw [Equiv.subLeft_apply])
  calc ‖∑' k : ℤ, f k * K (n - k)‖
      ≤ ∑' k : ℤ, ‖f k * K (n - k)‖ := norm_tsum_le_tsum_norm hnorm
    _ = ∑' k : ℤ, ‖f k‖ * ‖K (n - k)‖ := by simp
    _ ≤ ∑' k : ℤ, C * ‖K (n - k)‖ :=
        Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_right (hC k) (norm_nonneg _)) hA hB
    _ = C * ∑' k : ℤ, ‖K (n - k)‖ := tsum_mul_left
    _ = C * ∑' m : ℤ, ‖K m‖ := by rw [hreindex]
    _ = (∑' m : ℤ, ‖K m‖) * C := mul_comm _ _

/-- The `ℓ^∞` bound for a Fourier multiplier on `ℓ²(ℤ)` whose symbol has summable Fourier
coefficients: if the coefficients of the `L^∞`-symbol `Φ` (the circle integrals `∫ Φ · star e_m`)
form the summable sequence `K`, then the multiplier is bounded from `ℓ²(ℤ)` to `ℓ^∞(ℤ)` by the
`ℓ¹`-norm of `K` times the sup-norm of `f`. -/
theorem norm_opMul_le_of_kernel (Φ : MeasureTheory.Lp ℂ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (f : ℤ → ℂ) (hf : Memℓp f 2) {K : ℤ → ℂ} (hK : Summable fun m : ℤ => ‖K m‖) {C : ℝ}
    (hC : ∀ m : ℤ, ‖f m‖ ≤ C)
    (hker : ∀ m : ℤ, ∫ ξ, (Φ : Circle → ℂ) ξ * star (fourier m ξ)
        ∂(AddCircle.haarAddCircle (T := 1)) = K m) (n : ℤ) :
    ‖opMul Φ f hf n‖ ≤ (∑' m : ℤ, ‖K m‖) * C := by
  rw [opMul_eq_tsum_kernel Φ f hf hker n]
  exact norm_tsum_mul_shift_le hK hC n

end

end Work.BourgainPlan.IonescuWainger

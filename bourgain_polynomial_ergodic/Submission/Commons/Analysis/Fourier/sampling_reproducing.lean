import Mathlib.Analysis.Fourier.PoissonSummation

/-
Copyright (c) 2026 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/

/-!
# The lattice sampling / reproducing formula for band-limited Schwartz functions

If `ψ` is a Schwartz function on `ℝ` whose Fourier transform equals `1` on `[-c₀, c₀]`
and vanishes outside `[-1/2, 1/2]`, and `f` is a Schwartz function whose Fourier
transform is supported in `[-c₀, c₀]` with `c₀ < 1/2`, then `f` is reproduced from its
values on the integer lattice by

`f y = ∑' x : ℤ, ψ (y - x) * f x`  for every `y : ℝ`.

This is the "sampling/reproducing" ingredient in Krause–Mirek–Tao's proof of pointwise
ergodic theorems for non-conventional bilinear polynomial averages.

The proof is a standard Poisson-summation argument.  Writing
`S ξ = ∑' n : ℤ, f n * e^{-2πi n ξ}` for the discrete Fourier transform of the samples,
Poisson summation (Lemma `poisson_modulated`) gives `S ξ = ∑' k : ℤ, 𝓕f (ξ + k)`.
Using the support assumptions one deduces the pointwise identity
`𝓕f ξ = 𝓕ψ ξ * S ξ` (Lemma `hmain`).  Integrating the latter against `e^{2πi ξ y}`
(and interchanging sum and integral) yields the claim, the inner integral being
`ψ (y - x)` by Fourier inversion.
-/

namespace Commons.Analysis.Fourier

open MeasureTheory FourierTransform VectorFourier
open scoped FourierTransform Topology

noncomputable section

/-- The exponential character `φ t = e^{2πi t}`. -/
private def phi (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (t:ℂ))

private lemma phi_add (a b : ℝ) : phi (a+b) = phi a * phi b := by
  simp only [phi, ← Complex.exp_add]; congr 1; push_cast; ring

private lemma norm_phi (t : ℝ) : ‖phi t‖ = 1 := by
  rw [phi, show 2 * Real.pi * Complex.I * (t:ℂ) = ↑(2*Real.pi*t) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma phi_neg (t : ℝ) : phi (-t) = (phi t)⁻¹ := by
  rw [phi, phi, ← Complex.exp_neg]; congr 1; push_cast; ring

private lemma continuous_phi : Continuous phi := by
  unfold phi; fun_prop

/-- The Fourier transform of the Fourier transform of a Schwartz function is the
reflection of the function. -/
private lemma schwartz_fourier_fourier (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    (𝓕 (𝓕 g)) x = g (-x) := by
  have h_inv : (𝓕⁻ (𝓕 g) : SchwartzMap ℝ ℂ) = g := fourierInv_fourier_eq _
  have hneg : ∀ w, (𝓕 (𝓕 g)) (-w) = g w := by
    intro w
    have h := Real.fourierInv_eq_fourier_neg ((𝓕 g : SchwartzMap ℝ ℂ) : ℝ → ℂ) w
    rw [← SchwartzMap.fourierInv_coe (𝓕 g), ← SchwartzMap.fourier_coe (𝓕 g)] at h
    rw [congrFun (congrArg DFunLike.coe h_inv) w] at h
    exact h.symm
  have := hneg (-x)
  rwa [neg_neg] at this

/-- A Schwartz function is summable on the integer lattice. -/
private lemma schwartz_summable (f : SchwartzMap ℝ ℂ) : Summable (fun n : ℤ => f (n:ℝ)) :=
  summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1:ℝ)<2))
    ((f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)

/-- The norms of the lattice values of a Schwartz function form a summable series. -/
private lemma schwartz_summable_norm (f : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℤ => ‖f (n:ℝ)‖) :=
  summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : (1:ℝ)<2))
    (((f.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite).norm_left)

/-- **Modulated Poisson summation.**  For a Schwartz function `f` and real `ξ`,
`∑' n, f n * e^{-2πi n ξ} = ∑' k, 𝓕f (ξ + k)`.

This is Poisson summation applied to `𝓕f`: it follows from
`SchwartzMap.tsum_eq_tsum_fourier` and `𝓕𝓕 = reflection`. -/
private lemma poisson_modulated (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    ∑' n : ℤ, f (n:ℝ) * phi (-((n:ℝ)*ξ)) = ∑' k : ℤ, (𝓕 f) (ξ + (k:ℝ)) := by
  rw [show (∑' n : ℤ, f (n:ℝ) * phi (-((n:ℝ)*ξ)))
      = ∑' n : ℤ, f (n:ℝ) * Complex.exp (-(2 * Real.pi * Complex.I * (n:ℂ) * (ξ:ℂ)))
        from by
        apply tsum_congr; intro n; congr 1
        rw [phi]; congr 1; push_cast; ring]
  rw [SchwartzMap.tsum_eq_tsum_fourier (𝓕 f) ξ]
  have hR : (∑' n : ℤ, (𝓕 (𝓕 f)) (n:ℝ) * (_root_.fourier n) (ξ : UnitAddCircle))
      = ∑' n : ℤ, f (-(n:ℝ)) * Complex.exp (2 * Real.pi * Complex.I * (n:ℂ) * (ξ:ℂ)) := by
    apply tsum_congr; intro n
    rw [schwartz_fourier_fourier, fourier_coe_apply]
    norm_num
  rw [hR]
  rw [← Equiv.tsum_eq (Equiv.neg ℤ)
        (fun n : ℤ => f (-(n:ℝ)) * Complex.exp (2 * Real.pi * Complex.I * (n:ℂ) * (ξ:ℂ)))]
  apply tsum_congr; intro n
  simp only [Equiv.neg_apply]
  push_cast
  rw [show f (- -↑n) = f ↑n by rw [neg_neg]]
  congr 1
  ring_nf

/-- An integer whose real embedding is smaller than `1` in absolute value is zero. -/
private lemma int_abs_lt_one_eq_zero {k : ℤ} (h : |(k:ℝ)| < 1) : k = 0 := by
  by_contra hk
  have h1 : (1:ℤ) ≤ |k| := Int.one_le_abs hk
  have h2 : (1:ℝ) ≤ |(k:ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast h1
  linarith

/-- A quantitative lattice separation statement: if `|ξ| ≤ B` and `ξ + k ∈ [-c₀, c₀]`
with `c₀ + B < 1`, then `k = 0`. -/
private lemma int_eq_zero_of_shift_mem {c0 B : ℝ} (hB : c0 + B < 1) {ξ : ℝ} (hξ : |ξ| ≤ B)
    {k : ℤ} (hmem : ξ + (k:ℝ) ∈ Set.Icc (-c0) c0) (hk : k ≠ 0) : False := by
  have h1 : |ξ + (k:ℝ)| ≤ c0 := by
    rw [abs_le]; exact ⟨(Set.mem_Icc.mp hmem).1, (Set.mem_Icc.mp hmem).2⟩
  have htri : |(k:ℝ)| ≤ |ξ + (k:ℝ)| + |ξ| := by
    have h := abs_add_le (ξ + (k:ℝ)) (-ξ)
    rw [abs_neg, show ξ + (k:ℝ) + -ξ = (k:ℝ) by ring] at h
    exact h
  have : |(k:ℝ)| < 1 := by linarith
  exact hk (int_abs_lt_one_eq_zero this)

theorem sampling_reproducing (c0 : ℝ) (hc0 : 0 < c0) (hc0' : c0 < 1/2)
    (ψ : SchwartzMap ℝ ℂ) (f : SchwartzMap ℝ ℂ)
    (hψ1 : ∀ ξ ∈ Set.Icc (-c0) c0, FourierTransform.fourier ψ ξ = 1)
    (hψs : ∀ ξ, ξ ∉ Set.Icc (-(1/2:ℝ)) (1/2) → FourierTransform.fourier ψ ξ = 0)
    (hfs : ∀ ξ, ξ ∉ Set.Icc (-c0) c0 → FourierTransform.fourier f ξ = 0) :
    ∀ y : ℝ, f y = ∑' x : ℤ, ψ (y - x) * f x := by
  intro y
  have hξabs : ∀ {ξ : ℝ}, ξ ∈ Set.Icc (-c0) c0 → |ξ| ≤ c0 := by
    intro ξ hξ
    rw [abs_le]; exact ⟨(Set.mem_Icc.mp hξ).1, (Set.mem_Icc.mp hξ).2⟩
  have hξabs2 : ∀ {ξ : ℝ}, ξ ∈ Set.Icc (-(1/2:ℝ)) (1/2) → |ξ| ≤ 1/2 := by
    intro ξ hξ
    rw [abs_le]; exact ⟨(Set.mem_Icc.mp hξ).1, (Set.mem_Icc.mp hξ).2⟩
  -- Fourier inversion for `f`
  have hA : f y = ∫ ξ, phi (ξ * y) * (𝓕 f) ξ := by
    have hinv : (𝓕⁻ (𝓕 f) : SchwartzMap ℝ ℂ) = f := fourierInv_fourier_eq _
    rw [← congrFun (congrArg DFunLike.coe hinv) y]
    rw [SchwartzMap.fourierInv_coe (𝓕 f)]
    rw [Real.fourierInv_eq']
    apply integral_congr_ae; filter_upwards with ξ
    rw [Real.inner_apply, smul_eq_mul]
    congr 1
    rw [phi]; congr 1; push_cast; ring
  set S : ℝ → ℂ := fun ξ => ∑' n : ℤ, f (n:ℝ) * phi (-((n:ℝ)*ξ)) with hSdef
  have hS_eq : ∀ ξ, S ξ = ∑' k : ℤ, (𝓕 f) (ξ + (k:ℝ)) := by
    intro ξ; rw [hSdef]; exact poisson_modulated f ξ
  -- The pointwise identity `𝓕f ξ = 𝓕ψ ξ * S ξ`
  have hmain : ∀ ξ, (𝓕 f) ξ = (𝓕 ψ) ξ * S ξ := by
    intro ξ
    rw [hS_eq ξ]
    by_cases h1 : ξ ∈ Set.Icc (-c0) c0
    · have hsingle : (∑' k : ℤ, (𝓕 f) (ξ + (k:ℝ))) = (𝓕 f) ξ := by
        rw [tsum_eq_single 0]
        · simp
        · intro k hk
          exact hfs _ (fun hmem =>
            int_eq_zero_of_shift_mem (c0:=c0) (B:=c0) (by linarith) (hξabs h1) hmem hk)
      rw [hsingle, hψ1 ξ h1, one_mul]
    · rw [hfs ξ h1]
      by_cases h2 : ξ ∈ Set.Icc (-(1/2:ℝ)) (1/2)
      · have hzero : (∑' k : ℤ, (𝓕 f) (ξ + (k:ℝ))) = 0 := by
          rw [show (0:ℂ) = (∑' k : ℤ, (0:ℂ)) by simp]
          apply tsum_congr; intro k
          by_cases hk : k = 0
          · subst hk; simp only [Int.cast_zero, add_zero]; exact hfs ξ h1
          · exact hfs _ (fun hmem =>
              int_eq_zero_of_shift_mem (c0:=c0) (B:=1/2) (by linarith) (hξabs2 h2) hmem hk)
        rw [hzero, mul_zero]
      · rw [hψs ξ h2, zero_mul]
  set F : ℤ → ℝ → ℂ :=
    fun n ξ => phi (ξ*y) * ((𝓕 ψ) ξ * (f (n:ℝ) * phi (-((n:ℝ)*ξ)))) with hFdef
  set C : ℝ := ∫ ξ, ‖(𝓕 ψ) ξ‖ with hCdef
  -- Integrability of the summands
  have hFint : ∀ n : ℤ, Integrable (F n) := by
    intro n
    have hcont : Continuous (fun ξ : ℝ => phi (ξ*y) * (f (n:ℝ) * phi (-((n:ℝ)*ξ)))) := by
      apply Continuous.mul (continuous_phi.comp (by fun_prop))
      exact Continuous.mul continuous_const (continuous_phi.comp (by fun_prop))
    have hbd : ∀ ξ : ℝ, ‖phi (ξ*y) * (f (n:ℝ) * phi (-((n:ℝ)*ξ)))‖ ≤ ‖f (n:ℝ)‖ := by
      intro ξ; simp [norm_phi]
    have h := ((𝓕 ψ).integrable (μ := volume)).mul_bdd hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hbd)
    refine h.congr (Filter.Eventually.of_forall (fun ξ => ?_))
    rw [hFdef]; ring
  -- Summability of the integrals of the norms
  have hFsum : Summable (fun n : ℤ => ∫ ξ, ‖F n ξ‖) := by
    have hCeq : ∀ n : ℤ, (∫ ξ, ‖F n ξ‖) = C * ‖f (n:ℝ)‖ := by
      intro n
      have hpt : ∀ ξ : ℝ, ‖F n ξ‖ = ‖(𝓕 ψ) ξ‖ * ‖f (n:ℝ)‖ := by
        intro ξ; rw [hFdef]; simp [norm_phi]
      have hii : (∫ ξ, ‖F n ξ‖) = ∫ ξ, ‖(𝓕 ψ) ξ‖ * ‖f (n:ℝ)‖ :=
        integral_congr_ae (Filter.Eventually.of_forall hpt)
      rw [hii, integral_mul_const]
    exact ((schwartz_summable_norm f).mul_left C).congr (fun n => (hCeq n).symm)
  have hite := integral_tsum_of_summable_integral_norm hFint hFsum
  have hpoint : ∀ ξ : ℝ, phi (ξ * y) * ((𝓕 ψ) ξ * S ξ) = ∑' n : ℤ, F n ξ := by
    intro ξ
    rw [hSdef, ← tsum_mul_left, ← tsum_mul_left]
  -- Interchange sum and integral
  have e2 : (∫ ξ, phi (ξ * y) * ((𝓕 ψ) ξ * S ξ))
      = ∑' n : ℤ, f (n:ℝ) * ∫ ξ, (𝓕 ψ) ξ * phi (ξ * (y - (n:ℝ))) := by
    have hint : (∫ ξ, phi (ξ * y) * ((𝓕 ψ) ξ * S ξ)) = ∫ ξ, (∑' n : ℤ, F n ξ) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun ξ => hpoint ξ))
    rw [hint, ← hite]
    apply tsum_congr; intro n
    rw [← integral_const_mul]
    apply integral_congr_ae; filter_upwards with ξ
    simp only [hFdef]
    have hkey : phi (ξ*y) * phi (-((n:ℝ)*ξ)) = phi (ξ*(y-(n:ℝ))) := by
      rw [← phi_add]; congr 1; ring
    calc phi (ξ*y) * ((𝓕 ψ) ξ * (f (n:ℝ) * phi (-((n:ℝ)*ξ))))
        = f (n:ℝ) * ((𝓕 ψ) ξ * (phi (ξ*y) * phi (-((n:ℝ)*ξ)))) := by ring
      _ = f (n:ℝ) * ((𝓕 ψ) ξ * phi (ξ*(y-(n:ℝ)))) := by rw [hkey]
  -- Fourier inversion for `ψ`
  have e3 : ∀ n : ℤ, (∫ ξ, (𝓕 ψ) ξ * phi (ξ * (y - (n:ℝ)))) = ψ (y - (n:ℝ)) := by
    intro n
    have hinv : (𝓕⁻ (𝓕 ψ) : SchwartzMap ℝ ℂ) = ψ := fourierInv_fourier_eq _
    rw [← congrFun (congrArg DFunLike.coe hinv) (y - (n:ℝ))]
    rw [SchwartzMap.fourierInv_coe (𝓕 ψ)]
    rw [Real.fourierInv_eq']
    apply integral_congr_ae; filter_upwards with ξ
    rw [Real.inner_apply, smul_eq_mul]
    rw [show phi (ξ*(y-(n:ℝ))) = Complex.exp (↑(2*Real.pi*(ξ*(y-(n:ℝ)))) * Complex.I) by
      rw [phi]; congr 1; push_cast; ring]
    ring
  rw [hA]
  have hint2 : (∫ ξ, phi (ξ * y) * (𝓕 f) ξ) = ∫ ξ, phi (ξ * y) * ((𝓕 ψ) ξ * S ξ) :=
    integral_congr_ae (Filter.Eventually.of_forall (fun ξ => by simp only [hmain ξ]))
  rw [hint2, e2]
  refine tsum_congr (fun n => ?_)
  rw [e3 n, mul_comm]

end

end Commons.Analysis.Fourier
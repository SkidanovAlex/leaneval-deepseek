import Mathlib
import Submission.Work.Core.Basic

namespace Work.Sampling

open LeanEval.Analysis.CKMRVInterpolation
open Filter Topology
open scoped SchwartzMap

/-!
# Rapid decay of the CKMRV samples of a Schwartz function

For a complex-valued Schwartz function `f` on `R^n`, the four sequences obtained by
sampling `f`, its Fourier transform, and the radial derivatives of both at the radii
`sqrt (2 * k)` are rapidly decreasing.

The point of the estimate is that the sample point `realIncl (sqrt (2 * k))` has
norm `sqrt (2 * k)`, so the Schwartz seminorm bound
`‖x‖ ^ N * ‖g x‖ ≤ C` with `N = 2 * (m + 1)` gives
`k ^ (m + 1) * ‖g x_k‖ ≤ C / 2 ^ (m + 1)` for every `k`, which is more than enough
decay after dividing by `k` once (and a squeezing argument finishes).

The radial derivative is the Fréchet derivative in the direction `realIncl 1`, via
the chain rule along the (linear) curve `realIncl : ℝ → R^n`.
-/

/-- `realIncl r` is the `r`-th multiple of the first coordinate vector. -/
lemma realIncl_eq_single {n : ℕ} [NeZero n] (r : ℝ) :
    realIncl (n := n) r = EuclideanSpace.single (0 : Fin n) r := by
  apply PiLp.ext
  intro i
  simp [EuclideanSpace.single, PiLp.single, Pi.single, Function.update_apply]

/-- `realIncl` is linear in its argument. -/
lemma realIncl_eq_smul {n : ℕ} [NeZero n] (r : ℝ) :
    realIncl (n := n) r = r • realIncl (n := n) 1 := by
  rw [realIncl_eq_single (n := n) r, realIncl_eq_single (n := n) 1]
  simp only [EuclideanSpace.single, PiLp.single]
  rw [← WithLp.toLp_smul]
  congr 1
  rw [← Pi.single_smul]
  simp

/-- The curve `realIncl : ℝ → R^n` has derivative `realIncl 1` everywhere. -/
lemma hasDerivAt_realIncl {n : ℕ} [NeZero n] (r : ℝ) :
    HasDerivAt (realIncl (n := n)) (realIncl (n := n) 1) r := by
  have hfun : (realIncl (n := n)) = fun s : ℝ => s • realIncl (n := n) 1 :=
    funext fun s => realIncl_eq_smul (n := n) s
  rw [hfun]
  simpa using (hasDerivAt_id r).smul_const (realIncl (n := n) 1)

/-- The norm of `realIncl r` is `|r|`. -/
lemma realIncl_norm {n : ℕ} [NeZero n] (r : ℝ) : ‖realIncl (n := n) r‖ = |r| := by
  rw [realIncl_eq_single, PiLp.norm_single, Real.norm_eq_abs]

/-- `realIncl 1` is a unit vector. -/
lemma realIncl_norm_one {n : ℕ} [NeZero n] : ‖realIncl (n := n) 1‖ = 1 := by
  rw [realIncl_norm, abs_one]

/-- Chain rule for the composition `g ∘ realIncl`: the ordinary derivative at `r` is
the Fréchet derivative of `g` at `realIncl r` applied to the direction `realIncl 1`. -/
lemma deriv_comp_realIncl {n : ℕ} [NeZero n] {g : EuclideanSpace ℝ (Fin n) → ℂ}
    {g' : EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ} {r : ℝ}
    (hg : HasFDerivAt g g' (realIncl (n := n) r)) :
    deriv (g ∘ realIncl (n := n)) r = g' (realIncl (n := n) 1) := by
  have h := hg.comp_hasDerivAt r (hasDerivAt_realIncl (n := n) r)
  rw [h.deriv]

/-- Sampling a Schwartz function at the points `realIncl (sqrt (2 * k))` yields a
rapidly decreasing sequence. -/
lemma schwartz_sampling_decay {n : ℕ} [NeZero n]
    (g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (m : ℕ) :
    Tendsto (fun k : ℕ => (k : ℝ)^m * ‖g (realIncl (Real.sqrt (2 * (k:ℝ))))‖) atTop (𝓝 0) := by
  set C : ℝ := (SchwartzMap.seminorm ℂ (2 * (m + 1)) 0 g) with hC
  have hpow : (0:ℝ) < 2 ^ (m + 1) := by positivity
  have hbound : ∀ k : ℕ,
      (k : ℝ) ^ (m + 1) * ‖g (realIncl (Real.sqrt (2 * (k:ℝ))))‖ ≤ C / 2 ^ (m+1) := by
    intro k
    have h1 : ‖realIncl (n := n) (Real.sqrt (2 * (k:ℝ)))‖ ^ (2 * (m + 1)) *
        ‖iteratedFDeriv ℝ 0 (⇑g) (realIncl (n := n) (Real.sqrt (2 * (k:ℝ))))‖ ≤ C := by
      rw [hC]; exact SchwartzMap.le_seminorm ℂ (2*(m+1)) 0 g _
    rw [norm_iteratedFDeriv_zero, realIncl_norm, abs_of_nonneg (Real.sqrt_nonneg _)] at h1
    have hs : (Real.sqrt (2 * (k:ℝ))) ^ (2 * (m+1)) = 2^(m+1) * (k:ℝ)^(m+1) := by
      rw [pow_mul, Real.sq_sqrt (by positivity), mul_pow]
    rw [hs] at h1
    rw [le_div_iff₀ hpow]
    calc (k:ℝ)^(m+1) * ‖g (realIncl (Real.sqrt (2 * (k:ℝ))))‖ * 2^(m+1)
        = 2^(m+1) * (k:ℝ)^(m+1) * ‖g (realIncl (Real.sqrt (2 * (k:ℝ))))‖ := by ring
      _ ≤ C := h1
  refine squeeze_zero' (f := fun k : ℕ => (k:ℝ)^m * ‖g (realIncl (Real.sqrt (2 * (k:ℝ))))‖)
    (g := fun k : ℕ => (C / 2^(m+1)) / (k:ℝ)) ?_ ?_ ?_
  · exact Eventually.of_forall fun k => mul_nonneg (pow_nonneg (Nat.cast_nonneg k) m) (norm_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have hkpos : 0 < (k:ℝ) := lt_of_lt_of_le one_pos hk1
    rw [le_div_iff₀ hkpos]
    calc (k:ℝ)^m * ‖g (realIncl (Real.sqrt (2 * (k:ℝ))))‖ * (k:ℝ)
        = (k:ℝ)^(m+1) * ‖g (realIncl (Real.sqrt (2 * (k:ℝ))))‖ := by rw [pow_succ']; ring
      _ ≤ C / 2^(m+1) := hbound k
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

/-- Sampling the directional derivative of a Schwartz function along `realIncl` at the
points `realIncl (sqrt (2 * k))` yields a rapidly decreasing sequence. -/
lemma schwartz_decay_fderiv {n : ℕ} [NeZero n]
    (g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (m : ℕ) :
    Tendsto (fun k : ℕ => (k : ℝ)^m *
      ‖fderiv ℝ (⇑g) (realIncl (Real.sqrt (2 * (k:ℝ)))) (realIncl (n := n) 1)‖) atTop (𝓝 0) := by
  set C : ℝ := (SchwartzMap.seminorm ℂ (2 * (m + 1)) 1 g) with hC
  have hpow : (0:ℝ) < 2 ^ (m + 1) := by positivity
  have hbound : ∀ k : ℕ, (k : ℝ) ^ (m + 1) *
      ‖fderiv ℝ (⇑g) (realIncl (Real.sqrt (2 * (k:ℝ)))) (realIncl (n := n) 1)‖ ≤ C / 2 ^ (m+1) := by
    intro k
    have h1 := SchwartzMap.le_seminorm ℂ (2 * (m + 1)) 1 g (realIncl (n := n) (Real.sqrt (2 * (k:ℝ))))
    rw [norm_iteratedFDeriv_one, realIncl_norm, abs_of_nonneg (Real.sqrt_nonneg _)] at h1
    have hs : (Real.sqrt (2 * (k:ℝ))) ^ (2 * (m+1)) = 2^(m+1) * (k:ℝ)^(m+1) := by
      rw [pow_mul, Real.sq_sqrt (by positivity), mul_pow]
    rw [hs] at h1
    rw [le_div_iff₀ hpow]
    have hop : ‖fderiv ℝ (⇑g) (realIncl (Real.sqrt (2 * (k:ℝ)))) (realIncl (n := n) 1)‖
        ≤ ‖fderiv ℝ (⇑g) (realIncl (Real.sqrt (2 * (k:ℝ))))‖ := by
      calc _ ≤ ‖fderiv ℝ (⇑g) (realIncl (Real.sqrt (2 * (k:ℝ))))‖ * ‖realIncl (n := n) 1‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = _ := by rw [realIncl_norm_one, mul_one]
    calc (k:ℝ)^(m+1) * ‖fderiv ℝ (⇑g) (realIncl (Real.sqrt (2 * (k:ℝ)))) (realIncl (n := n) 1)‖ * 2^(m+1)
        ≤ (k:ℝ)^(m+1) * ‖fderiv ℝ (⇑g) (realIncl (Real.sqrt (2 * (k:ℝ))))‖ * 2^(m+1) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hop (pow_nonneg (Nat.cast_nonneg k) _)) (le_of_lt hpow)
      _ = 2^(m+1) * (k:ℝ)^(m+1) * ‖fderiv ℝ (⇑g) (realIncl (Real.sqrt (2 * (k:ℝ))))‖ := by ring
      _ ≤ C := h1
  refine squeeze_zero' (f := fun k : ℕ => (k : ℝ)^m *
      ‖fderiv ℝ (⇑g) (realIncl (Real.sqrt (2 * (k:ℝ)))) (realIncl (n := n) 1)‖)
    (g := fun k : ℕ => (C / 2^(m+1)) / (k:ℝ)) ?_ ?_ ?_
  · exact Eventually.of_forall fun k => mul_nonneg (pow_nonneg (Nat.cast_nonneg k) m) (norm_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with k hk
    have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have hkpos : 0 < (k:ℝ) := lt_of_lt_of_le one_pos hk1
    rw [le_div_iff₀ hkpos]
    calc (k:ℝ)^m * ‖fderiv ℝ (⇑g) (realIncl (Real.sqrt (2 * (k:ℝ)))) (realIncl (n := n) 1)‖ * (k:ℝ)
        = (k:ℝ)^(m+1) * ‖fderiv ℝ (⇑g) (realIncl (Real.sqrt (2 * (k:ℝ)))) (realIncl (n := n) 1)‖ := by rw [pow_succ']; ring
      _ ≤ C / 2^(m+1) := hbound k
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

/-- The coercion from `Set.Ici k₀` to `ℕ` tends to infinity. -/
lemma tendsto_subtype_Ici_val_atTop (k₀ : ℕ) :
    Tendsto (fun k : Set.Ici k₀ => (k.1 : ℕ)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  exact ⟨⟨max k₀ b, Set.mem_Ici.mpr (le_max_left _ _)⟩, fun a ha => le_trans (le_max_right _ _) ha⟩

/-- **Rapid decay of the CKMRV samples.** Every complex Schwartz function on `R^n` has
rapidly decreasing samples: its values, its Fourier transform's values, and the radial
derivatives of both, at the radii `sqrt (2 * k)`. -/
theorem rapidlyDecreasing_coeffs (n k₀ : ℕ) [NeZero n]
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    RapidlyDecreasingSamples (coeffs n k₀ f) := by
  have hcoe := tendsto_subtype_Ici_val_atTop k₀
  intro j m
  fin_cases j
  · simpa [coeffs, Function.comp_def] using (schwartz_sampling_decay f m).comp hcoe
  · simpa [coeffs, Function.comp_def] using
      (schwartz_sampling_decay (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f) m).comp hcoe
  · have hfun : ∀ k : Set.Ici k₀, coeffs n k₀ f (k, 2)
        = fderiv ℝ (⇑f) (realIncl (Real.sqrt (2 * (k:ℝ)))) (realIncl (n:=n) 1) := by
      intro k
      simp only [coeffs]
      exact deriv_comp_realIncl (SchwartzMap.hasFDerivAt f _)
    simpa [hfun, Function.comp_def] using (schwartz_decay_fderiv f m).comp hcoe
  · have hfun : ∀ k : Set.Ici k₀, coeffs n k₀ f (k, 3)
        = fderiv ℝ (⇑(FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f))
            (realIncl (Real.sqrt (2 * (k:ℝ)))) (realIncl (n:=n) 1) := by
      intro k
      simp only [coeffs]
      exact deriv_comp_realIncl (SchwartzMap.hasFDerivAt _ _)
    simpa [hfun, Function.comp_def] using
      (schwartz_decay_fderiv (FourierTransform.fourierCLM ℂ (𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f) m).comp hcoe

end Work.Sampling

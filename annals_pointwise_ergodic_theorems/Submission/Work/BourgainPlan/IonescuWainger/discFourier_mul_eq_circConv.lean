import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FreqArc

open MeasureTheory Finset
open scoped BigOperators

namespace Work.BourgainPlan.IonescuWainger

/-! ## Auxiliary facts about the Fourier monomials on the circle

The proof of `discFourier_mul_eq_circConv` is the standard "the Fourier transform turns products into
convolutions" computation, carried out explicitly as a finite sum:

`∫_𝕋 𝓕h η · 𝓕k (ξ - η) dη = Σ_{n,m} h n k m ∫_𝕋 e^{2πi n η} e^{2πi m (ξ - η)} dη
 = Σ_{n,m} h n k m e^{2πi m ξ} ∫_𝕋 e^{2πi (n-m) η} dη = Σ_n h n k n e^{2πi n ξ}`,

using `∫_𝕋 e^{2πi j η} dη = δ_{j,0}` (the orthonormality of the characters) and the elementary
identity `e^{2πi n η} e^{2πi m (ξ - η)} = e^{2πi m ξ} e^{2πi (n - m) η}`. -/

namespace DiscFourierMul

/-- Orthonormality of the characters on `𝕋 = ℝ/ℤ`: the integral of `fourier j` is `1` for `j = 0`
and `0` otherwise.  This is the `j = 0` coefficient of Mathlib's `fourierCoeff_fourier`. -/
lemma integral_fourier (j : ℤ) :
    (∫ η : Circle, fourier j η ∂AddCircle.haarAddCircle) = if j = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := 1) (0 : ℤ)) (-j)
  simp only [fourierCoeff, Pi.single_apply, neg_neg, neg_eq_zero] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp

/-- The characters are multiplicative in their argument: `e^{2πi m (x+y)} = e^{2πi m x} e^{2πi m y}`. -/
lemma fourier_add_arg (m : ℤ) (x y : Circle) :
    fourier m (x + y) = fourier m x * fourier m y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- `fourier m (ξ - η) = fourier m ξ · fourier (-m) η`, i.e. `e^{2πi m (ξ-η)} = e^{2πi m ξ}
e^{-2πi m η}`. -/
lemma fourier_sub (m : ℤ) (ξ η : Circle) :
    fourier m (ξ - η) = fourier m ξ * fourier (-m) η := by
  have h2 : fourier m η * fourier (-m) η = 1 := by
    rw [← fourier_add, add_neg_cancel, fourier_zero]
  calc fourier m (ξ - η)
      = fourier m (ξ - η) * (fourier m η * fourier (-m) η) := by rw [h2, mul_one]
    _ = fourier m (ξ - η) * fourier m η * fourier (-m) η := by ring
    _ = fourier m ((ξ - η) + η) * fourier (-m) η := by rw [← fourier_add_arg]
    _ = fourier m ξ * fourier (-m) η := by rw [sub_add_cancel]

/-- The key pointwise identity behind the convolution theorem:
`e^{2πi n η} e^{2πi m (ξ-η)} = e^{2πi m ξ} e^{2πi (n-m) η}`. -/
lemma fourier_mul_fourier_sub (n m : ℤ) (ξ η : Circle) :
    fourier n η * fourier m (ξ - η) = fourier m ξ * fourier (n - m) η := by
  have h1 : fourier n η * fourier m (ξ - η) = fourier m ξ * fourier (n + -m) η := by
    rw [fourier_sub, mul_left_comm, ← fourier_add]
  simpa [sub_eq_add_neg] using h1

/-- The integral of a product of two characters: `∫_𝕋 e^{2πi n η} e^{2πi m (ξ-η)} dη = δ_{n,m}
e^{2πi n ξ}`. -/
lemma integral_fourier_mul_fourier_sub (n m : ℤ) (ξ : Circle) :
    (∫ η : Circle, fourier n η * fourier m (ξ - η) ∂AddCircle.haarAddCircle)
      = if n = m then fourier n ξ else 0 := by
  rw [show (fun η : Circle => fourier n η * fourier m (ξ - η))
      = fun η => fourier m ξ * fourier (n - m) η from
        funext fun η => fourier_mul_fourier_sub n m ξ η]
  rw [integral_const_mul, integral_fourier]
  by_cases hnm : n = m
  · subst hnm; simp
  · have h : n - m ≠ 0 := sub_ne_zero.mpr hnm
    simp [h, hnm]

/-- A product of two characters with arbitrary coefficients is integrable on the compact circle. -/
lemma integrable_fourier_prod (n m : ℤ) (ξ : Circle) (a b : ℂ) :
    Integrable (fun η : Circle => (a * fourier n η) * (b * fourier m (ξ - η)))
      AddCircle.haarAddCircle := by
  have hc : Continuous (fun η : Circle => (a * fourier n η) * (b * fourier m (ξ - η))) := by
    refine Continuous.mul ?_ ?_
    · exact continuous_const.mul (map_continuous (fourier n))
    · exact continuous_const.mul
        ((map_continuous (fourier m)).comp (continuous_const.sub continuous_id))
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

end DiscFourierMul

open DiscFourierMul in
/-- **The Fourier transform turns pointwise products into convolutions.**  For finitely supported
`h, k : ℤ → ℂ` and every `ξ : 𝕋 = ℝ/ℤ`,

`𝓕(h · k) ξ = (𝓕h * 𝓕k) ξ = ∫_𝕋 𝓕h η · 𝓕k (ξ − η) dη`,

where `discFourier f ξ = ∑'_n f n · e^{2πi n ξ}` (Mathlib's `fourier n ξ`) and the convolution is
`circConv` from `FreqArc.lean` with respect to the probability Haar measure `AddCircle.haarAddCircle`.

This is the Fourier-side bridge used in Tao's `ortho`(ii)/(iii) (arXiv:2008.05066, §4, "inspecting the
Fourier transform"): together with `integral_circConvFin_mul_conj_eq_zero` it converts the vanishing
of the pairing `Σ_n ∏_j ⟨f_j(n), g_j(n)⟩` of two halves of a nonce tuple into the disjointness of
the Minkowski sums of the arcs supporting the transforms.

Proof ingredients: expand both sides as finite sums over the supports
(`discFourier_eq_sum_of_support`), use `fourier n η * fourier m (ξ − η) = fourier m ξ * fourier (n−m) η`,
and Mathlib's orthonormality `orthonormal_fourier` (equivalently
`∫ η, fourier j η ∂haarAddCircle = if j = 0 then 1 else 0`). -/
theorem discFourier_mul_eq_circConv {h k : ℤ → ℂ} (hh : (Function.support h).Finite)
    (hk : (Function.support k).Finite) (ξ : Circle) :
    discFourier (fun n => h n * k n) ξ = circConv (discFourier h) (discFourier k) ξ := by
  classical
  have hhs : ∀ n, n ∉ hh.toFinset → h n = 0 := fun n hn => by
    by_contra hne; exact hn (hh.mem_toFinset.mpr hne)
  have hks : ∀ n, n ∉ hk.toFinset → k n = 0 := fun n hn => by
    by_contra hne; exact hn (hk.mem_toFinset.mpr hne)
  have h1 : discFourier (fun n => h n * k n) ξ
      = ∑ n ∈ hh.toFinset, h n * k n * fourier n ξ := by
    rw [discFourier_eq_sum_of_support (fun n hn => by rw [hhs n hn, zero_mul]) ξ]
  have h2 : circConv (discFourier h) (discFourier k) ξ
      = ∑ n ∈ hh.toFinset, h n * k n * fourier n ξ := by
    rw [circConv]
    have hA : (fun η : Circle => discFourier h η * discFourier k (ξ - η))
        = fun η : Circle => (∑ n ∈ hh.toFinset, h n * fourier n η)
            * (∑ m ∈ hk.toFinset, k m * fourier m (ξ - η)) := by
      funext η
      simp only [discFourier_eq_sum_of_support hhs η, discFourier_eq_sum_of_support hks (ξ - η)]
    have hB : (fun η : Circle => (∑ n ∈ hh.toFinset, h n * fourier n η)
            * (∑ m ∈ hk.toFinset, k m * fourier m (ξ - η)))
        = fun η : Circle => ∑ n ∈ hh.toFinset, ∑ m ∈ hk.toFinset,
            (h n * fourier n η) * (k m * fourier m (ξ - η)) := by
      funext η
      simp only [Finset.sum_mul_sum]
    rw [hA, hB]
    calc (∫ η, ∑ n ∈ hh.toFinset, ∑ m ∈ hk.toFinset,
              (h n * fourier n η) * (k m * fourier m (ξ - η))
            ∂AddCircle.haarAddCircle)
        = ∑ n ∈ hh.toFinset, ∑ m ∈ hk.toFinset,
              (∫ η, (h n * fourier n η) * (k m * fourier m (ξ - η))
                ∂AddCircle.haarAddCircle) := by
          rw [integral_finsetSum]
          · refine Finset.sum_congr rfl fun n hn => ?_
            rw [integral_finsetSum]
            intro m hm
            exact integrable_fourier_prod n m ξ (h n) (k m)
          · intro n hn
            exact integrable_finsetSum _
              (fun m hm => integrable_fourier_prod n m ξ (h n) (k m))
      _ = ∑ n ∈ hh.toFinset, ∑ m ∈ hk.toFinset,
              h n * k m * (if n = m then fourier n ξ else 0) := by
          refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
          rw [show (fun η : Circle => (h n * fourier n η) * (k m * fourier m (ξ - η)))
              = fun η => (h n * k m) * (fourier n η * fourier m (ξ - η)) from
                funext fun η => by ring]
          rw [integral_const_mul, integral_fourier_mul_fourier_sub]
      _ = ∑ n ∈ hh.toFinset, h n * k n * fourier n ξ := by
          refine Finset.sum_congr rfl fun n hn => ?_
          by_cases hnt : n ∈ hk.toFinset
          · rw [Finset.sum_eq_single n]
            · simp
            · intro m hm hmn
              rw [if_neg (Ne.symm hmn), mul_zero]
            · intro hn'; exact absurd hnt hn'
          · have hkn : k n = 0 := hks n hnt
            have hzero : ∀ m ∈ hk.toFinset,
                h n * k m * (if n = m then fourier n ξ else 0) = 0 := by
              intro m hm
              by_cases hmn : m = n
              · subst hmn; simp [hkn]
              · rw [if_neg (Ne.symm hmn), mul_zero]
            rw [Finset.sum_eq_zero hzero, hkn, mul_zero, zero_mul]
  rw [h1, h2]

end Work.BourgainPlan.IonescuWainger

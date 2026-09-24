import Mathlib
import Submission.Work.GM.S2.pair_sum_defs

/-!
# `ĥ_t(-ξ) = conj (ĥ_{-t}(ξ))`  (the reflection symmetry of `Submission.GM.hhat`)

The `S₂` area (GM §6) reflects the negative half of the `m`-sum onto the positive half
using the elementary symmetry

`ĥ_t(-ξ) = conj (ĥ_{-t}(ξ))`

of GM's Fourier transform `ĥ_t(ξ) = ∫ w(u)² u^{it} e(-ξu) du` (`Submission.GM.hhat`).

Both the phase flip `u ↦ u^{-it}` and the conjugation `e(-ξu) ↦ e(ξu)` come out of the
single pointwise identity `conj (hfun s u) = hfun (-s) u` for the integrand
`hfun s u = w(u)² u^{is}`: this is immediate off the support of `w` (both sides vanish)
and, on the support `[1,2]` where `u > 0`, follows from
`Complex.conj (u ^ z) = u ^ (conj z)` (a real positive base). Passing to the integral is
`MeasureTheory.integral_conj`, which holds for arbitrary integrands.
-/

set_option autoImplicit false

namespace Work.GM.S2

open Complex

/-- On a positive real base, complex conjugation commutes with `cpow` by flipping the
exponent. Special case of `Complex.cpow_conj` for `(u : ℂ)` with `u > 0`. -/
lemma conj_cpow_ofReal_pos {u : ℝ} (hu : 0 < u) (z : ℂ) :
    (starRingEnd ℂ) ((u : ℂ) ^ z) = (u : ℂ) ^ ((starRingEnd ℂ) z) := by
  have harg : (u : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (le_of_lt hu)]
    exact Real.pi_ne_zero.symm
  have h := Complex.cpow_conj (u : ℂ) z harg
  rw [Complex.conj_ofReal] at h
  exact h.symm

/-- The integrand of `ĥ_t` satisfies `conj (hfun s u) = hfun (-s) u` for every `u`,
because outside `[1,2]` the weight `w = bumpW` vanishes, and inside it `u > 0`. -/
lemma hfun_conj (s u : ℝ) :
    (starRingEnd ℂ) (Submission.GM.hfun s u) = Submission.GM.hfun (-s) u := by
  unfold Submission.GM.hfun
  by_cases hw : Submission.LargeValues.bumpW u = 0
  · simp [hw]
  · have hu : 0 < u := by
      have hmem : u ∈ Set.Icc 1 2 := Submission.LargeValues.bumpW_spec.2.2.1 u hw
      exact lt_of_lt_of_le zero_lt_one hmem.1
    rw [map_mul, Complex.conj_ofReal]
    congr 1
    rw [conj_cpow_ofReal_pos hu]
    congr 1
    simp [map_mul, Complex.conj_I]

/-- `𝓕 (conj ∘ f) ξ = conj (𝓕 f (-ξ))` for any `f : ℝ → ℂ`. -/
lemma fourier_conj_neg (f : ℝ → ℂ) (ξ : ℝ) :
    FourierTransform.fourier (fun u => (starRingEnd ℂ) (f u)) ξ
      = (starRingEnd ℂ) (FourierTransform.fourier f (-ξ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  rw [← integral_conj]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with v
  rw [smul_eq_mul, smul_eq_mul, map_mul, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring_nf

/-- **The reflection symmetry of `ĥ`**: `ĥ_t(-ξ) = conj (ĥ_{-t}(ξ))`. -/
theorem hhat_neg_symm (t ξ : ℝ) :
    Submission.GM.hhat t (-ξ) = (starRingEnd ℂ) (Submission.GM.hhat (-t) ξ) := by
  have hfun_eq : (fun u => (starRingEnd ℂ) (Submission.GM.hfun (-t) u))
      = Submission.GM.hfun t := by
    funext u
    simpa using hfun_conj (-t) u
  show FourierTransform.fourier (Submission.GM.hfun t) (-ξ)
      = (starRingEnd ℂ) (FourierTransform.fourier (Submission.GM.hfun (-t)) ξ)
  rw [← hfun_eq, fourier_conj_neg]
  simp

end Work.GM.S2

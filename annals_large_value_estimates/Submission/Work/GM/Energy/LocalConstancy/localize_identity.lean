import Mathlib
import Submission.Work.GM.Energy.LocalConstancy.LocalizeSetup

/-!
# The localization identity behind GM Lemma 11.3

For the *normalised* Dirichlet polynomial
`G(u) = Σ_{n∈[N,2N]} a_n (n/N)^{iu}` (whose frequencies `log (n/N) / (2π)` all lie in `[0,1]`)
and the fixed flat-top bump `ψ = Work.GM.Energy.RLocal.PsiBump` -- which equals `1` on `[0,1]`
and has rapidly decaying Fourier transform -- we have the exact identity

  `G(t) = ∫ ξ, 𝓕ψ(ξ) * G(t+ξ) dξ`.

Indeed, expanding `G(t+ξ) = Σ_n a_n exp (i (t+ξ) log (n/N))` and inserting Fourier inversion
`ψ(s) = ∫ ξ, exp (2πi ξ s) 𝓕ψ(ξ) dξ` at `s = log (n/N)/(2π)` turns the right-hand side into
`Σ_n a_n exp (i t log (n/N)) · ψ(log (n/N)/(2π)) = Σ_n a_n exp (i t log (n/N)) = G(t)`,
because `ψ = 1` at `log (n/N)/(2π)` for every `n ∈ [N,2N]`.

This is the "exact identity" half of the proof of GM Lemma 11.3 (locality of a Dirichlet
polynomial); the other half restricts the `ξ`-integral to `|ξ| ≤ K` using the Fourier decay.
-/

namespace Work.GM.Energy.LocalConstancy

open Complex Finset MeasureTheory
open scoped BigOperators FourierTransform
open Work.GM.Energy.RLocal

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Small helpers about the character `e(x) = exp (2πix)` -/

/-- `e(x) = exp (2πix)`: the character `Real.fourierChar` as a complex number. -/
noncomputable def locIdEf (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

lemma locIdEf_norm (x : ℝ) : ‖locIdEf x‖ = 1 := by
  rw [locIdEf, Complex.norm_exp]
  have h : (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I).re = 0 := by simp
  rw [h, Real.exp_zero]

lemma locIdEf_continuous : Continuous locIdEf := by
  unfold locIdEf
  fun_prop

lemma locIdEf_add (a b : ℝ) : locIdEf (a + b) = locIdEf a * locIdEf b := by
  unfold locIdEf
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma locIdEf_eq_fourierChar (x : ℝ) : locIdEf x = ((Real.fourierChar x : Circle) : ℂ) := by
  rw [locIdEf, ← Real.fourierChar_apply]

lemma locIdFourierChar_smul (a : ℝ) (y : ℂ) : Real.fourierChar a • y = locIdEf a * y := by
  rw [Circle.smul_def, smul_eq_mul, locIdEf_eq_fourierChar]

/-- For a positive base, the complex power `x^{iu}` is the character `e` at `u log x / (2π)`. -/
lemma locIdCpow_I (r : ℝ) (hr : 0 < r) (u : ℝ) :
    ((r : ℂ) ^ (Complex.I * (u : ℂ))) = locIdEf (u * (Real.log r / (2 * Real.pi))) := by
  rw [Complex.cpow_def_of_ne_zero (by simpa using hr.ne'), ← Complex.ofReal_log hr.le]
  unfold locIdEf
  congr 1
  push_cast
  field_simp

/-! ## The frequencies of the normalised polynomial -/

/-- The frequency of the `n`-th term of the normalised polynomial: `log (n/N) / (2π)`. -/
noncomputable def locIdD (N n : ℕ) : ℝ := Real.log ((n : ℝ) / (N : ℝ)) / (2 * Real.pi)

lemma locIdBasePos (N n : ℕ) (hN : 1 ≤ N) (hn : n ∈ Finset.Icc N (2 * N)) :
    (0 : ℝ) < (n : ℝ) / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hn1 : (1 : ℕ) ≤ n := le_trans hN (Finset.mem_Icc.mp hn).1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  exact div_pos hnpos hNpos

/-- The flat-top bump is `1` at every frequency `log (n/N)/(2π)`, `N ≤ n ≤ 2N`. -/
lemma locIdPsi_eq_one (N n : ℕ) (hN : 1 ≤ N) (hn : n ∈ Finset.Icc N (2 * N)) :
    PsiBump (locIdD N n) = 1 := by
  show ((psiBump (Real.log ((n : ℝ) / (N : ℝ)) / (2 * Real.pi)) : ℝ) : ℂ) = 1
  rw [Loc.psiBump_log_div_eq_one hN hn]
  norm_num

/-! ## The identity -/

theorem localize_identity (N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℂ) (t : ℝ) :
    Work.GM.Energy.LocalConstancy.Loc.G N a t
      = ∫ ξ, FourierTransform.fourier Work.GM.Energy.RLocal.PsiBump ξ
              * Work.GM.Energy.LocalConstancy.Loc.G N a (t + ξ) := by
  -- `G` written with the character `e`
  have hG : ∀ u : ℝ, Loc.G N a u = ∑ n ∈ Finset.Icc N (2 * N),
      a n * locIdEf (u * locIdD N n) := by
    intro u
    unfold Loc.G
    refine Finset.sum_congr rfl fun n hn => ?_
    exact congrArg (fun z => a n * z) (locIdCpow_I _ (locIdBasePos N n hN hn) u)
  -- integrability of the summands
  have hbase : ∀ n : ℕ, Integrable (fun ξ : ℝ => locIdEf (ξ * locIdD N n) * 𝓕 PsiBump ξ) := by
    intro n
    refine Integrable.mono' PsiBump_fourier_integrable.norm ?_ ?_
    · exact ((locIdEf_continuous.comp (continuous_id.mul continuous_const)).mul
        continuous_fourier_PsiBump).aestronglyMeasurable
    · filter_upwards with ξ
      simp [locIdEf_norm]
  -- pointwise rewriting of the integrand
  have hpoint : (∫ ξ, 𝓕 PsiBump ξ * Loc.G N a (t + ξ))
      = ∫ ξ, ∑ n ∈ Finset.Icc N (2 * N),
          (a n * locIdEf (t * locIdD N n))
            * (locIdEf (ξ * locIdD N n) * 𝓕 PsiBump ξ) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    show 𝓕 PsiBump ξ * Loc.G N a (t + ξ)
      = ∑ n ∈ Finset.Icc N (2 * N),
          (a n * locIdEf (t * locIdD N n)) * (locIdEf (ξ * locIdD N n) * 𝓕 PsiBump ξ)
    rw [hG (t + ξ), Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have h1 : locIdEf ((t + ξ) * locIdD N n)
        = locIdEf (t * locIdD N n) * locIdEf (ξ * locIdD N n) := by
      rw [show (t + ξ) * locIdD N n = t * locIdD N n + ξ * locIdD N n by ring, locIdEf_add]
    rw [h1]
    ring
  -- swap the finite sum and the integral
  have hswap : (∫ ξ, ∑ n ∈ Finset.Icc N (2 * N),
          (a n * locIdEf (t * locIdD N n))
            * (locIdEf (ξ * locIdD N n) * 𝓕 PsiBump ξ))
      = ∑ n ∈ Finset.Icc N (2 * N), (a n * locIdEf (t * locIdD N n))
          * ∫ ξ, locIdEf (ξ * locIdD N n) * 𝓕 PsiBump ξ := by
    have h := MeasureTheory.integral_finsetSum (s := Finset.Icc N (2 * N))
      (f := fun n ξ => (a n * locIdEf (t * locIdD N n)) * (locIdEf (ξ * locIdD N n) * 𝓕 PsiBump ξ))
      (fun n _ => (hbase n).const_mul _)
    rw [h]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [MeasureTheory.integral_const_mul]
  -- evaluate each term by Fourier inversion
  have hval : ∀ n ∈ Finset.Icc N (2 * N),
      (∫ ξ, locIdEf (ξ * locIdD N n) * 𝓕 PsiBump ξ) = 1 := by
    intro n hn
    have h1 : (∫ ξ, locIdEf (ξ * locIdD N n) * 𝓕 PsiBump ξ) = PsiBump (locIdD N n) := by
      rw [PsiBump_fourier_inversion (locIdD N n)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      show locIdEf (ξ * locIdD N n) * 𝓕 PsiBump ξ
        = Real.fourierChar (inner ℝ ξ (locIdD N n)) • 𝓕 PsiBump ξ
      rw [locIdFourierChar_smul, Real.inner_apply]
    rw [h1, locIdPsi_eq_one N n hN hn]
  calc Loc.G N a t = ∑ n ∈ Finset.Icc N (2 * N), a n * locIdEf (t * locIdD N n) := hG t
    _ = ∑ n ∈ Finset.Icc N (2 * N), (a n * locIdEf (t * locIdD N n))
          * (∫ ξ, locIdEf (ξ * locIdD N n) * 𝓕 PsiBump ξ) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [hval n hn, mul_one]
    _ = ∫ ξ, 𝓕 PsiBump ξ * Loc.G N a (t + ξ) := (hpoint.trans hswap).symm

end Work.GM.Energy.LocalConstancy

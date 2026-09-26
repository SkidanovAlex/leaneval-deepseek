import Mathlib
import Submission.Work.Kernels.ModerateGrowth

/-!
# Vanishing of low `q`-expansion coefficients from exponential decay

Cohn--Kumar--Miller--Radchenko--Viazovska (Ann. of Math. 196 (2022)), in the rigidity step of
their Fourier interpolation theorem, need the following elementary consequence of Cauchy's
integral formula.

Let `F : ℍ → ℂ` be `1`-periodic, holomorphic of moderate growth (`F ∈ 𝒫`, i.e.
`Work.Kernels.InP F`) and bounded at the cusp `i∞`, and suppose that for some `m : ℕ` and `C ≥ 0`

  `‖F τ‖ ≤ C · exp (-(2π m Im τ))`   for `Im τ ≥ 1`.

Then the `q`-expansion of `F` at `i∞`, `F τ = ∑_n a_n q^n` with `q = exp (2π i τ)`, has
`a_n = 0` for every `n < m`.

The proof is the standard one: `UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral` writes `a_n`
as the integral `∫_0^1 (1/q^n) F(u + i t) du` along the horizontal line `Im = t`; there
`‖q‖ = exp (-2π t)`, so `‖1/q^n‖ = exp (2π n t)`, and the decay hypothesis gives the bound
`‖a_n‖ ≤ C · exp (2π (n - m) t)`.  As `t → ∞` the right-hand side tends to `0` whenever
`n < m`, hence `a_n = 0`.
-/

open UpperHalfPlane Filter Topology

namespace Work.Rigidity

set_option linter.unusedVariables false

/-- **Vanishing of `q`-expansion coefficients below the decay threshold.**  A `1`-periodic
holomorphic function of moderate growth on `ℍ` that decays like `exp (-(2π m Im τ))` has all
`q`-expansion coefficients of order `n < m` equal to zero. -/
theorem ExpDecayCoeffZero {F : UpperHalfPlane → ℂ} {C : ℝ} (hC : 0 ≤ C) {m : ℕ}
    (hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1)
    (hP : Work.Kernels.InP F) (hbdd : UpperHalfPlane.IsBoundedAtImInfty F)
    (hdec : ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖F τ‖ ≤ C * Real.exp (-(2 * Real.pi * (m : ℝ) * τ.im))) :
    ∀ n : ℕ, n < m → (UpperHalfPlane.qExpansion 1 F).coeff n = 0 := by
  intro n hn
  -- Bound on `a_n` along the horizontal line `Im = t`, for every `t ≥ 1`.
  have hcol : ∀ t : ℝ, 1 ≤ t →
      ‖(UpperHalfPlane.qExpansion 1 F).coeff n‖ ≤
        C * Real.exp (-(2 * Real.pi * ((m : ℝ) - n) * t)) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have hmain := UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral (h := 1) one_pos hper
      hP.1 hbdd n ht0
    rw [hmain]
    simp only [one_div, Complex.ofReal_one, inv_one, one_mul]
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := C * Real.exp (-(2 * Real.pi * ((m : ℝ) - n) * t))) ?_) ?_
    · intro u _
      have hzim : ((u : ℂ) + (t : ℂ) * ((UpperHalfPlane.I : UpperHalfPlane) : ℂ)).im = t := by
        simp [Complex.add_im, Complex.mul_im]
      set τ : ℍ := ⟨(u : ℂ) + (t : ℂ) * ((UpperHalfPlane.I : UpperHalfPlane) : ℂ),
        by rw [hzim]; exact ht0⟩ with hτdef
      have hτim : τ.im = t := by rw [hτdef]; exact hzim
      -- `‖q^n‖ = exp (-2π n t)`, hence `‖1/q^n‖ = exp (2π n t)`.
      have hqpow : ‖Function.Periodic.qParam 1 ((u : ℂ) + (t : ℂ) *
            ((UpperHalfPlane.I : UpperHalfPlane) : ℂ)) ^ n‖
          = Real.exp (-(2 * Real.pi * (n : ℝ) * t)) := by
        rw [norm_pow, Function.Periodic.norm_qParam, hzim, div_one, ← Real.exp_nat_mul]
        congr 1
        ring
      have hqnorm : ‖(Function.Periodic.qParam 1 ((u : ℂ) + (t : ℂ) *
            ((UpperHalfPlane.I : UpperHalfPlane) : ℂ)) ^ n)⁻¹‖
          = Real.exp (2 * Real.pi * (n : ℝ) * t) := by
        rw [norm_inv, hqpow, ← Real.exp_neg]
        congr 1
        ring
      rw [norm_mul, hqnorm]
      calc Real.exp (2 * Real.pi * (n : ℝ) * t) * ‖F τ‖
          ≤ Real.exp (2 * Real.pi * (n : ℝ) * t) *
              (C * Real.exp (-(2 * Real.pi * (m : ℝ) * τ.im))) := by
            apply mul_le_mul_of_nonneg_left (hdec τ ?_) (Real.exp_nonneg _)
            rw [hτim]; exact ht
        _ = C * (Real.exp (2 * Real.pi * (n : ℝ) * t) *
              Real.exp (-(2 * Real.pi * (m : ℝ) * t))) := by
            rw [hτim]; ring
        _ = C * Real.exp (2 * Real.pi * (n : ℝ) * t + -(2 * Real.pi * (m : ℝ) * t)) := by
            rw [Real.exp_add]
        _ = C * Real.exp (-(2 * Real.pi * ((m : ℝ) - n) * t)) := by
            congr 1
            ring_nf
    · simp
  -- The bound tends to `0` as `t → ∞`, because `m - n > 0`.
  have hlim : Tendsto (fun t : ℝ => C * Real.exp (-(2 * Real.pi * ((m : ℝ) - n) * t)))
      atTop (𝓝 0) := by
    have hcoef : -(2 * Real.pi * ((m : ℝ) - n)) < 0 := by
      have h : (0 : ℝ) < (m : ℝ) - n := by
        have h' : (n : ℝ) < (m : ℝ) := by exact_mod_cast hn
        linarith
      have : (0 : ℝ) < 2 * Real.pi * ((m : ℝ) - n) := by positivity
      linarith
    have hexp : Tendsto (fun t : ℝ => Real.exp (-(2 * Real.pi * ((m : ℝ) - n)) * t))
        atTop (𝓝 0) := by
      rw [Real.tendsto_exp_comp_nhds_zero]
      have h := (Filter.tendsto_const_mul_atBot_of_neg
        (r := -(2 * Real.pi * ((m : ℝ) - n))) hcoef).mpr (Filter.tendsto_id)
      refine h.congr (fun t => ?_)
      simp only [id_eq]
    have h3 : Tendsto (fun t : ℝ => C * Real.exp (-(2 * Real.pi * ((m : ℝ) - n)) * t))
        atTop (𝓝 0) := by
      simpa using hexp.const_mul C
    refine h3.congr (fun t => ?_)
    congr 1
    ring_nf
  -- Squeeze `‖a_n‖` between the constant `‖a_n‖` and a function tending to `0`.
  have hle : ‖(UpperHalfPlane.qExpansion 1 F).coeff n‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (eventually_atTop.mpr ⟨1, fun t ht => hcol t ht⟩)
  exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))

end Work.Rigidity

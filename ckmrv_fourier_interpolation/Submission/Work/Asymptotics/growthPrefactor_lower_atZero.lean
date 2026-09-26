import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atZero
import Submission.Work.Asymptotics.jInvariantFun_imagAxis_atZero

noncomputable section

open Work.Kernels

namespace Work.Asymptotics

/-! ## Auxiliary estimates near the cusp `t → 0`

We need three elementary ingredients:

* for every `M` there is `T > 0` with `M ≤ exp (2π/t)` on `(0,T]`;
* the reverse triangle inequality upgraded by `jInvariantFun_imagAxis_atZero`: the
  *difference* `j(τ) - j(it)` is itself bounded below by `(c/2) exp (2π/t)`;
* the algebra combining `‖Δ(it)‖ ≥ c t^{-12} exp(-2π/t)` with the previous point to get
  `‖Δ(τ)‖ ‖Δ(it)‖^e ‖j(τ) - j(it)‖ ≥ c' t^{-12e} exp(-2π(e-1)/t)`.
-/

/-- **Exponential domination at the cusp.**  For every `M` there is `T > 0` such that
`M ≤ exp (2π/t)` for all `0 < t ≤ T`. -/
lemma exists_le_exp_two_pi_div (M : ℝ) :
    ∃ T : ℝ, 0 < T ∧ ∀ t : ℝ, 0 < t → t ≤ T → M ≤ Real.exp (2 * Real.pi / t) := by
  refine ⟨2 * Real.pi / (Real.log (max M 1) + 1), ?_, ?_⟩
  · have h1 : (1 : ℝ) ≤ max M 1 := le_max_right M 1
    have h2 : 0 ≤ Real.log (max M 1) := Real.log_nonneg h1
    positivity
  · intro t ht htT
    have hM1 : (0 : ℝ) < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
    have hLpos : 0 < Real.log (max M 1) + 1 := by
      have h2 : 0 ≤ Real.log (max M 1) := Real.log_nonneg (le_max_right M 1)
      linarith
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hge : Real.log (max M 1) + 1 ≤ 2 * Real.pi / t := by
      have h1 : 2 * Real.pi / (2 * Real.pi / (Real.log (max M 1) + 1)) ≤ 2 * Real.pi / t :=
        div_le_div_of_nonneg_left h2pi.le ht htT
      have h2 : 2 * Real.pi / (2 * Real.pi / (Real.log (max M 1) + 1))
          = Real.log (max M 1) + 1 := by field_simp
      rwa [h2] at h1
    calc M ≤ max M 1 := le_max_left M _
      _ = Real.exp (Real.log (max M 1)) := (Real.exp_log hM1).symm
      _ ≤ Real.exp (Real.log (max M 1) + 1) :=
          Real.exp_le_exp.mpr (le_add_of_nonneg_right zero_le_one)
      _ ≤ Real.exp (2 * Real.pi / t) := Real.exp_le_exp.mpr hge

/-- **Lower bound for the difference `j(τ) - j(it)` at the cusp `t → 0`.**  Since
`‖j(it)‖ ≥ c exp(2π/t)` blows up, the reverse triangle inequality gives
`‖j(τ) - j(it)‖ ≥ (c/2) exp(2π/t)` for `t` small (half of the growth, which is what we need
to cancel the `exp(-2π/t)` from `Δ(it)`). -/
lemma jInvariantFun_sub_imagAxis_atZero (τ : UpperHalfPlane) :
    ∃ c T : ℝ, 0 < c ∧ 0 < T ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ T →
      c * Real.exp (2 * Real.pi / t)
        ≤ ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖ := by
  obtain ⟨c₂, T₂, hc₂, hT₂, hJ⟩ := jInvariantFun_imagAxis_atZero
  obtain ⟨T₃, hT₃, hle⟩ := exists_le_exp_two_pi_div (2 * ‖jInvariantFun τ‖ / c₂)
  refine ⟨c₂ / 2, min T₂ T₃, by positivity, lt_min hT₂ hT₃, ?_⟩
  intro t ht htT
  have ht₂ : t ≤ T₂ := le_trans htT (min_le_left _ _)
  have ht₃ : t ≤ T₃ := le_trans htT (min_le_right _ _)
  have hJt : c₂ * Real.exp (2 * Real.pi / t)
      ≤ ‖jInvariantFun (imagAxis t ht)‖ := hJ t ht ht₂
  have hexp : 2 * ‖jInvariantFun τ‖ ≤ c₂ * Real.exp (2 * Real.pi / t) := by
    have h := hle t ht ht₃
    rw [div_le_iff₀ hc₂] at h
    linarith
  have hsub := norm_sub_norm_le (jInvariantFun (imagAxis t ht)) (jInvariantFun τ)
  rw [norm_sub_rev] at hsub
  have hhalf : c₂ * Real.exp (2 * Real.pi / t) / 2
      ≤ ‖jInvariantFun (imagAxis t ht)‖ - ‖jInvariantFun τ‖ := by
    have h1 : c₂ * Real.exp (2 * Real.pi / t) / 2 ≤ ‖jInvariantFun (imagAxis t ht)‖ / 2 :=
      div_le_div_of_nonneg_right hJt (by norm_num)
    have h2 : ‖jInvariantFun (imagAxis t ht)‖ / 2
        ≤ ‖jInvariantFun (imagAxis t ht)‖ - ‖jInvariantFun τ‖ := by linarith
    linarith
  calc c₂ / 2 * Real.exp (2 * Real.pi / t) = c₂ * Real.exp (2 * Real.pi / t) / 2 := by ring
    _ ≤ ‖jInvariantFun (imagAxis t ht)‖ - ‖jInvariantFun τ‖ := hhalf
    _ ≤ ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖ := hsub

/-- **Algebraic assembly.**  From the two cusp estimates
`‖Δ(it)‖ ≥ c₁ t^{-12} e^{-2π/t}` and `‖j(τ) - j(it)‖ ≥ c₂ e^{2π/t}`, and `Δ(τ) ≠ 0`, deduce
`∃ c T, 0 < c ∧ 0 < T ∧ c t^{-12e} e^{-2π(e-1)/t} ≤ ‖Δ(τ)‖ ‖Δ(it)‖^e ‖j(τ) - j(it)‖`
for `0 < t ≤ T`.  The exponentials combine as `-2πe/t + 2π/t = -2π(e-1)/t`. -/
private lemma growthPrefactor_lower_aux (τ : UpperHalfPlane) (e : ℕ)
    (c₁ c₂ T₁ T₂ : ℝ) (hc₁ : 0 < c₁) (hT₁ : 0 < T₁) (hc₂ : 0 < c₂) (hT₂ : 0 < T₂)
    (hA : 0 < ‖DeltaFun τ‖)
    (hD : ∀ (t : ℝ) (ht : 0 < t), t ≤ T₁ →
      c₁ * ((t : ℝ) ^ 12)⁻¹ * Real.exp (-(2 * Real.pi / t)) ≤ ‖DeltaFun (imagAxis t ht)‖)
    (hJ : ∀ (t : ℝ) (ht : 0 < t), t ≤ T₂ →
      c₂ * Real.exp (2 * Real.pi / t)
        ≤ ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖) :
    ∃ c T : ℝ, 0 < c ∧ 0 < T ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ T →
      c * ((t : ℝ) ^ (12 * e))⁻¹ * Real.exp (-(2 * Real.pi * ((e : ℝ) - 1) / t))
        ≤ ‖DeltaFun τ‖ * ‖DeltaFun (imagAxis t ht)‖ ^ e
            * ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖ := by
  refine ⟨‖DeltaFun τ‖ * c₁ ^ e * c₂, min T₁ T₂, by positivity, lt_min hT₁ hT₂, ?_⟩
  intro t ht htT
  have ht₁ : t ≤ T₁ := le_trans htT (min_le_left _ _)
  have ht₂ : t ≤ T₂ := le_trans htT (min_le_right _ _)
  have hDt := hD t ht ht₁
  have hJt := hJ t ht ht₂
  have ht12 : (0 : ℝ) < (t : ℝ) ^ 12 := pow_pos ht 12
  have hX : 0 ≤ ((t : ℝ) ^ 12)⁻¹ * Real.exp (-(2 * Real.pi / t)) :=
    mul_nonneg (inv_nonneg.mpr ht12.le) (Real.exp_pos _).le
  have hDt' : c₁ * (((t : ℝ) ^ 12)⁻¹ * Real.exp (-(2 * Real.pi / t)))
      ≤ ‖DeltaFun (imagAxis t ht)‖ := by rw [← mul_assoc]; exact hDt
  have hpow : (c₁ * (((t : ℝ) ^ 12)⁻¹ * Real.exp (-(2 * Real.pi / t)))) ^ e
      ≤ ‖DeltaFun (imagAxis t ht)‖ ^ e :=
    pow_le_pow_left₀ (mul_nonneg hc₁.le hX) hDt' e
  rw [mul_pow, mul_pow] at hpow
  have h1 : ((t : ℝ) ^ 12)⁻¹ ^ e = ((t : ℝ) ^ (12 * e))⁻¹ := by rw [inv_pow, ← pow_mul]
  have h2 : (Real.exp (-(2 * Real.pi / t))) ^ e
      = Real.exp (-(2 * Real.pi * (e : ℝ) / t)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [h1, h2, ← mul_assoc] at hpow
  have hexpadd : Real.exp (-(2 * Real.pi * (e : ℝ) / t)) * Real.exp (2 * Real.pi / t)
      = Real.exp (-(2 * Real.pi * ((e : ℝ) - 1) / t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hE : 0 ≤ c₂ * Real.exp (2 * Real.pi / t) := mul_nonneg hc₂.le (Real.exp_pos _).le
  have hDS : c₁ ^ e * ((t : ℝ) ^ (12 * e))⁻¹ * Real.exp (-(2 * Real.pi * (e : ℝ) / t))
        * (c₂ * Real.exp (2 * Real.pi / t))
      ≤ ‖DeltaFun (imagAxis t ht)‖ ^ e
        * ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖ :=
    mul_le_mul hpow hJt hE (pow_nonneg (norm_nonneg _) e)
  have hmain : ‖DeltaFun τ‖ * (c₁ ^ e * ((t : ℝ) ^ (12 * e))⁻¹
        * Real.exp (-(2 * Real.pi * (e : ℝ) / t)) * (c₂ * Real.exp (2 * Real.pi / t)))
      ≤ ‖DeltaFun τ‖ * (‖DeltaFun (imagAxis t ht)‖ ^ e
        * ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖) :=
    mul_le_mul_of_nonneg_left hDS (norm_nonneg _)
  calc ‖DeltaFun τ‖ * c₁ ^ e * c₂ * ((t : ℝ) ^ (12 * e))⁻¹
        * Real.exp (-(2 * Real.pi * ((e : ℝ) - 1) / t))
      = ‖DeltaFun τ‖ * (c₁ ^ e * ((t : ℝ) ^ (12 * e))⁻¹
          * Real.exp (-(2 * Real.pi * (e : ℝ) / t))
          * (c₂ * Real.exp (2 * Real.pi / t))) := by
        rw [← hexpadd]; ring
    _ ≤ ‖DeltaFun τ‖ * (‖DeltaFun (imagAxis t ht)‖ ^ e
          * ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖) := hmain
    _ = ‖DeltaFun τ‖ * ‖DeltaFun (imagAxis t ht)‖ ^ e
          * ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖ := by ring

/-- **Lower bound for the CKMRV divisor at the cusp `t → 0`.**  For every `τ` the divisor
`Δ(τ)Δ(it)^e(j(τ)-j(it))` is bounded below on `t ≤ T` by
`c · t^{-12e} · exp(-2π(e-1)/t)` (`e = 1` for `d = 8`, `e = 2` for `d = 24`); this is the
`t → 0` counterpart of `Work.Asymptotics.growthPrefactor_lower_atTop`, obtained by transferring
the cusp asymptotics of `Δ` and `j` across `S`. -/
theorem growthPrefactor_lower_atZero (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) :
    ∃ c T : ℝ, 0 < c ∧ 0 < T ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ T →
      c * ((t : ℝ) ^ (12 * (if d = 8 then 1 else 2)))⁻¹
          * Real.exp (-(2 * Real.pi * ((if d = 8 then 0 else 1 : ℕ)) / t))
        ≤ ‖Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht)‖ := by
  obtain ⟨c₁, C₁, T₁, hc₁, hC₁, hT₁, hD⟩ := DeltaFun_imagAxis_atZero
  obtain ⟨c₂, T₂, hc₂, hT₂, hJ⟩ := jInvariantFun_sub_imagAxis_atZero τ
  have hA : 0 < ‖DeltaFun τ‖ :=
    norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)
  obtain ⟨c, T, hc, hT, hb⟩ :=
    growthPrefactor_lower_aux τ (if d = 8 then 1 else 2) c₁ c₂ T₁ T₂ hc₁ hT₁ hc₂ hT₂ hA
      (fun t ht h => (hD t ht h).1) hJ
  refine ⟨c, T, hc, hT, ?_⟩
  intro t ht htT
  have h := hb t ht htT
  have hcoe : (((if d = 8 then 1 else 2 : ℕ)) : ℝ) - 1
      = ((if d = 8 then 0 else 1 : ℕ) : ℝ) := by
    by_cases h8 : d = 8
    · rw [if_pos h8, if_pos h8]; norm_num
    · rw [if_neg h8, if_neg h8]; norm_num
  rw [hcoe] at h
  have hnorm : ‖growthPrefactor d τ (imagAxis t ht)‖
      = ‖DeltaFun τ‖ * ‖DeltaFun (imagAxis t ht)‖ ^ (if d = 8 then 1 else 2)
        * ‖jInvariantFun τ - jInvariantFun (imagAxis t ht)‖ := by
    rw [growthPrefactor, norm_mul, norm_mul, norm_pow]
  rw [hnorm]
  exact h

end Work.Asymptotics

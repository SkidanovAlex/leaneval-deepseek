import Mathlib
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.DeltaFun_imagAxis_atTop
import Submission.Work.Asymptotics.jInvariantFun_imagAxis_atTop

namespace Work.Asymptotics

open UpperHalfPlane

/-! ## The factorisation of the CKMRV divisor

The CKMRV divisor is `Δ(τ)Δ(z)^e(j(τ)−j(z))` with `e = 1` for `d = 8` and `e = 2` for
`d = 24`.  Using `Δ(z)j(z) = E₄(z)³` it factors as

`Δ(τ) · Δ(z)^{e-1} · (Δ(z)j(τ) − E₄(z)³)`,

with `e - 1 = 0` for `d = 8` and `e - 1 = 1` for `d = 24` (in fact for every `d` the same
identity holds, because `growthPrefactor` also uses the exponent `2` in the `d ≠ 8` branch). -/
private lemma growthPrefactor_eq_factor (d : ℕ) (τ z : ℍ) :
    Work.Kernels.growthPrefactor d τ z =
      Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun z ^ (if d = 8 then 0 else 1) *
        (Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun τ - Work.Kernels.E4Fun z ^ 3) := by
  have h := Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun z
  by_cases hd : d = 8
  · simp only [Work.Kernels.growthPrefactor, hd, if_true, pow_one, pow_zero, mul_one]
    rw [← h]; ring
  · simp only [Work.Kernels.growthPrefactor, hd, if_false, pow_one]
    rw [← h]; ring

/-- **The cusp limit of the off-diagonal factor.**  For `τ` fixed, the quantity
`Δ(z)j(τ) − E₄(z)³` tends to `−1` along `z = it → i∞`; in particular it is bounded below in
norm by `1/16` on a tail.  This is where `E₄(it) → 1` and `Δ(it) → 0` are used. -/
private lemma eventually_norm_Delta_mul_j_sub_E4_cubed (τ : ℍ) :
    ∃ T : ℝ, 0 < T ∧ ∀ (t : ℝ) (ht : 0 < t), T ≤ t →
      (1 / 16 : ℝ) ≤
        ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) * Work.Kernels.jInvariantFun τ
          - Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) ^ 3‖ := by
  -- the quantitative cusp asymptotics of `Δ` and `E₄`
  obtain ⟨c0, C, T1, hc0, hC, hT1, hD⟩ := Work.Asymptotics.DeltaFun_imagAxis_atTop
  obtain ⟨A, hA⟩ := Work.Asymptotics.exists_bound_norm_E4Fun_atImInfty
  -- `C exp(-2πt) ‖j τ‖ → 0`, so it is `≤ 1/16` eventually
  have hdec : ∃ T2 : ℝ, 0 < T2 ∧ ∀ t : ℝ, T2 ≤ t →
      C * Real.exp (-(2 * Real.pi * t)) * ‖Work.Kernels.jInvariantFun τ‖ ≤ 1 / 16 := by
    have h : Filter.Tendsto
        (fun t : ℝ => C * Real.exp (-(2 * Real.pi * t)) * ‖Work.Kernels.jInvariantFun τ‖)
        Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun t : ℝ => 2 * Real.pi * t) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop (by positivity) Filter.tendsto_id
      have h3 : Filter.Tendsto (fun t : ℝ => -(2 * Real.pi * t)) Filter.atTop Filter.atBot :=
        Filter.tendsto_neg_atTop_atBot.comp h2
      have h4 : Filter.Tendsto (fun t : ℝ => Real.exp (-(2 * Real.pi * t))) Filter.atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp h3
      simpa using (h4.const_mul C).mul_const ‖Work.Kernels.jInvariantFun τ‖
    have hev : ∀ᶠ t : ℝ in Filter.atTop,
        C * Real.exp (-(2 * Real.pi * t)) * ‖Work.Kernels.jInvariantFun τ‖ ≤ 1 / 16 :=
      h.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 16))
    obtain ⟨T0, hT0⟩ := Filter.eventually_atTop.mp hev
    exact ⟨max T0 1, lt_of_lt_of_le one_pos (le_max_right _ _),
      fun t ht' => hT0 t (le_trans (le_max_left _ _) ht')⟩
  obtain ⟨T2, hT2pos, hT2⟩ := hdec
  refine ⟨max (max T1 A) T2, by positivity, fun t ht hT => ?_⟩
  have him : (Work.Kernels.imagAxis t ht).im = t := by simp [Work.Kernels.imagAxis]
  have hT1' : T1 ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hA' : A ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT2' : T2 ≤ t := le_trans (le_max_right _ _) hT
  have hDm := (hD t ht hT1').2
  have hEm : (1 / 2 : ℝ) ≤ ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht)‖ :=
    hA _ (by rw [him]; exact hA')
  have hE3 : (1 / 8 : ℝ) ≤ ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) ^ 3‖ := by
    rw [norm_pow]
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hEm 3
    rw [show ((1 : ℝ) / 2) ^ 3 = 1 / 8 by norm_num] at hpow
    exact hpow
  have hDj : ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) * Work.Kernels.jInvariantFun τ‖
      ≤ 1 / 16 := by
    rw [norm_mul]
    exact le_trans (mul_le_mul_of_nonneg_right hDm (norm_nonneg _)) (hT2 t hT2')
  have htri : ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) ^ 3‖
      - ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) * Work.Kernels.jInvariantFun τ‖
      ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) * Work.Kernels.jInvariantFun τ
          - Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) ^ 3‖ := by
    have h1 := neg_le_abs
      (‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) * Work.Kernels.jInvariantFun τ‖
        - ‖Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) ^ 3‖)
    have h2 := abs_norm_sub_norm_le
      (Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) * Work.Kernels.jInvariantFun τ)
      (Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) ^ 3)
    linarith
  linarith [hE3, hDj, htri]

/-- **Lower bound for the CKMRV divisor at the cusp `t → ∞`.**  For every `τ` the divisor of
the kernels, `Δ(τ)Δ(it)^e(j(τ)-j(it))` (`e = 1` for `d = 8`, `e = 2` for `d = 24`), is bounded
below on the tail `t ≥ T` by a constant times `‖Δ(it)‖^{e-1}`; in particular, for `d = 8` it is
bounded below by a positive constant, while for `d = 24` it decays like `Δ(it)`, which is
exactly the rate that makes the contour integral converge for `|r| > √2`.  The proof uses
`Δ(z)j(z) = E₄(z)³` together with `Work.Asymptotics.DeltaFun_imagAxis_atTop` and
`E₄(it) → 1`. -/
theorem growthPrefactor_lower_atTop (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) :
    ∃ c T : ℝ, 0 < c ∧ 0 < T ∧ ∀ (t : ℝ) (ht : 0 < t), T ≤ t →
      c * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 0 else 1) ≤
        ‖Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht)‖ := by
  obtain ⟨T, hTpos, hbnd⟩ := eventually_norm_Delta_mul_j_sub_E4_cubed τ
  refine ⟨‖Work.Kernels.DeltaFun τ‖ / 16, T,
    div_pos (norm_pos_iff.mpr (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero τ)) (by norm_num),
    hTpos, fun t ht hT => ?_⟩
  have hw := hbnd t ht hT
  -- factor the divisor and take norms
  have hfac : ‖Work.Kernels.growthPrefactor d τ (Work.Kernels.imagAxis t ht)‖ =
      ‖Work.Kernels.DeltaFun τ‖
        * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 0 else 1)
        * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) * Work.Kernels.jInvariantFun τ
            - Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) ^ 3‖ := by
    rw [growthPrefactor_eq_factor d τ (Work.Kernels.imagAxis t ht)]
    simp only [norm_mul, norm_pow]
  rw [hfac]
  have hk : 0 ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 0 else 1) :=
    pow_nonneg (norm_nonneg _) _
  calc ‖Work.Kernels.DeltaFun τ‖ / 16
        * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 0 else 1)
      = (‖Work.Kernels.DeltaFun τ‖
          * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 0 else 1))
          * (1 / 16) := by ring
    _ ≤ (‖Work.Kernels.DeltaFun τ‖
          * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 0 else 1))
          * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) * Work.Kernels.jInvariantFun τ
              - Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) ^ 3‖ :=
        mul_le_mul_of_nonneg_left hw (mul_nonneg (norm_nonneg _) hk)
    _ = ‖Work.Kernels.DeltaFun τ‖
          * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ ^ (if d = 8 then 0 else 1)
          * ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) * Work.Kernels.jInvariantFun τ
              - Work.Kernels.E4Fun (Work.Kernels.imagAxis t ht) ^ 3‖ := by ring

end Work.Asymptotics

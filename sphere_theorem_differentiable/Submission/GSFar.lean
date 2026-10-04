import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The dyadic "farness propagation" lemma (pure real analysis)

If `F : ℝ → ℝ` is continuous on `[0,s]`, exceeds a threshold `c` at both endpoints, and is
*midpoint-closed above the threshold* (both `F a > c` and `F b > c` imply `F ((a+b)/2) > c` for
`a < b` in `[0,s]`), then `F ≥ c` everywhere on `[0,s]`.

The proof is the classical dyadic argument: an induction on `n` shows that all the dyadic points
`k s / 2^n` are *strictly* above `c`, and every point of `[0,s]` is the limit of such points (of
`⌊t 2^n / s⌋ s / 2^n`), so continuity gives `F ≥ c`.

This is the abstract form of the "farness propagation" step of the Grove–Shiohama critical point
theory: with `c = π/2` and `F t = d(p, γ t)` along a minimising geodesic, the midpoint-closure is
`GSConcaveSeg.midpoint_far`.
-/

set_option maxHeartbeats 800000

namespace Submission.GSFar

open Filter Set
open scoped Topology

/-- **Dyadic farness propagation.** -/
theorem le_of_midpoint_of_continuousOn
    {F : ℝ → ℝ} {s c : ℝ} (hs : 0 ≤ s) (hcont : ContinuousOn F (Set.Icc 0 s))
    (h0 : c < F 0) (h1 : c < F s)
    (hmid : ∀ a b, a ∈ Set.Icc (0:ℝ) s → b ∈ Set.Icc (0:ℝ) s → a < b → c < F a → c < F b →
      c < F ((a + b) / 2)) :
    ∀ t ∈ Set.Icc (0:ℝ) s, c ≤ F t := by
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · -- degenerate case `s = 0`
    intro t ht
    rw [Set.mem_Icc] at ht
    have hts : t ≤ 0 := by rw [hs0]; exact ht.2
    have ht0 : t = 0 := le_antisymm hts ht.1
    rw [ht0]
    exact h0.le
  · have key : ∀ n : ℕ, ∀ k : ℕ, k ≤ 2 ^ n → c < F ((k : ℝ) * s / (2 : ℝ) ^ n) := by
      intro n
      induction n with
      | zero =>
        intro k hk
        have hk1 : k ≤ 1 := by simpa using hk
        interval_cases k
        · simpa using h0
        · simpa using h1
      | succ n ih =>
        intro k hk
        have hdn : (0:ℝ) < (2:ℝ) ^ n := by positivity
        rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
        · -- `k = 2 j`
          have hk' : 2 * j ≤ 2 ^ (n + 1) := by rw [hj, ← two_mul] at hk; exact hk
          rw [pow_succ] at hk'
          have hjle : j ≤ 2 ^ n := by omega
          have hgoal : (k : ℝ) * s / (2 : ℝ) ^ (n + 1) = (j : ℝ) * s / (2 : ℝ) ^ n := by
            rw [hj, pow_succ]; push_cast
            field_simp
            ring
          rw [hgoal]
          exact ih j hjle
        · -- `k = 2 j + 1`
          have hk' : 2 * j + 1 ≤ 2 ^ (n + 1) := by rw [← hj]; exact hk
          rw [pow_succ] at hk'
          have hjle : j ≤ 2 ^ n := by omega
          have hj1le : j + 1 ≤ 2 ^ n := by omega
          have hjn : (j : ℝ) ≤ (2 : ℝ) ^ n := by
            have h := (Nat.cast_le (α := ℝ)).mpr hjle
            simpa [Nat.cast_pow] using h
          have hj1n : ((j : ℝ) + 1) ≤ (2 : ℝ) ^ n := by
            have h := (Nat.cast_le (α := ℝ)).mpr hj1le
            simpa [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using h
          have ha : ((j : ℝ) * s / (2 : ℝ) ^ n) ∈ Set.Icc (0:ℝ) s := by
            refine ⟨by positivity, ?_⟩
            rw [div_le_iff₀ hdn]
            calc (j : ℝ) * s ≤ (2 : ℝ) ^ n * s := mul_le_mul_of_nonneg_right hjn hs
              _ = s * (2 : ℝ) ^ n := by ring
          have hb : (((j : ℝ) + 1) * s / (2 : ℝ) ^ n) ∈ Set.Icc (0:ℝ) s := by
            refine ⟨by positivity, ?_⟩
            rw [div_le_iff₀ hdn]
            calc ((j : ℝ) + 1) * s ≤ (2 : ℝ) ^ n * s := mul_le_mul_of_nonneg_right hj1n hs
              _ = s * (2 : ℝ) ^ n := by ring
          have hab : (j : ℝ) * s / (2 : ℝ) ^ n < ((j : ℝ) + 1) * s / (2 : ℝ) ^ n := by
            rw [div_lt_div_iff_of_pos_right hdn]
            exact mul_lt_mul_of_pos_right (by linarith [show (0:ℝ) ≤ (j:ℝ) from Nat.cast_nonneg j]) hspos
          have hL : c < F ((j : ℝ) * s / (2 : ℝ) ^ n) := ih j hjle
          have hR : c < F (((j : ℝ) + 1) * s / (2 : ℝ) ^ n) := by
            have h := ih (j + 1) hj1le
            simpa [Nat.cast_add, Nat.cast_one] using h
          have hres := hmid _ _ ha hb hab hL hR
          have hgoal : ((j : ℝ) * s / (2 : ℝ) ^ n + ((j : ℝ) + 1) * s / (2 : ℝ) ^ n) / 2
              = (k : ℝ) * s / (2 : ℝ) ^ (n + 1) := by
            rw [hj, pow_succ]; push_cast
            field_simp
            ring
          rw [← hgoal]
          exact hres
    intro t ht
    rw [Set.mem_Icc] at ht
    obtain ⟨ht0, hts⟩ := ht
    set kn : ℕ → ℕ := fun n => Nat.floor (t * (2:ℝ) ^ n / s) with hkndef
    set xn : ℕ → ℝ := fun n => (kn n : ℝ) * s / (2:ℝ) ^ n with hxndef
    have hdn : ∀ n : ℕ, (0:ℝ) < (2:ℝ) ^ n := fun n => by positivity
    have hub : ∀ n, (kn n : ℝ) ≤ t * (2:ℝ) ^ n / s := fun n =>
      Nat.floor_le (by positivity)
    have hlb : ∀ n, t * (2:ℝ) ^ n / s < (kn n : ℝ) + 1 := fun n => Nat.lt_floor_add_one _
    have h_le : ∀ n, xn n ≤ t := by
      intro n
      have h := hub n
      have hsq : t * (2:ℝ) ^ n / s * (s / (2:ℝ) ^ n) = t := by
        field_simp
      calc xn n = (kn n : ℝ) * (s / (2:ℝ) ^ n) := by rw [hxndef]; ring
        _ ≤ (t * (2:ℝ) ^ n / s) * (s / (2:ℝ) ^ n) :=
            mul_le_mul_of_nonneg_right h (by positivity)
        _ = t := hsq
    have h_lt : ∀ n, t < ((kn n : ℝ) + 1) * s / (2:ℝ) ^ n := by
      intro n
      have h := hlb n
      have hsq : t * (2:ℝ) ^ n / s * (s / (2:ℝ) ^ n) = t := by
        field_simp
      calc t = t * (2:ℝ) ^ n / s * (s / (2:ℝ) ^ n) := hsq.symm
        _ < ((kn n : ℝ) + 1) * (s / (2:ℝ) ^ n) :=
            mul_lt_mul_of_pos_right h (by positivity)
        _ = ((kn n : ℝ) + 1) * s / (2:ℝ) ^ n := by ring
    have hkn2 : ∀ n, kn n ≤ 2 ^ n := by
      intro n
      have h2 : t * (2:ℝ) ^ n / s ≤ (2:ℝ) ^ n := by
        rw [div_le_iff₀ hspos]
        calc t * (2:ℝ) ^ n ≤ s * (2:ℝ) ^ n := mul_le_mul_of_nonneg_right hts (by positivity)
          _ = (2:ℝ) ^ n * s := by ring
      have h3 : (kn n : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
        rw [Nat.cast_pow, Nat.cast_ofNat]
        exact le_trans (hub n) h2
      exact_mod_cast h3
    have htend : Tendsto (fun n : ℕ => s / (2:ℝ) ^ n) atTop (𝓝 0) := by
      have h : Tendsto (fun n : ℕ => ((2:ℝ) ^ n)⁻¹) atTop (𝓝 0) :=
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)).inv_tendsto_atTop
      have h2 := h.const_mul s
      simpa only [mul_zero, div_eq_mul_inv] using h2
    have hconv : Tendsto xn atTop (𝓝 t) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) htend
      have h1 : (kn n : ℝ) * s / (2:ℝ) ^ n ≤ t := h_le n
      have h2 : t < (kn n : ℝ) * s / (2:ℝ) ^ n + s / (2:ℝ) ^ n := by
        have h2' := h_lt n
        have heq : ((kn n : ℝ) + 1) * s / (2:ℝ) ^ n
            = (kn n : ℝ) * s / (2:ℝ) ^ n + s / (2:ℝ) ^ n := by ring
        linarith [heq.le, heq.ge]
      show ‖xn n - t‖ ≤ s / (2:ℝ) ^ n
      rw [show xn n = (kn n : ℝ) * s / (2:ℝ) ^ n from rfl]
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      linarith
    have hmem : ∀ n, xn n ∈ Set.Icc (0:ℝ) s := by
      intro n
      refine ⟨by rw [hxndef]; positivity, ?_⟩
      exact le_trans (h_le n) hts
    have hxnn : Tendsto xn atTop (𝓝[Set.Icc (0:ℝ) s] t) :=
      tendsto_nhdsWithin_iff.mpr ⟨hconv, Eventually.of_forall hmem⟩
    have hF : Tendsto (fun n => F (xn n)) atTop (𝓝 (F t)) :=
      Filter.Tendsto.comp
        (show Tendsto F (𝓝[Set.Icc (0:ℝ) s] t) (𝓝 (F t)) from
          hcont.continuousWithinAt (Set.mem_Icc.mpr ⟨ht0, hts⟩)) hxnn
    exact ge_of_tendsto' hF (fun n => (key n (kn n) (hkn2 n)).le)


/-- **The right derivative of the model distance at `t = 0`.**  For `r ∈ (0,π)` the function
`t ↦ arccos (cos t cos r + sin t sin r cos θ)` leaves `r` with right derivative `-cos θ`.  This is
the infinitesimal form of the hinge comparison ("the cosine of the angle between `v` and a shortest
direction to `p` is `≤ -α` when `d(p,σ t) ≥ d(p,x) + α t`"). -/
theorem tendsto_arccos_model_sub_div (r θ : ℝ) (hr : 0 < r) (hrπ : r < Real.pi) :
    Filter.Tendsto
      (fun t : ℝ =>
        (Real.arccos (Real.cos t * Real.cos r + Real.sin t * Real.sin r * Real.cos θ) - r) / t)
      (𝓝[>] (0:ℝ)) (𝓝 (-Real.cos θ)) := by
  set u : ℝ → ℝ :=
    (fun t : ℝ => Real.cos t * Real.cos r) + (fun t : ℝ => Real.sin t * Real.sin r * Real.cos θ)
    with hudef
  have hu0 : u 0 = Real.cos r := by simp [hudef]
  have hsinpos : 0 < Real.sin r := Real.sin_pos_of_pos_of_lt_pi hr hrπ
  have hcos1 : Real.cos r ≠ 1 := by
    intro h
    have h2 : Real.sin r ^ 2 = 0 := by
      have hs := Real.sin_sq_add_cos_sq r
      rw [h] at hs; norm_num at hs ⊢; linarith
    have h3 : Real.sin r = 0 := by nlinarith [sq_nonneg (Real.sin r), hsinpos]
    linarith
  have hcosm1 : Real.cos r ≠ -1 := by
    intro h
    have h2 : Real.sin r ^ 2 = 0 := by
      have hs := Real.sin_sq_add_cos_sq r
      rw [h] at hs; norm_num at hs ⊢; linarith
    have h3 : Real.sin r = 0 := by nlinarith [sq_nonneg (Real.sin r), hsinpos]
    linarith
  have hdu : HasDerivAt u (Real.sin r * Real.cos θ) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => Real.cos t * Real.cos r) (-Real.sin 0 * Real.cos r) 0 :=
      (Real.hasDerivAt_cos 0).mul_const (Real.cos r)
    have h2 : HasDerivAt (fun t : ℝ => Real.sin t * Real.sin r * Real.cos θ)
        (Real.cos 0 * Real.sin r * Real.cos θ) 0 :=
      ((Real.hasDerivAt_sin 0).mul_const (Real.sin r)).mul_const (Real.cos θ)
    have h1' : HasDerivAt (fun t : ℝ => Real.cos t * Real.cos r) 0 0 := by
      simpa using h1
    have h2' : HasDerivAt (fun t : ℝ => Real.sin t * Real.sin r * Real.cos θ)
        (Real.sin r * Real.cos θ) 0 := by
      simpa using h2
    have h := h1'.add h2'
    rw [hudef]
    simpa using h
  have hdarccos : HasDerivAt Real.arccos (-(1 / Real.sqrt (1 - (Real.cos r) ^ 2))) (u 0) := by
    rw [hu0]
    exact Real.hasDerivAt_arccos hcosm1 hcos1
  have hval : (-(1 / Real.sqrt (1 - (Real.cos r) ^ 2))) * (Real.sin r * Real.cos θ)
      = -Real.cos θ := by
    have hsq : 1 - (Real.cos r) ^ 2 = (Real.sin r) ^ 2 := by
      have hs := Real.sin_sq_add_cos_sq r; linarith
    rw [hsq, Real.sqrt_sq hsinpos.le]
    field_simp
  have hg : HasDerivAt (Real.arccos ∘ u) (-Real.cos θ) 0 :=
    (hdarccos.comp 0 hdu).congr_deriv hval
  have hlim := hg.tendsto_slope_zero_right
  have hfun : (fun t : ℝ => t⁻¹ • ((Real.arccos ∘ u) (0 + t) - (Real.arccos ∘ u) 0))
      = fun t : ℝ =>
        (Real.arccos (Real.cos t * Real.cos r + Real.sin t * Real.sin r * Real.cos θ) - r) / t := by
    funext t
    simp only [Function.comp_apply, zero_add, smul_eq_mul, div_eq_mul_inv, hu0,
      Real.arccos_cos hr.le hrπ.le]
    rw [mul_comm]
    rfl
  rwa [hfun] at hlim

end Submission.GSFar

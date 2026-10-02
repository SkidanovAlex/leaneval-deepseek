import Submission.EFL.S12Params

/-!
# §12: the numeric side conditions of the Type B branch

This module fixes the constants of the Type B branch of §12 as
`ρ = ρ_abs = 10⁻⁵`, `ε = 10⁻⁴`, `κ = 1/2` and `γ = γ₂`, where the relevant
constant hierarchy comes from `s12_step1`
(`γ₂ ≤ 10⁻²⁴`, `δ ≤ γ₂`, `σ ≤ δ`, `γ₁ ≤ σ¹⁰/10²⁵⁰`, `β ≤ γ₁`,
`32 ≤ βr₁`, `r₁ < β(r₀-1)`, `r₁ < γ₁(r₀-1)/4`).

The structure `S12BNum` collects *all* the numeric facts the assembly of the
Type B branch needs; they all hold for `n` large.
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- **The numeric side conditions of the Type B branch of §12.**  The constants
are `ρ = ρ_abs = 10⁻⁵`, `ε = 10⁻⁴`, `κ = 1/2`; `γ` is `γ₂` and `δ` the
extremality parameter of `IsTypeB` (with `δ ≤ 10⁻²⁴`). -/
structure S12BNum (n : ℕ) (r₁ r₀ : ℕ) (β γ δ ξ : ℝ) : Prop where
  /-- the numeric hierarchy of §12 -/
  hm : S12Margins n r₁ r₀ β γ (1 / 10 ^ 5) (1 / 10 ^ 5) ξ (1 / 10 ^ 4) (1 / 2)
  /-- `2ρ(n-1)+1 ≤ εn`: the Type B conjunct of the reservoir disjunction -/
  hmargB : 2 * (1 / 10 ^ 5) * ((n : ℝ) - 1) + 1 ≤ (1 / 10 ^ 4) * (n : ℝ)
  /-- `3 ≤ (1-δ)√n`: the hypothesis of (EP3) -/
  h3 : 3 ≤ (1 - δ) * Real.sqrt (n : ℝ)
  /-- `15γ^{1/2} + ξ ≤ ρε/2`: `(eqn:bound_prev_col)` / UC1 -/
  h15ρ : 15 * Real.sqrt γ + ξ ≤ (1 / 10 ^ 5) * (1 / 10 ^ 4) / 2
  /-- `8 ≤ ρε r₀`: the numeric hypothesis `hUCnum2` -/
  h8r₀ : 8 ≤ (1 / 10 ^ 5) * (1 / 10 ^ 4) * (r₀ : ℝ)
  /-- `4 ≤ δ r₀`: `|C_w| ≤ 2n/r₀ ≤ (δ/2)n` -/
  hδr₀ : 4 ≤ δ * (r₀ : ℝ)
  /-- `14δ + 15γ^{1/2} ≤ ρ`: `|C_final| ≥ 14δn` -/
  hCfin : 14 * δ + 15 * Real.sqrt γ ≤ 1 / 10 ^ 5
  /-- `β ≤ δ/2`: the colour-side Hall bound -/
  hβδ2 : β ≤ δ / 2
  /-- `2δ < 1 - 10ε`: (EP3) / UC4 -/
  hδ2 : 2 * δ < 1 - 10 * (1 / 10 ^ 4)
  /-- `4 ≤ ρεn`: UC1 -/
  h4ρεn : 4 ≤ (1 / 10 ^ 5) * (1 / 10 ^ 4) * (n : ℝ)
  /-- `δ ≤ ε`: `|V(φ⁻¹(c)) ∩ U| ≤ δn ≤ εn` for a huge class -/
  hδε : δ ≤ 1 / 10 ^ 4
  /-- `δ ≤ 1/2` -/
  hδ1 : δ ≤ 1 / 2
  /-- `δ < 3/10` -/
  hδ3 : δ < 3 / 10
  /-- `3 ≤ εn`: `s12_step3_typeB` -/
  hεn3 : 3 ≤ (1 / 10 ^ 4) * (n : ℝ)
  /-- the C1/C3 numeric hypotheses of the nibble (`NibbleStatement`) -/
  hnum3 : (Dparam n (1 / 10 ^ 5) : ℝ) + (D'param (Dparam n (1 / 10 ^ 5)) γ : ℝ) +
      (2 * γ * (n : ℝ) + 32 / β ^ 2) ≤ (n : ℝ)

end

end ErdosFaberLovaszConjecture

namespace ErdosFaberLovaszConjecture

open Classical
open Commons.Analysis.Real

noncomputable section

variable {n : ℕ}

/-- **The numeric side conditions of the Type B branch hold eventually.**  With
the constant hierarchy of `s12_step1` (`γ ≤ 10⁻²⁴`, `δ ≤ 10⁻²⁴`, `σ ≤ δ`,
`γ₁ ≤ σ¹⁰/10²⁵⁰`, `β ≤ γ₁`, `32 ≤ βr₁`, `r₁ ≤ β(r₀-1)`,
`r₁ < γ₁(r₀-1)/4`) there are `ξ > 0` and `N` such that `S12BNum n r₁ r₀ β γ δ ξ`
holds for every `n ≥ N`. -/
theorem exists_S12BNum {r₁ r₀ : ℕ} {β γ δ σ γ₁ : ℝ}
    (hβ0 : 0 < β) (hβγ₁ : β ≤ γ₁) (hβsq : 8 * β ≤ γ ^ 2)
    (hβ4 : β ≤ γ ^ 4 / 10 ^ 12)
    (hγ₁σ : γ₁ ≤ σ ^ 10 / 10 ^ 250)
    (hσ0 : 0 < σ) (hσ24 : σ ≤ (10 : ℝ) ^ (-24 : ℤ)) (hσδ : σ ≤ δ) (hδ0 : 0 < δ)
    (hδ24 : δ ≤ (10 : ℝ) ^ (-24 : ℤ)) (hδγ : δ ≤ γ) (hγ0 : 0 < γ)
    (hγ24 : γ ≤ (10 : ℝ) ^ (-24 : ℤ))
    (hr₁2 : 2 ≤ r₁) (hr₀2 : 2 ≤ r₀) (hr₁r₀ : r₁ < r₀)
    (hβr1 : 32 ≤ β * (r₁ : ℝ)) (hr₁β₀ : (r₁ : ℝ) ≤ β * ((r₀ : ℝ) - 1))
    (hr₀big : (r₁ : ℝ) < γ₁ / 4 * ((r₀ : ℝ) - 1)) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ N : ℕ, ∀ n ≥ N, S12BNum n r₁ r₀ β γ δ ξ := by
  classical
  have hσ24' : σ ≤ 1 / 10 ^ 24 := by have := hσ24; norm_num at this ⊢; exact this
  have hδ24' : δ ≤ 1 / 10 ^ 24 := by have := hδ24; norm_num at this ⊢; exact this
  have hγ24' : γ ≤ 1 / 10 ^ 24 := by have := hγ24; norm_num at this ⊢; exact this
  have hδ24m : δ * 10 ^ 24 ≤ 1 :=
    (le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 24)).mp hδ24'
  have hσ1 : σ ≤ 1 := by linarith only [hσ24']
  have hδ1' : δ ≤ 1 / 2 := by linarith only [hδ24']
  have hδ3' : δ < 3 / 10 := by linarith only [hδ24']
  have hγ1 : γ ≤ 1 := by linarith only [hγ24']
  -- `β` and `γ₁` are minuscule
  have hσ10 : σ ^ 9 ≤ 1 / 2 := by
    have h : σ ^ 9 ≤ (1 / 10 ^ 24 : ℝ) ^ 9 := pow_le_pow_left₀ (le_of_lt hσ0) hσ24' 9
    have h2 : ((1 / 10 ^ 24 : ℝ) ^ 9) = 1 / 10 ^ 216 := by norm_num
    have h3 : (1 / 10 ^ 216 : ℝ) ≤ 1 / 2 := by norm_num
    rw [h2] at h
    linarith only [h, h3]
  have hσpow : σ ^ 10 / 10 ^ 250 ≤ σ / 2 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 250)]
    have h1 : σ * σ ^ 9 ≤ σ * (1 / 2) := mul_le_mul_of_nonneg_left hσ10 (le_of_lt hσ0)
    have h1' : σ * (1 / 2) = σ / 2 := by ring
    have h2 : (σ / 2) * 1 ≤ (σ / 2) * 10 ^ 250 := by
      have hc : (1 : ℝ) ≤ 10 ^ 250 := by norm_num
      exact mul_le_mul_of_nonneg_left hc (by positivity)
    have h3 : σ ^ 10 = σ * σ ^ 9 := by ring
    linarith only [h1, h1', h2, h3]
  have hσpowσ : σ ^ 10 / 10 ^ 250 ≤ σ := by
    have h1 : σ ^ 10 ≤ σ := by
      have h := pow_le_pow_of_le_one (le_of_lt hσ0) hσ1 (show 1 ≤ 10 by norm_num)
      simpa using h
    have h2 : (1 : ℝ) ≤ 10 ^ 250 := by norm_num
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 250)]
    nlinarith only [h1, h2, hσ0]
  have hβσ : β ≤ σ / 2 := le_trans (le_trans hβγ₁ hγ₁σ) hσpow
  have hβδ2 : β ≤ δ / 2 := by linarith only [hβσ, hσδ, hσ0.le]
  have hβ1 : β ≤ 1 := by linarith only [hβσ, hσ1, le_of_lt hσ0]
  have hβγ : β ≤ γ := by linarith only [hβσ, hσδ, hδγ, le_of_lt hσ0]
  have hγ₁leσ : γ₁ ≤ σ := le_trans hγ₁σ hσpowσ
  -- `√γ` is minuscule
  have hsqrtγ : Real.sqrt γ ≤ 1 / 10 ^ 12 := by
    have h : Real.sqrt γ ≤ Real.sqrt ((1 / 10 ^ 12 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by
      nlinarith only [hγ24'])
    rwa [show Real.sqrt ((1 / 10 ^ 12 : ℝ) ^ 2) = 1 / 10 ^ 12 from by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]] at h
  -- `δr₀ ≥ 4`
  have hδr₀4 : 4 * (r₁ : ℝ) < δ * (r₀ : ℝ) := by
    have hz : (0 : ℝ) ≤ (r₀ : ℝ) - 1 := by
      have h2 : (2 : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hr₀2
      linarith
    have h0 : 4 * (r₁ : ℝ) < γ₁ * ((r₀ : ℝ) - 1) := by
      have h := mul_lt_mul_of_pos_left hr₀big (by norm_num : (0 : ℝ) < 4)
      have he : (4 : ℝ) * (γ₁ / 4 * ((r₀ : ℝ) - 1)) = γ₁ * ((r₀ : ℝ) - 1) := by ring
      linarith only [h, he]
    have h1 : γ₁ * ((r₀ : ℝ) - 1) ≤ σ * ((r₀ : ℝ) - 1) :=
      mul_le_mul_of_nonneg_right hγ₁leσ hz
    have h2 : σ * ((r₀ : ℝ) - 1) ≤ σ * (r₀ : ℝ) := by nlinarith only [hσ0]
    have h3 : σ * (r₀ : ℝ) ≤ δ * (r₀ : ℝ) :=
      mul_le_mul_of_nonneg_right hσδ (Nat.cast_nonneg _)
    linarith only [h0, h1, h2, h3]
  have hδr₀ : 4 ≤ δ * (r₀ : ℝ) := by
    have h : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr₁2
    linarith only [hδr₀4, h]
  have h8r₀ : 8 ≤ (1 / 10 ^ 5) * (1 / 10 ^ 4) * (r₀ : ℝ) := by
    have h1 : (4 : ℝ) / δ ≤ (r₀ : ℝ) := by
      rw [div_le_iff₀ hδ0]; linarith only [hδr₀]
    have h2 : (4 : ℝ) / δ ≥ 4 * 10 ^ 24 := by
      rw [ge_iff_le, le_div_iff₀ hδ0]
      nlinarith only [hδ24m]
    have h3 : (4 : ℝ) * 10 ^ 24 ≤ (r₀ : ℝ) := le_trans h2 h1
    have hc : (8 : ℝ) ≤ (1 / 10 ^ 5) * (1 / 10 ^ 4) * (4 * 10 ^ 24) := by norm_num
    nlinarith only [h3, hc]
  -- the constant side conditions of `exists_S12Margins`
  have hγ2ε : γ ≤ 2 * (1 / 10 ^ 4) := by linarith only [hγ24']
  have h8γ : 8 * γ ≤ 1 / 10 ^ 4 := by linarith only [hγ24']
  have hεsmall : 1000 * (1 / 10 ^ 4 : ℝ) ≤ 1 := by norm_num
  have hρlt : 2 * (1 / 10 ^ 5 : ℝ) ≤ (1 / 10 ^ 4) / 2 := by norm_num
  have hγρabs : 1000 * (3 * γ / 2) ≤ (1 / 10 ^ 5 : ℝ) * (1 / 10 ^ 4) := by
    nlinarith only [hγ24']
  have hL5in : 10 * Real.sqrt γ < 3 * (1 / 10 ^ 4 : ℝ) := by linarith only [hsqrtγ]
  have hβr1' : 16 ≤ (β / 2) * (r₁ : ℝ) := by linarith only [hβr1]
  have hr₀big' : 2 * (r₁ : ℝ) ≤ γ * ((r₀ : ℝ) - 1) := by
    have h1 : (4 : ℝ) * (r₁ : ℝ) ≤ γ₁ * ((r₀ : ℝ) - 1) := by linarith only [hr₀big]
    have h2 : γ₁ ≤ γ := by linarith only [hγ₁leσ, hσδ, hδγ]
    have h3 : γ₁ * ((r₀ : ℝ) - 1) ≤ γ * ((r₀ : ℝ) - 1) := by
      have hz : (0 : ℝ) ≤ (r₀ : ℝ) - 1 := by
        have h4 : (2 : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hr₀2
        linarith
      exact mul_le_mul_of_nonneg_right h2 hz
    linarith only [h1, h3]
  obtain ⟨ξ, hξ0, hξle, -, -, -, -, -, N, hN⟩ :=
    exists_S12Margins (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (ρ := 1 / 10 ^ 5)
      (ρ_abs := 1 / 10 ^ 5) (ε := 1 / 10 ^ 4) hβ0 hβ1 hγ0 hγ1 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) hr₁2 hr₀2 hr₁r₀ hβγ hβsq hβ4
      (by nlinarith only [hγ24']) (by norm_num) hγ2ε hεsmall (by norm_num) h8γ hρlt
      hγρabs (by norm_num) hβr1' hr₁β₀ hr₀big' hL5in
  -- the remaining side conditions
  have h15ρ : 15 * Real.sqrt γ + ξ ≤ (1 / 10 ^ 5) * (1 / 10 ^ 4) / 2 := by
    have hξle' : ξ ≤ 1 / 10 ^ 24 * (1 / 10 ^ 5) / 10 ^ 4 := by
      calc ξ ≤ γ * (1 / 10 ^ 5) / 10 ^ 4 := hξle
        _ ≤ (1 / 10 ^ 24) * (1 / 10 ^ 5) / 10 ^ 4 := by
            have hz : (0 : ℝ) < (1 / 10 ^ 5) / 10 ^ 4 := by norm_num
            have h := mul_le_mul_of_nonneg_right hγ24' (le_of_lt hz)
            linarith only [h]
    have hc : 15 * (1 / 10 ^ 12 : ℝ) + 1 / 10 ^ 24 * (1 / 10 ^ 5) / 10 ^ 4 ≤
        (1 / 10 ^ 5) * (1 / 10 ^ 4) / 2 := by norm_num
    linarith only [hsqrtγ, hξle', hc]
  have hCfin : 14 * δ + 15 * Real.sqrt γ ≤ 1 / 10 ^ 5 := by
    have hc : (14 : ℝ) * (1 / 10 ^ 24) + 15 * (1 / 10 ^ 12 : ℝ) ≤ 1 / 10 ^ 5 := by norm_num
    nlinarith only [hδ24', hsqrtγ, hc]
  have hδ2 : 2 * δ < 1 - 10 * (1 / 10 ^ 4 : ℝ) := by linarith only [hδ24']
  have hδε : δ ≤ 1 / 10 ^ 4 := by linarith only [hδ24']
  refine ⟨ξ, hξ0, N + 12500 + 36 + 10 ^ 10 + 30000 + 8, fun n hn => ?_⟩
  have hnN : N ≤ n := by omega
  have hn1 : 12500 ≤ n := by omega
  have hn2 : 36 ≤ n := by omega
  have hn3 : (10 ^ 10 : ℕ) ≤ n := by omega
  have hn4 : 30000 ≤ n := by omega
  have hn5 : 8 ≤ n := by omega
  have hn1R : (12500 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hnR : (36 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hnR2 : ((10 : ℝ) ^ 10) ≤ (n : ℝ) := by
    have h : ((10 : ℕ) ^ 10 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    simpa using h
  have hsqrtn : (6 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have h : Real.sqrt (36 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hnR
    rwa [show Real.sqrt (36 : ℝ) = 6 from by
      rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
  have hm := hN n hnN
  have hεn3 : 3 ≤ (1 / 10 ^ 4) * (n : ℝ) := by
    have h1 : (30000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
    have hc : (3 : ℝ) ≤ (1 / 10 ^ 4) * 30000 := by norm_num
    nlinarith only [h1, hc]
  have hnum3 : (Dparam n (1 / 10 ^ 5) : ℝ) + (D'param (Dparam n (1 / 10 ^ 5)) γ : ℝ) +
      (2 * γ * (n : ℝ) + 32 / β ^ 2) ≤ (n : ℝ) := by
    have hn8 : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn5
    have hD : (Dparam n (1 / 10 ^ 5) : ℝ) ≤ (1 - 1 / 10 ^ 5) * ((n : ℝ) - 1) := by
      rw [Dparam]
      exact Nat.floor_le (by nlinarith only [hn8, Nat.cast_nonneg (α := ℝ) n])
    have hDn : (Dparam n (1 / 10 ^ 5) : ℝ) ≤ (n : ℝ) := by
      nlinarith only [hD, hn8, Nat.cast_nonneg (α := ℝ) n]
    have hD' : (D'param (Dparam n (1 / 10 ^ 5)) γ : ℝ) ≤ 10 * Real.sqrt γ * (n : ℝ) := by
      have h1 : (D'param (Dparam n (1 / 10 ^ 5)) γ : ℝ) ≤
          10 * Real.sqrt γ * (Dparam n (1 / 10 ^ 5) : ℝ) := by
        rw [D'param]
        exact le_trans (Nat.floor_le (by positivity)) le_rfl
      have h2 : 10 * Real.sqrt γ * (Dparam n (1 / 10 ^ 5) : ℝ) ≤ 10 * Real.sqrt γ * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hDn (by positivity)
      linarith only [h1, h2]
    have hlin : 10 * Real.sqrt γ + 2 * γ + γ / 2 ≤ 1 / 10 ^ 5 := by
      have hc : 10 * (1 / 10 ^ 12 : ℝ) + 2 * (1 / 10 ^ 24) + 1 / 10 ^ 24 / 2 ≤ 1 / 10 ^ 5 := by
        norm_num
      nlinarith only [hsqrtγ, hγ24', hc]
    nlinarith only [hD, hD', hm.hk2, hlin, hn8, Nat.cast_nonneg (α := ℝ) n]
  refine ⟨hm, ?_, ?_, h15ρ, h8r₀, hδr₀, hCfin, hβδ2, hδ2, ?_, hδε, hδ1', hδ3', hεn3,
    hnum3⟩
  · -- `2ρ(n-1)+1 ≤ εn`
    nlinarith only [hn1R]
  · -- `3 ≤ (1-δ)√n`
    nlinarith only [hsqrtn, hδ1']
  · -- `4 ≤ ρεn`
    nlinarith only [hnR2]

/-! ## The numerical margins of the Leftover Lemma for the Type B constants -/

/-- **The `LeftoverMargins` bundle for the Type B constants.**  With
`ρ = ρ_abs = 10⁻⁵`, `ε = 10⁻⁴` and `γ ≤ 10⁻³⁰` (so that the buffer's parameter
`10√γ` is comfortably below `ρ_abs ε = 10⁻⁹`), together with the smallness of
`ξ` coming from `S12Margins`, the margin conditions of the Leftover Lemma hold
for all large `n`. -/
theorem exists_leftoverMargins_B (hK : KahnStatement) {r₁ : ℕ} {γ ξ : ℝ}
    (hγ0 : 0 < γ) (hγ30 : γ ≤ 1 / 10 ^ 30) (hξ0 : 0 < ξ)
    (hξγρ : 4000 * ξ ≤ (3 * γ / 2) * (1 / 10 ^ 5)) :
    ∃ N : ℕ, ∀ n ≥ N, LeftoverMargins n r₁ γ (1 / 10 ^ 5) (1 / 10 ^ 5) (1 / 10 ^ 4) ξ := by
  have hγ1 : γ ≤ 1 := by
    have h : (1 / 10 ^ 30 : ℝ) ≤ 1 := by norm_num
    linarith only [hγ30, h]
  have hγ100 : γ ≤ 1 / 100 := by
    have h : (1 / 10 ^ 30 : ℝ) ≤ 1 / 100 := by norm_num
    linarith only [hγ30, h]
  have hsqrt : Real.sqrt γ ≤ 1 / 10 ^ 13 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 13)]
    have hc : (1 / 10 ^ 30 : ℝ) ≤ 1 / 10 ^ 26 := by norm_num
    have h2 : (1 / 10 ^ 13 : ℝ) ^ 2 = 1 / 10 ^ 26 := by norm_num
    linarith only [hγ30, hc, h2]
  have h3 : 3 * γ / 2 ≤ Real.sqrt γ := by
    have hs : Real.sqrt γ * Real.sqrt γ = γ := by
      have h := Real.sq_sqrt (le_of_lt hγ0)
      nlinarith only [h]
    have h4 : (3 / 2 : ℝ) * Real.sqrt γ ≤ 1 := by linarith only [hsqrt]
    have h5 := mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg γ)
    nlinarith only [h5, hs]
  refine exists_leftoverMargins hK (r₁ := r₁) (ρ := 1 / 10 ^ 5) (ρ_abs := 1 / 10 ^ 5)
    (ε := 1 / 10 ^ 4) hγ0 hγ100 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hξ0 ?_ ?_
  · have h1 : (10 : ℝ) ^ 4 * (1 / 10 ^ 13) = (1 / 10 ^ 5) * (1 / 10 ^ 4) := by norm_num
    calc 10 ^ 4 * Real.sqrt γ ≤ 10 ^ 4 * (1 / 10 ^ 13) :=
          mul_le_mul_of_nonneg_left hsqrt (by norm_num)
      _ = (1 / 10 ^ 5) * (1 / 10 ^ 4) := h1
  · calc 4000 * ξ ≤ (3 * γ / 2) * (1 / 10 ^ 5) := hξγρ
      _ ≤ Real.sqrt γ * (1 / 10 ^ 5) := mul_le_mul_of_nonneg_right h3 (by norm_num)

end

end ErdosFaberLovaszConjecture

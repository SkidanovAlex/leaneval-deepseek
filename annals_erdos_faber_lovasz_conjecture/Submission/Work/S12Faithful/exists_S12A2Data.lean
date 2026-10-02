import Submission.Work.S12Faithful.Data

namespace Work.S12Faithful

open ErdosFaberLovaszConjecture

open Commons.Analysis.Real

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

/-- **The faithful Type-A₂ numeric data are satisfiable for all large `n`.**  Model:
`exists_S12ANum` in `Submission/EFL/S12ANum.lean` (same shape, with the powers of the master
constant `σ` replaced by free parameters; in particular `hsmall` is the analogue of the old
`√γ ≤ σ⁵/10¹²⁵`).  For parameters satisfying the listed smallness relations there is `ξ > 0`
and a threshold `N` with `S12A2Data n r₁ r₀ β γ ρ ξ ε ζ η ηr` for every `n ≥ N`.  The
`n`-level fields of `S12A2Data` are eventual conditions on the fixed constants and are
obtained from `Filter.eventually_atTop` arguments (as in `exists_S12ANum`); `hm` and `hleft`
come from `S12Margins_of` (`Submission/EFL/S12Params.lean`, whose `n`-level hypotheses are
likewise eventual) and `exists_leftoverMargins` (`Submission/EFL/LeftoverMargins.lean`).
Please use narrow Mathlib imports only (never `import Mathlib`): this module is on the import
path of the cone. -/
theorem exists_S12A2Data (hK : KahnStatement) {r₁ r₀ : ℕ} {β γ ρ ε ζ η ηr : ℝ}
    (hβ0 : 0 < β) (hγ0 : 0 < γ) (hρ0 : 0 < ρ) (hε0 : 0 < ε) (hζ0 : 0 < ζ)
    (hη0 : 0 < η) (hηr0 : 0 < ηr)
    (hr₁2 : 2 ≤ r₁) (hr₀2 : 2 ≤ r₀) (hr₁r₀ : r₁ < r₀)
    (hρ4 : ρ ≤ 1 / 4) (hρ100 : ρ ≤ 1 / 100) (hγ1 : γ ≤ 1) (hβγ : β ≤ γ)
    (hβsq : 8 * β ≤ γ ^ 2) (hβ4 : β ≤ γ ^ 4 / 10 ^ 12)
    (hγρs : 10 ^ 6 * (2 * γ) ≤ ρ / 2)
    (hγ2ε : γ ≤ 2 * ε) (hε1000 : 1000 * ε ≤ 1) (hε4000 : 4000 * ε ≤ 1)
    (h8γε : 8 * γ ≤ ε) (hγρabs : 1000 * (3 * γ / 2) ≤ (ρ / 2) * ε)
    (hβr1 : 32 ≤ β * (r₁ : ℝ)) (hr₁β₀ : (r₁ : ℝ) ≤ β * ((r₀ : ℝ) - 1))
    (hr₀big : (r₁ : ℝ) < γ / 4 * ((r₀ : ℝ) - 1))
    (hL5in : 10 * Real.sqrt γ < 3 * ε)
    (hsmall : 10 ^ 4 * Real.sqrt γ ≤ (ρ / 2) * ε)
    (hη22 : 22 * ε ≤ η)
    (h15γρε : 60 * Real.sqrt γ ≤ ρ * ε)
    (h15γε : 15 * Real.sqrt γ ≤ ε)
    (h20ερ : 20 * ε ≤ ρ / 4)
    (h30 : 30 * Real.sqrt γ ≤ ρ)
    (h8r₀ : 8 ≤ ρ * ε * (r₀ : ℝ))
    (h20ε : 20 * ε ≤ ρ ^ 2)
    (h15ερ : 15 * ε ≤ ρ)
    (hηrbig : 4 * Real.sqrt (15 * Real.sqrt γ) ≤ ηr)
    (hsqrtε : Real.sqrt ε ≤ ηr)
    (hnumα0 : ρ / 2 * (1 - 2 * Real.sqrt ε) ≥
      2 * Real.sqrt (15 * Real.sqrt γ) + (ρ / 3 - ηr))
    (hnum1 : ρ / 4 - ζ ≤ ρ / 3 * (1 - 1 / 10 ^ 4) ^ 2 - ηr / (1 - 1 / 10 ^ 4))
    (hnum2 : ηr / (1 - 1 / 10 ^ 4) ≤ ζ)
    (hcardc : (1 : ℝ) ≤ (1 + (1 / 10 ^ 4) * ηr) * (1 - 10 * ε)) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ N : ℕ, ∀ n ≥ N, S12A2Data n r₁ r₀ β γ ρ ξ ε ζ η ηr := by
  classical
  have hsγ0 : (0 : ℝ) < Real.sqrt γ := Real.sqrt_pos.2 hγ0
  have hβ1 : β ≤ 1 := le_trans hβγ hγ1
  have hε1 : ε ≤ 1 := by linarith only [hε1000]
  have hγs : γ ≤ Real.sqrt γ := by
    have h1 : Real.sqrt γ ≤ 1 := Real.sqrt_le_one.mpr hγ1
    have h2 : Real.sqrt γ * Real.sqrt γ = γ := Real.mul_self_sqrt (le_of_lt hγ0)
    nlinarith only [h1, h2, Real.sqrt_nonneg γ]
  have hγ100 : γ ≤ 1 / 100 := by
    have hρ' : ρ / 2 ≤ 1 / 200 := by linarith only [hρ100]
    have hε' : ε ≤ 1 / 1000 := by linarith only [hε1000]
    have h2 : (ρ / 2) * ε ≤ (1 / 200) * (1 / 1000) :=
      mul_le_mul hρ' hε' (le_of_lt hε0) (by norm_num)
    have h3 : 10 ^ 4 * Real.sqrt γ ≤ 1 / 200000 := by linarith only [hsmall, h2]
    have h4 : Real.sqrt γ ≤ 1 / (2 * 10 ^ 9) := by nlinarith only [h3]
    have h5 : γ ≤ (1 / (2 * 10 ^ 9)) ^ 2 := by
      have hs := Real.mul_self_sqrt (le_of_lt hγ0)
      nlinarith only [hs, h4, Real.sqrt_nonneg γ]
    nlinarith only [h5]
  have hβr1' : 16 ≤ (β / 2) * (r₁ : ℝ) := by linarith only [hβr1]
  have hr₀big' : 2 * (r₁ : ℝ) ≤ γ * ((r₀ : ℝ) - 1) := by
    have h2 : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr₁2
    nlinarith only [hr₀big, h2, hγ0]
  -- ## the parameter `ξ`
  set ξ : ℝ := min (min (min (γ * (ρ / 2)) β) (min γ (ρ * ε)))
    (min (2 * γ * (ρ / 2) * ε / 10 ^ 12) ((2 * γ) ^ 2 / 10 ^ 8)) / 10 ^ 4 with hξdef
  have hξleA : ξ ≤ (min (min (γ * (ρ / 2)) β) (min γ (ρ * ε))) / 10 ^ 4 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hξmin1 : ξ ≤ (γ * (ρ / 2)) / 10 ^ 4 :=
    le_trans hξleA (div_le_div_of_nonneg_right
      (le_trans (min_le_left _ _) (min_le_left _ _)) (by norm_num))
  have hξmin2 : ξ ≤ β / 10 ^ 4 :=
    le_trans hξleA (div_le_div_of_nonneg_right
      (le_trans (min_le_left _ _) (min_le_right _ _)) (by norm_num))
  have hξmin3 : ξ ≤ γ / 10 ^ 4 :=
    le_trans hξleA (div_le_div_of_nonneg_right
      (le_trans (min_le_right _ _) (min_le_left _ _)) (by norm_num))
  have hξmin4 : ξ ≤ (ρ * ε) / 10 ^ 4 :=
    le_trans hξleA (div_le_div_of_nonneg_right
      (le_trans (min_le_right _ _) (min_le_right _ _)) (by norm_num))
  have hξmin5 : ξ ≤ (2 * γ * (ρ / 2) * ε / 10 ^ 12) / 10 ^ 4 :=
    le_trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
      (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hξmin6 : ξ ≤ ((2 * γ) ^ 2 / 10 ^ 8) / 10 ^ 4 :=
    le_trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
      (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  have hξ0 : 0 < ξ := by
    have h1 : 0 < min (min (γ * (ρ / 2)) β) (min γ (ρ * ε)) :=
      lt_min (lt_min (mul_pos hγ0 (by linarith only [hρ0])) hβ0)
        (lt_min hγ0 (mul_pos hρ0 hε0))
    have h2 : 0 < min (2 * γ * (ρ / 2) * ε / 10 ^ 12) ((2 * γ) ^ 2 / 10 ^ 8) :=
      lt_min (by positivity) (by positivity)
    rw [hξdef]
    exact div_pos (lt_min h1 h2) (by norm_num)
  have hξβ : 8 * ξ ≤ β / 2 := by linarith only [hξmin2, hβ0]
  have hξγ : 10 * ξ ≤ γ / 2 := by linarith only [hξmin3, hγ0]
  have hξγρ : 4000 * ξ ≤ (3 * γ / 2) * (ρ / 2) := by
    nlinarith only [hξmin1, hγ0, hρ0]
  have hξε1 : 10 ^ 12 * ξ ≤ 2 * γ * (ρ / 2) * ε := by
    have h1 : 10 ^ 12 * ξ ≤ 10 ^ 12 * ((2 * γ * (ρ / 2) * ε / 10 ^ 12) / 10 ^ 4) :=
      mul_le_mul_of_nonneg_left hξmin5 (by norm_num)
    have h2 : 10 ^ 12 * ((2 * γ * (ρ / 2) * ε / 10 ^ 12) / 10 ^ 4) =
        2 * γ * (ρ / 2) * ε / 10 ^ 4 := by ring
    have h3 : (0 : ℝ) ≤ 2 * γ * (ρ / 2) * ε := by positivity
    linarith only [h1, h2.le, h2.ge, h3]
  have hξε2 : ξ ≤ (2 * γ) ^ 2 / 10 ^ 8 := by
    have h3 : (0 : ℝ) ≤ (2 * γ) ^ 2 / 10 ^ 8 := by positivity
    linarith only [hξmin6, h3]
  have hξsmallLeft : 4000 * ξ ≤ Real.sqrt γ * (ρ / 2) := by
    have h2 : (0 : ℝ) ≤ ρ / 2 := by linarith only [hρ0]
    have hs : Real.sqrt γ ≤ 1 := Real.sqrt_le_one.mpr hγ1
    have hs0 : (0 : ℝ) ≤ Real.sqrt γ := Real.sqrt_nonneg γ
    have hsq : Real.sqrt γ * Real.sqrt γ = γ := Real.mul_self_sqrt (le_of_lt hγ0)
    have h4 : (2 / 5) * γ ≤ Real.sqrt γ := by nlinarith only [hsq, hs, hs0]
    calc 4000 * ξ ≤ 4000 * (γ * (ρ / 2) / 10 ^ 4) :=
          mul_le_mul_of_nonneg_left hξmin1 (by norm_num)
      _ = 2 / 5 * γ * (ρ / 2) := by ring
      _ ≤ Real.sqrt γ * (ρ / 2) := mul_le_mul_of_nonneg_right h4 h2
  have hξs15 : ξ ≤ Real.sqrt (15 * Real.sqrt γ) := by
    have hs : Real.sqrt γ * Real.sqrt γ = γ := Real.mul_self_sqrt (le_of_lt hγ0)
    have hs1 : Real.sqrt γ ≤ 1 := Real.sqrt_le_one.mpr hγ1
    have hs0 : (0 : ℝ) ≤ Real.sqrt γ := Real.sqrt_nonneg γ
    have h3 : (Real.sqrt γ) ^ 3 ≤ 15 * 10 ^ 8 :=
      le_trans (pow_le_one₀ hs0 hs1 (n := 3)) (by norm_num)
    have h4 : (Real.sqrt γ) ^ 4 ≤ 15 * 10 ^ 8 * Real.sqrt γ := by
      have h7 : (Real.sqrt γ) ^ 4 = (Real.sqrt γ) ^ 3 * Real.sqrt γ := by ring
      rw [h7]
      exact mul_le_mul_of_nonneg_right h3 hs0
    have hgoal : (γ / 10 ^ 4) ^ 2 ≤ 15 * Real.sqrt γ := by
      nlinarith only [h4, hs]
    calc ξ ≤ γ / 10 ^ 4 := hξmin3
      _ = Real.sqrt ((γ / 10 ^ 4) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (15 * Real.sqrt γ) := Real.sqrt_le_sqrt hgoal
  have hξεrob : ξ + Real.sqrt (15 * Real.sqrt γ) ≤ ηr / 2 := by
    linarith only [hξs15, hηrbig]
  have hnumα : ρ / 2 * (1 - 2 * Real.sqrt ε) ≥
      (ξ + Real.sqrt (15 * Real.sqrt γ)) + (ρ / 3 - ηr) := by
    linarith only [hnumα0, hξs15]
  have h15ρ : 15 * Real.sqrt γ + ξ ≤ ρ * ε / 2 := by
    have h1 : Real.sqrt γ ≤ ρ * ε / (2 * 10 ^ 4) := by linarith only [hsmall]
    have h3 : ξ ≤ ρ * ε / 10 ^ 4 := by linarith only [hξmin4]
    nlinarith only [h1, h3, hγ0, hρ0, hε0, Real.sqrt_nonneg γ]
  have hξquarter : ξ ≤ ρ / 4 := by nlinarith only [hξmin4, hρ0, hε0, hε1]
  have h20εξ : 20 * ε + ξ ≤ ρ / 2 := by linarith only [h20ερ, hξquarter, hρ0]
  have hξε : ξ ≤ ρ / 2 := by linarith only [hξquarter, hρ0]
  have hξε19 : ξ ≤ 19 * ε := by nlinarith only [hξmin3, hγ0, hε0, h8γε]
  have hδnum : ξ + 20 * ε + 15 * Real.sqrt γ ≤ 22 * ε := by
    have h1 : ξ ≤ ε := by nlinarith only [hξmin3, hγ0, hε0, h8γε]
    linarith only [h1, h15γε]
  -- ## the leftover margins
  obtain ⟨Nleft, hNleft⟩ := exists_leftoverMargins hK (r₁ := r₁) (γ := γ) (ρ := ρ)
    (ρ_abs := ρ / 2) (ε := ε) (ξ := ξ) hγ0 hγ100 hρ0 hρ4 (by linarith only [hρ0])
    (by linarith only [hρ4]) hε0 hε1000 hξ0 hsmall hξsmallLeft
  have hleft_ev : ∀ᶠ n : ℕ in Filter.atTop, LeftoverMargins n r₁ γ ρ (ρ / 2) ε ξ :=
    Filter.eventually_atTop.mpr ⟨Nleft, hNleft⟩
  -- ## the `n`-large conditions
  have h100εn : ∀ᶠ n : ℕ in Filter.atTop, (100 : ℝ) ≤ ε * (n : ℝ) :=
    eventually_const_le_mul_nat (c := ε) (a := 100) hε0
  have h8βn : ∀ᶠ n : ℕ in Filter.atTop, (8 : ℝ) ≤ β * (n : ℝ) :=
    eventually_const_le_mul_nat (c := β) (a := 8) hβ0
  have h24βn : ∀ᶠ n : ℕ in Filter.atTop, (24 : ℝ) ≤ (β / 2) * (n : ℝ) :=
    eventually_const_le_mul_nat (c := β / 2) (a := 24) (by positivity)
  have hn8 : ∀ᶠ n : ℕ in Filter.atTop, (8 : ℝ) ≤ (n : ℝ) := by
    simpa using eventually_const_le_mul_nat (c := (1 : ℝ)) (a := 8) (by norm_num)
  have hk2 : ∀ᶠ n : ℕ in Filter.atTop, 32 / β ^ 2 ≤ γ * (n : ℝ) / 2 := by
    have h := eventually_const_le_mul_nat (c := γ / 2) (a := 32 / β ^ 2) (by positivity)
    refine h.mono ?_
    intro n hn
    have he : γ / 2 * (n : ℝ) = γ * (n : ℝ) / 2 := by ring
    linarith only [hn, he.le, he.ge]
  have hr₁βn : ∀ᶠ n : ℕ in Filter.atTop, (r₁ : ℝ) < β * (n : ℝ) / 4 := by
    have h := eventually_const_le_mul_nat (c := β / 4) (a := (r₁ : ℝ) + 1) (by positivity)
    refine h.mono ?_
    intro n hn
    have he : β / 4 * (n : ℝ) = β * (n : ℝ) / 4 := by ring
    linarith only [hn, he.le, he.ge]
  have hnbig : ∀ᶠ n : ℕ in Filter.atTop, (2000 : ℝ) ≤ (3 * γ / 2) * (ρ / 2) * (n : ℝ) := by
    have h := eventually_const_le_mul_nat (c := (3 * γ / 2) * (ρ / 2)) (a := 2000)
      (by positivity)
    refine h.mono ?_
    intro n hn
    have he : (3 * γ / 2) * (ρ / 2) * (n : ℝ) = ((3 * γ / 2) * (ρ / 2)) * (n : ℝ) := by
      ring
    linarith only [hn, he.le, he.ge]
  have hβhalf : ∀ᶠ n : ℕ in Filter.atTop,
      (β / 2) * (n : ℝ) / 2 ≤ (1 - ρ) * ((n : ℝ) - 1) := by
    have hc : (0 : ℝ) < 1 - ρ - β / 4 := by nlinarith only [hρ4, hβγ, hγ1]
    have h := eventually_const_le_mul_nat (c := 1 - ρ - β / 4) (a := 1 - ρ) hc
    refine h.mono ?_
    intro n hn
    nlinarith only [hn]
  have hDbig : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ 10 * Real.sqrt γ * (Dparam n ρ : ℝ) := by
    have hc : (0 : ℝ) < 1 - ρ := by linarith only [hρ4]
    have hs10 : (0 : ℝ) < 10 * Real.sqrt γ := by linarith only [hsγ0]
    have hA : ∀ᶠ n : ℕ in Filter.atTop,
        (2 / (10 * Real.sqrt γ) + 1 + (1 - ρ)) ≤ (1 - ρ) * (n : ℝ) :=
      eventually_const_le_mul_nat (c := 1 - ρ) hc
    refine hA.mono ?_
    intro n hn
    have hle : 2 / (10 * Real.sqrt γ) + 1 ≤ (1 - ρ) * ((n : ℝ) - 1) := by
      have he : (1 - ρ) * ((n : ℝ) - 1) = (1 - ρ) * (n : ℝ) - (1 - ρ) := by ring
      linarith only [hn, he.le, he.ge]
    have hlt : 2 / (10 * Real.sqrt γ) < (Nat.floor ((1 - ρ) * ((n : ℝ) - 1)) : ℝ) := by
      have hf := Nat.sub_one_lt_floor ((1 - ρ) * ((n : ℝ) - 1))
      linarith only [hle, hf]
    refine le_of_lt ?_
    calc (2 : ℝ) = 10 * Real.sqrt γ * (2 / (10 * Real.sqrt γ)) := by field_simp
      _ < 10 * Real.sqrt γ * (Dparam n ρ : ℝ) := mul_lt_mul_of_pos_left hlt hs10
  have h25ρn : ∀ᶠ n : ℕ in Filter.atTop, (25 : ℝ) ≤ ρ * (n : ℝ) :=
    eventually_const_le_mul_nat (c := ρ) (a := 25) hρ0
  have h2ξn : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ ξ * (n : ℝ) :=
    eventually_const_le_mul_nat (c := ξ) (a := 2) hξ0
  have h1ξn : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) ≤ ξ * (n : ℝ) :=
    eventually_const_le_mul_nat (c := ξ) (a := 1) hξ0
  have h4ρn : ∀ᶠ n : ℕ in Filter.atTop, (4 : ℝ) ≤ ρ * ε * (n : ℝ) := by
    have h := eventually_const_le_mul_nat (c := ρ * ε) (a := 4) (by positivity)
    exact h.mono fun n hn => by linarith only [hn]
  have hξsharp : ∀ᶠ n : ℕ in Filter.atTop, 10 * ξ + 1 / (n : ℝ) ≤ γ / 2 := by
    have hc : (0 : ℝ) < γ / 2 - 10 * ξ := by linarith only [hξmin3, hγ0]
    have h := eventually_const_le_mul_nat (c := γ / 2 - 10 * ξ) (a := 1) hc
    refine h.mono ?_
    intro n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by
      have : (0 : ℕ) < n := by
        by_contra hcon
        have hz : n = 0 := by omega
        subst hz
        norm_num at hn
      exact_mod_cast this
    have h2 : 1 / (n : ℝ) ≤ γ / 2 - 10 * ξ := by
      rw [div_le_iff₀ hn0]
      linarith only [hn]
    linarith only [h2]
  have hn100 : ∀ᶠ n : ℕ in Filter.atTop, 10 ^ 100 ≤ 2 * γ * (ρ / 2) * ε * (n : ℝ) := by
    have h := eventually_const_le_mul_nat (c := 2 * γ * (ρ / 2) * ε) (a := 10 ^ 100)
      (by positivity)
    exact h.mono fun n hn => by linarith only [hn]
  have hnsup : ∀ᶠ n : ℕ in Filter.atTop,
      10 ^ 400 * (((ρ / 2)⁻¹) ^ 6 + ((2 * γ)⁻¹) ^ 16 + (2 * γ * (ρ / 2) * ε)⁻¹
        + ((2 * γ * (ρ / 2) * ε)⁻¹) ^ 2 + (r₁ : ℝ)) ≤ (n : ℝ) := by
    have h := eventually_const_le_mul_nat (c := (1 : ℝ)) (a := 10 ^ 400 * (((ρ / 2)⁻¹) ^ 6
      + ((2 * γ)⁻¹) ^ 16 + (2 * γ * (ρ / 2) * ε)⁻¹
      + ((2 * γ * (ρ / 2) * ε)⁻¹) ^ 2 + (r₁ : ℝ))) (by norm_num)
    simpa using h
  have hnum3 : ∀ᶠ n : ℕ in Filter.atTop,
      (Dparam n ρ : ℝ) + (D'param (Dparam n ρ) γ : ℝ) +
        (2 * γ * (n : ℝ) + 32 / β ^ 2) ≤ (n : ℝ) := by
    refine (hk2.and hn8).mono ?_
    rintro n ⟨hk, h8n⟩
    have hD : (Dparam n ρ : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) := by
      rw [Dparam]
      exact Nat.floor_le (by nlinarith only [hρ4, h8n, Nat.cast_nonneg (α := ℝ) n])
    have hDn : (Dparam n ρ : ℝ) ≤ (n : ℝ) := by
      nlinarith only [hD, hρ4, hρ0, h8n, Nat.cast_nonneg (α := ℝ) n]
    have hD' : (D'param (Dparam n ρ) γ : ℝ) ≤ 10 * Real.sqrt γ * (n : ℝ) := by
      have h1 : (D'param (Dparam n ρ) γ : ℝ) ≤ 10 * Real.sqrt γ * (Dparam n ρ : ℝ) := by
        rw [D'param]
        exact le_trans (Nat.floor_le (by positivity)) le_rfl
      have h2 : 10 * Real.sqrt γ * (Dparam n ρ : ℝ) ≤ 10 * Real.sqrt γ * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hDn (by positivity)
      linarith only [h1, h2]
    have hlin : 10 * Real.sqrt γ + 2 * γ + γ / 2 ≤ ρ := by
      have h1 : 10 * Real.sqrt γ ≤ ρ / 3 := by linarith only [h30]
      have h4 : γ ≤ ρ / 120 := by linarith only [h8γε, h15ερ]
      linarith only [h1, h4, hρ0]
    nlinarith only [hD, hD', hk, hlin, hρ4, hρ0, h8n, Nat.cast_nonneg (α := ℝ) n]
  -- ## assembly
  have hall : ∀ᶠ n : ℕ in Filter.atTop, S12A2Data n r₁ r₀ β γ ρ ξ ε ζ η ηr := by
    filter_upwards [h100εn, h8βn, h24βn, hn8, hk2, hr₁βn, hnbig, hβhalf, hDbig, h25ρn,
      h2ξn, h1ξn, h4ρn, hξsharp, hn100, hnsup, hnum3, hleft_ev]
      with n hεn100 hβn8 hβn24 hn8' hk2' hr₁βn' hnbig' hβhalf' hDbig' hρn25' hξn2' hξn1'
        h4ρεn' hξsharp' hn100' hnsup' hnum3' hleft'
    exact
      { hm := S12Margins_of (n := n) (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (ρ := ρ)
          (ρ_abs := ρ / 2) (ε := ε) (ξ := ξ)
          hβ0 hγ0 hρ0 (by linarith only [hρ0]) hε0 hr₁2 hr₀2 hr₁r₀ hρ4 hγ1 hβγ hβsq hβ4
          hγρs (by linarith only [hρ0]) hγ2ε hε1000 hε4000 h8γε hγρabs
          (by linarith only [hρ4]) hβr1' hr₁β₀ hr₀big' hL5in
          (by linarith only [hεn100]) hβn8 hk2' hr₁βn' hnbig' hβn24 hDbig'
          hεn100 (by exact_mod_cast hn8') (by linarith only [hβn8]) hβhalf'
          hξ0 hξβ hξγ hξγρ hξn1' hξε1 hξε2 hn100' hnsup'
        hleft := hleft'
        hρ0 := hρ0
        hρ1 := by linarith only [hρ4]
        hρ100 := hρ100
        hβ0 := hβ0
        hβ1 := hβ1
        hβγ := hβγ
        hγ0 := hγ0
        hγ1 := hγ1
        hγs := hγs
        hξ0 := hξ0
        hε0 := hε0
        hζ0 := hζ0
        hη0 := hη0
        hηr0 := hηr0
        hη22 := hη22
        h15ρ := h15ρ
        h30 := h30
        h8r₀ := h8r₀
        h20ε := h20ε
        h20εξ := h20εξ
        hξε := hξε
        h15ε := h15ερ
        hξε19 := hξε19
        hδnum := hδnum
        hξεrob := hξεrob
        hsqrtε := hsqrtε
        hnumα := hnumα
        hnum1 := hnum1
        hnum2 := hnum2
        hcardc := hcardc
        hξsharp := hξsharp'
        hεn3 := by linarith only [hεn100]
        hρn25 := hρn25'
        hξn := hξn2'
        h4ρεn := h4ρεn'
        hnum3 := hnum3' }
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hall
  exact ⟨ξ, hξ0, N, fun n hn => hN n hn⟩

end

end Work.S12Faithful

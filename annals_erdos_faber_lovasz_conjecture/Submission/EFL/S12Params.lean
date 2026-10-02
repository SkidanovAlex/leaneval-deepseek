import Submission.EFL.S12Final
import Submission.Work.Nib.strong_of_margins
import Submission.EFL.Comm.S12NumericArith
import Submission.Commons.Analysis.Real.rpow_two_thirds_le_half

/-!
# §12: the numeric parameter hierarchy (`S12Margins`)

Given a valid constant hierarchy `β ≤ γ ≪ ρ ≤ ε ≪ 1` (with the smallness
needed by the individual steps) together with the `n`-large conditions that the
hierarchy implies for all sufficiently large `n`, this module produces `ξ`, `κ`
and proves `S12Margins n r₁ r₀ β γ ρ ρ_abs ξ ε κ`.

The `n`-large conditions (`2 ≤ εn`, `8 ≤ βn`, `6 ≤ βn`, `32/β² ≤ γn/2`,
`r₁ < βn/4`, `24 ≤ (β/2)n`, `100 ≤ εn`, `8 ≤ n` and
`2 ≤ 10γ^{1/2}D`) are taken as hypotheses here; producing a threshold `N` such
that they hold for all `n ≥ N` is pure arithmetic (given the constants, `N` can
be taken to be any explicit sum of reciprocals of the parameters).
-/

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical
open Commons.Analysis.Real

noncomputable section

variable {n : ℕ}

/-- **The numeric hierarchy of §12 (for a fixed `n`).** -/
theorem S12Margins_of {r₁ r₀ : ℕ} {β γ ρ ρ_abs ε : ℝ}
    (hβ0 : 0 < β) (hγ0 : 0 < γ) (hρ0 : 0 < ρ) (hρabs0 : 0 < ρ_abs) (hε0 : 0 < ε)
    (hr₁2 : 2 ≤ r₁) (hr₀2 : 2 ≤ r₀) (hr₁r₀ : r₁ < r₀)
    (hρ4 : ρ ≤ 1 / 4) (hγ1 : γ ≤ 1) (hβγ : β ≤ γ) (hβsq : 8 * β ≤ γ ^ 2)
    (hβ4 : β ≤ γ ^ 4 / 10 ^ 12) (hγρs : 10 ^ 6 * (2 * γ) ≤ ρ_abs) (hρabs_le : ρ_abs ≤ ρ)
    (hγ2ε : γ ≤ 2 * ε)
    (hεsmall : 1000 * ε ≤ 1) (hε4000 : 4000 * ε ≤ 1) (h8γε : 8 * γ ≤ ε)
    (hγρabs : 1000 * (3 * γ / 2) ≤ ρ_abs * ε) (hρabs1 : ρ_abs ≤ 1)
    (hβr1 : 16 ≤ (β / 2) * (r₁ : ℝ)) (hr₁β₀ : (r₁ : ℝ) ≤ β * ((r₀ : ℝ) - 1))
    (hr₀big : 2 * (r₁ : ℝ) ≤ γ * ((r₀ : ℝ) - 1))
    (hL5in : 10 * Real.sqrt γ < 3 * ε)
    (hεn : 2 ≤ ε * (n : ℝ)) (hβn : 8 ≤ β * (n : ℝ)) (hk2 : 32 / β ^ 2 ≤ γ * (n : ℝ) / 2)
    (hr₁βn : (r₁ : ℝ) < β * (n : ℝ) / 4) (hnbig : 2000 ≤ (3 * γ / 2) * ρ_abs * (n : ℝ))
    (hβn24 : 24 ≤ (β / 2) * (n : ℝ)) (hDbig : 2 ≤ 10 * Real.sqrt γ * (Dparam n ρ : ℝ))
    (hεn100 : 100 ≤ ε * (n : ℝ)) (hn8 : 8 ≤ n) (hβn6 : 6 ≤ β * (n : ℝ))
    (hβhalf : (β / 2) * (n : ℝ) / 2 ≤ (1 - ρ) * ((n : ℝ) - 1))
    {ξ : ℝ} (hξ0 : 0 < ξ) (hξβ : 8 * ξ ≤ β / 2) (hξγ : 10 * ξ ≤ γ / 2)
    (hξγρ : 4000 * ξ ≤ (3 * γ / 2) * ρ_abs) (hnξ : 1 ≤ ξ * (n : ℝ))
    (hξε1 : 10 ^ 12 * ξ ≤ 2 * γ * ρ_abs * ε) (hξε2 : ξ ≤ (2 * γ) ^ 2 / 10 ^ 8)
    (hn100 : 10 ^ 100 ≤ 2 * γ * ρ_abs * ε * (n : ℝ))
    (hnsup : 10 ^ 400 * ((ρ_abs⁻¹) ^ 6 + ((2 * γ)⁻¹) ^ 16 + (2 * γ * ρ_abs * ε)⁻¹
      + ((2 * γ * ρ_abs * ε)⁻¹) ^ 2 + (r₁ : ℝ)) ≤ (n : ℝ)) :
    S12Margins n r₁ r₀ β γ ρ ρ_abs ξ ε (1 / 2) := by
  classical
  have hγ'0 : 0 < 3 * γ / 2 := by linarith
  have hγρabs0 : (0 : ℝ) < (3 * γ / 2) * ρ_abs := mul_pos hγ'0 hρabs0
  have hsqrt0 : (0 : ℝ) < Real.sqrt γ := Real.sqrt_pos.mpr hγ0
  have hβγ' : β ^ 2 * γ ≠ 0 := by positivity
  have hn1 : 1 ≤ n := by omega
  have hnpos : 0 < n := by omega
  have hn4 : 4 ≤ n := by omega
  have hnD : (n : ℝ) ≤ 2 * (Dparam n ρ : ℝ) := n_le_two_Dparam (by linarith only [hρ4]) hn8
  have hnDge : (n : ℝ) / 2 ≤ (Dparam n ρ : ℝ) := by
    have h := le_floor_mul_sub_one (le_of_lt hρ0) (by linarith only [hρ4]) hn8
    rw [Dparam]
    linarith only [h]
  have hnum1 : 2 / 3 * β * (n : ℝ) + 2 ≤ 2 * β * (Dparam n ρ : ℝ) :=
    two_thirds_beta_le (le_of_lt hβ0) hβn6 hnD
  have hEP2num : (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) ≤ 2 * β * (Dparam n ρ : ℝ) :=
    EP2num_le hr₀2 (le_of_lt hβ0) (by linarith) hnD
  have hL4ov : (r₁ : ℝ) * (n : ℝ) / ((r₀ : ℝ) - 1) ≤ γ * ((Dparam n ρ : ℕ) : ℝ) :=
    overlap_le_gamma_mul hr₀2 (by linarith) hnD
  have hL1 : (10 * Real.sqrt γ) * ((Dparam n ρ : ℕ) : ℝ) / 2 ≤
      (D'param (Dparam n ρ) γ : ℕ) := D'param_ge_half _ _ hDbig
  have h3γ : 3 * γ ≤ ε := by linarith only [h8γε, hγ0]
  have hS₂num : (Dparam n ρ : ℝ) + 3 * γ * (n : ℝ) / 2 + 5 + 4 * ε * (n : ℝ) ≤
      (1 - ρ) * (n : ℝ) + 5 * ε * (n : ℝ) := by
    have h := floor_mul_sub_one_add_le hε0 (le_of_lt hγ0) h3γ (le_of_lt hρ0)
      (by linarith only [hρ4]) hεn100
    rw [Dparam]
    linarith only [h]
  have hβγ5 : β ≤ 5 * Real.sqrt γ := by
    have h1 : Real.sqrt γ ≤ 1 := Real.sqrt_le_one.mpr hγ1
    have h2 : γ ≤ 5 * Real.sqrt γ := by
      nlinarith only [h1, Real.sq_sqrt (le_of_lt hγ0), Real.sqrt_nonneg γ]
    linarith only [h2, hβγ]
  have hL3 : 4 * γ ≤ 100 * Real.sqrt γ := four_gamma_le_sqrt (le_of_lt hγ0) (by linarith only [hγ1])
  have hξγ2 : 10 * ξ + 3 * γ / 2 ≤ 2 * γ := by linarith only [hξγ, hγ0]
  -- ## the asymptotic side conditions of the Nibble Lemma
  have hr₁n : 4 * (r₁ : ℝ) ≤ (n : ℝ) := by
    have h4 : 4 * (r₁ : ℝ) < β * (n : ℝ) := by linarith only [hr₁βn]
    have hβnle : β * (n : ℝ) ≤ (n : ℝ) := by
      nlinarith only [hβγ, hγ1, Nat.cast_nonneg (α := ℝ) n]
    linarith only [h4, hβnle]
  have hγr₁ : 4 ≤ (2 * γ) * (r₁ : ℝ) := by
    have h1 : (32 : ℝ) ≤ β * (r₁ : ℝ) := by linarith only [hβr1]
    have h2 : β * (r₁ : ℝ) ≤ γ * (r₁ : ℝ) :=
      mul_le_mul_of_nonneg_right hβγ (Nat.cast_nonneg (α := ℝ) r₁)
    linarith only [h1, h2]
  have hDhigh : (Dparam n ρ : ℝ) ≤ (n : ℝ) := by
    rw [Dparam]
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have h2 : (0 : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) := by nlinarith only [hρ4, hn1']
    have h3 : (⌊(1 - ρ) * ((n : ℝ) - 1)⌋₊ : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) :=
      Nat.floor_le h2
    nlinarith only [h3, hρ0, hρ4, hn1']
  have hDlow : Real.rpow (n : ℝ) (2 / 3) ≤ (Dparam n ρ : ℝ) :=
    le_trans (Commons.Analysis.Real.rpow_two_thirds_le_half n hn8) hnDge
  have hβn2 : (1 : ℝ) ≤ (2 * β) * (n : ℝ) := by nlinarith only [hβn]
  have hξγ2' : 4 * ξ ≤ 2 * γ := by linarith only [hξγ, hγ0]
  have hβγ2 : 16 * (2 * β) ≤ (2 * γ) ^ 2 := by nlinarith only [hβsq]
  have hγε2 : 4 * (2 * γ) ≤ ε := by linarith only [h8γε]
  have hγρabs' : 4 * (2 * γ) ≤ ρ_abs := by
    have hε1 : ε ≤ 1 := by linarith only [hεsmall]
    have h2 : ρ_abs * ε ≤ ρ_abs * 1 := by nlinarith only [hε1, hρabs0]
    linarith only [hγρabs, h2, hγ0]
  have hnib : NibbleMargins n ((Dparam n ρ : ℕ) : ℝ) r₁ (2 * β) (2 * γ) ε ρ_abs ξ :=
    { hn := hn8
      hr := hr₁2
      hβ0 := by linarith only [hβ0]
      hγ0 := by linarith only [hγ0]
      hε0 := hε0
      hρ0 := hρabs0
      hξ0 := hξ0
      hρ1 := hρabs1
      hDlow := hDlow
      hDhigh := hDhigh
      hnr := hr₁n
      hnξ := hnξ
      hnβ := hβn2
      hrγ := hγr₁
      hξγ := hξγ2'
      hβγ := hβγ2
      hγε := hγε2
      hγρ := hγρabs' }
  -- ## the corrected (session 4) margin bundle `NibbleMarginsStrong`
  have hDlinS : (n : ℝ) / 2 ≤ (Dparam n ρ : ℝ) := hnDge
  have hDgapS : (Dparam n ρ : ℝ) ≤ (1 - ρ_abs) * (n : ℝ) := by
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have h1 : (Dparam n ρ : ℝ) ≤ (1 - ρ) * ((n : ℝ) - 1) := by
      rw [Dparam]
      refine Nat.floor_le ?_
      nlinarith only [hρ4, hρ0, hnR]
    have h2 : (1 - ρ) * ((n : ℝ) - 1) ≤ (1 - ρ_abs) * (n : ℝ) := by
      nlinarith only [hρabs_le, hρ0, hρ4, hnR]
    linarith only [h1, h2]
  have hnibS : NibbleMarginsStrong n ((Dparam n ρ : ℕ) : ℝ) r₁ (2 * β) (2 * γ) ε ρ_abs ξ :=
    Work.Nib.strong_of_margins (n := n) (D := ((Dparam n ρ : ℕ) : ℝ)) (β := β) (γ := γ)
      (ε := ε) (ρ := ρ) (ρ_abs := ρ_abs) (ξ := ξ) (r₁ := r₁)
      hnib hDlinS hDgapS hβ4 hγρs hξε1 hξε2 hn100 hnsup hβr1 hγρabs hε4000 hγ1
  refine ⟨⟨hρabs0, hρabs1, hε0, hγ'0, by norm_num, hξ0, hεsmall, hγρabs, hnbig, hξγρ⟩,
    ⟨hρ0, by linarith only [hρ4], hε0, le_of_lt hξ0, by linarith only [hβ0], hr₁2,
      hξβ, hβr1, hβn24,
      hβhalf⟩,
    hβ0, le_of_lt hγ0, le_of_lt hε0, le_of_lt hξ0, hn1, hnpos, hn4, hr₁2, hr₀2, hr₁r₀,
    hξγ2, hγ2ε, hεn, hk2, hβn, hr₁βn, hS₂num, hnum1, hnD, hEP2num, hL1, hβγ5, hL3,
    hL4ov, hL5in, hnibS⟩

/-- **The numeric parameter hierarchy of §12, with the threshold `N`.**  For a
constant hierarchy `β ≤ γ ≤ 1`, `ρ ≤ 1/4`, `2ρ ≤ ε/2`, `1000·(3γ/2) ≤ ρ_abs ε`
(and the two size conditions linking `r₀` to `r₁` and `β, γ`), there are `ξ` and
`N` with `S12Margins n r₁ r₀ β γ ρ ρ_abs ξ ε (1/2)` for every `n ≥ N`. -/
theorem exists_S12Margins {r₁ r₀ : ℕ} {β γ ρ ρ_abs ε : ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hρ0 : 0 < ρ) (hρ4 : ρ ≤ 1 / 4) (hρabs0 : 0 < ρ_abs) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hr₁2 : 2 ≤ r₁) (hr₀2 : 2 ≤ r₀) (hr₁r₀ : r₁ < r₀)
    (hβγ : β ≤ γ) (hβsq : 8 * β ≤ γ ^ 2)
    (hβ4 : β ≤ γ ^ 4 / 10 ^ 12) (hγρs : 10 ^ 6 * (2 * γ) ≤ ρ_abs) (hρabs_le : ρ_abs ≤ ρ)
    (hγ2ε : γ ≤ 2 * ε)
    (hεsmall : 1000 * ε ≤ 1) (hε4000 : 4000 * ε ≤ 1) (h8γε : 8 * γ ≤ ε)
    (hρlt : 2 * ρ ≤ ε / 2) (hγρabs : 1000 * (3 * γ / 2) ≤ ρ_abs * ε) (hρabs1 : ρ_abs ≤ 1)
    (hβr1 : 16 ≤ (β / 2) * (r₁ : ℝ)) (hr₁β₀ : (r₁ : ℝ) ≤ β * ((r₀ : ℝ) - 1))
    (hr₀big : 2 * (r₁ : ℝ) ≤ γ * ((r₀ : ℝ) - 1)) (hL5in : 10 * Real.sqrt γ < 3 * ε) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ γ * ρ_abs / 10 ^ 4 ∧ 8 * ξ ≤ β / 2 ∧ 10 * ξ ≤ γ / 2 ∧
      4000 * ξ ≤ (3 * γ / 2) * ρ_abs ∧ 10 ^ 12 * ξ ≤ 2 * γ * ρ_abs * ε ∧
      ξ ≤ (2 * γ) ^ 2 / 10 ^ 8 ∧
      ∃ N : ℕ, ∀ n ≥ N, S12Margins n r₁ r₀ β γ ρ ρ_abs ξ ε (1 / 2) := by
  classical
  set ξ : ℝ := min (min (min (γ * ρ_abs) β) (min γ (ρ * ε)))
    (min (2 * γ * ρ_abs * ε / 10 ^ 12) ((2 * γ) ^ 2 / 10 ^ 8)) / 10 ^ 4 with hξdef
  have hξleA : ξ ≤ (min (min (γ * ρ_abs) β) (min γ (ρ * ε))) / 10 ^ 4 :=
    div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hξmin1 : ξ ≤ (γ * ρ_abs) / 10 ^ 4 :=
    le_trans hξleA (div_le_div_of_nonneg_right
      (le_trans (min_le_left _ _) (min_le_left _ _)) (by norm_num))
  have hξmin2 : ξ ≤ β / 10 ^ 4 :=
    le_trans hξleA (div_le_div_of_nonneg_right
      (le_trans (min_le_left _ _) (min_le_right _ _)) (by norm_num))
  have hξmin3 : ξ ≤ γ / 10 ^ 4 :=
    le_trans hξleA (div_le_div_of_nonneg_right
      (le_trans (min_le_right _ _) (min_le_left _ _)) (by norm_num))
  have hξmin4 : ξ ≤ ((2 * γ) ^ 2 / 10 ^ 8) / 10 ^ 4 :=
    le_trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
      (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  have hξmin5 : ξ ≤ ((2 * γ * ρ_abs * ε) / 10 ^ 12) / 10 ^ 4 :=
    le_trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
      (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hξε1 : 10 ^ 12 * ξ ≤ 2 * γ * ρ_abs * ε := by
    have h1 : 10 ^ 12 * ξ ≤ 10 ^ 12 * (((2 * γ * ρ_abs * ε) / 10 ^ 12) / 10 ^ 4) :=
      mul_le_mul_of_nonneg_left hξmin5 (by norm_num)
    have h2 : 10 ^ 12 * (((2 * γ * ρ_abs * ε) / 10 ^ 12) / 10 ^ 4) =
        2 * γ * ρ_abs * ε / 10 ^ 4 := by ring
    have h3 : (0 : ℝ) ≤ 2 * γ * ρ_abs * ε := by positivity
    linarith only [h1, h2.le, h2.ge, h3]
  have hξε2 : ξ ≤ (2 * γ) ^ 2 / 10 ^ 8 := by
    have h3 : (0 : ℝ) ≤ (2 * γ) ^ 2 / 10 ^ 8 := by positivity
    linarith only [hξmin4, h3]
  have hξ0 : 0 < ξ := by
    have h1 : 0 < min (min (γ * ρ_abs) β) (min γ (ρ * ε)) :=
      lt_min (lt_min (mul_pos hγ0 hρabs0) hβ0) (lt_min hγ0 (mul_pos hρ0 hε0))
    have h2 : 0 < min (2 * γ * ρ_abs * ε / 10 ^ 12) ((2 * γ) ^ 2 / 10 ^ 8) :=
      lt_min (by positivity) (by positivity)
    rw [hξdef]
    exact div_pos (lt_min h1 h2) (by norm_num)
  have hξβ : 8 * ξ ≤ β / 2 := by linarith only [hξmin2, hβ0]
  have hξγ : 10 * ξ ≤ γ / 2 := by linarith only [hξmin3, hγ0]
  have hξγρ : 4000 * ξ ≤ (3 * γ / 2) * ρ_abs := by nlinarith only [hξmin1, hγ0, hρabs0]
  refine ⟨ξ, hξ0, hξmin1, hξβ, hξγ, hξγρ, hξε1, hξε2, ?_⟩
  obtain ⟨N, hN⟩ := exists_thresholds_hierarchy_rho_eps (β := β) (γ := γ) (ρ := ρ)
    (ρ_abs := ρ_abs) (ε := ε) r₁ hβ0 hβ1 hγ0 hγ1 hρ0 hρ4 hρabs0 hε0 hε1 hρlt
  -- ## the threshold for `1 ≤ ξn`
  obtain ⟨Nξ, hNξ⟩ : ∃ N : ℕ, ∀ n ≥ N, 1 ≤ ξ * (n : ℝ) := by
    refine ⟨⌈(1 : ℝ) / ξ⌉₊, fun n hn => ?_⟩
    have h1 : (1 : ℝ) / ξ ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    have h2 : ξ * ((1 : ℝ) / ξ) = 1 := by field_simp
    calc (1 : ℝ) = ξ * ((1 : ℝ) / ξ) := h2.symm
      _ ≤ ξ * (n : ℝ) := mul_le_mul_of_nonneg_left h1 (le_of_lt hξ0)
  -- ## the two new `n`-large conditions of the corrected margins
  have hnsup₁ : ∀ᶠ n : ℕ in Filter.atTop,
      10 ^ 100 ≤ 2 * γ * ρ_abs * ε * (n : ℝ) := by
    have h := eventually_const_le_mul_nat (c := 2 * γ * ρ_abs * ε) (a := 10 ^ 100)
      (by positivity)
    exact h.mono fun n hn => by linarith only [hn]
  have hnsup₂ : ∀ᶠ n : ℕ in Filter.atTop,
      10 ^ 400 * ((ρ_abs⁻¹) ^ 6 + ((2 * γ)⁻¹) ^ 16 + (2 * γ * ρ_abs * ε)⁻¹
        + ((2 * γ * ρ_abs * ε)⁻¹) ^ 2 + (r₁ : ℝ)) ≤ (n : ℝ) := by
    have h := eventually_const_le_mul_nat (c := (1 : ℝ)) (a := 10 ^ 400 *
      ((ρ_abs⁻¹) ^ 6 + ((2 * γ)⁻¹) ^ 16 + (2 * γ * ρ_abs * ε)⁻¹
        + ((2 * γ * ρ_abs * ε)⁻¹) ^ 2 + (r₁ : ℝ))) (by norm_num)
    simpa using h
  obtain ⟨Nbig, hNbig⟩ := Filter.eventually_atTop.mp (hnsup₁.and hnsup₂)
  refine ⟨max N (max Nξ Nbig), fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnξ : 1 ≤ ξ * (n : ℝ) :=
    hNξ n (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn))
  have hnBig : Nbig ≤ n := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn)
  obtain ⟨hn100, hnsup'⟩ := hNbig n hnBig
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hN n hnN
  exact S12Margins_of (n := n) (r₁ := r₁) (r₀ := r₀) hβ0 hγ0 hρ0 hρabs0 hε0 hr₁2 hr₀2 hr₁r₀
    hρ4 hγ1 hβγ hβsq hβ4 hγρs hρabs_le hγ2ε hεsmall hε4000 h8γε hγρabs hρabs1 hβr1 hr₁β₀ hr₀big
    hL5in h1 h2 h7 h8 h9 h4 h12 h5 (by exact_mod_cast h6) h3 h11 hξ0 hξβ hξγ hξγρ hnξ hξε1 hξε2
    hn100 hnsup'

/-- **The Type A call site of `exists_S12Margins`.**  With
`γ := γ₁`, `ρ := σ/2`, `ρ_abs := ρ/2 = σ/4`, `ε := 10⁻⁴` and `κ := 1/2`, all the
*constant* hypotheses of `exists_S12Margins` are consequences of
`s12_step1`'s guarantees `γ ≤ (σ/10⁷)²`, `σ ≤ 10⁻⁵`, `32 ≤ βr₁`,
`r₁ < (γ/4)(r₀-1)`; the extra side conditions needed downstream
(`ρ ≪ σ` is the equality `ρ = σ/2` itself, `30√γ ≤ ρ`, `ξ + 15√γ ≤ ρε/2`,
`8 ≤ ρεr₀`, `3γ ≤ √γ`) are part of the conclusion. -/
theorem S12Margins_typeA {r₁ r₀ : ℕ} {β γ σ : ℝ}
    (hβ0 : 0 < β) (hγ0 : 0 < γ) (hσ0 : 0 < σ) (hβγ : β ≤ γ) (hβsq : 8 * β ≤ γ ^ 2)
    (hβ4 : β ≤ γ ^ 4 / 10 ^ 12)
    (hγσ : γ ≤ (σ / 10 ^ 7) ^ 2) (hσ1 : σ ≤ 1 / 10 ^ 5)
    (hr₁2 : 2 ≤ r₁) (hr₀2 : 2 ≤ r₀) (hr₁r₀ : r₁ < r₀)
    (hβr1 : 32 ≤ β * (r₁ : ℝ)) (hr₁β₀ : (r₁ : ℝ) ≤ β * ((r₀ : ℝ) - 1))
    (hr₀big : (r₁ : ℝ) < γ / 4 * ((r₀ : ℝ) - 1)) :
    ∃ ξ : ℝ, 0 < ξ ∧
      (30 * Real.sqrt γ ≤ σ / 2) ∧
      (ξ + 15 * Real.sqrt γ ≤ σ / 2 * (1 / 10 ^ 4) / 2) ∧
      (8 ≤ σ / 2 * (1 / 10 ^ 4) * (r₀ : ℝ)) ∧ (3 * γ ≤ Real.sqrt γ) ∧
      ∃ N : ℕ, ∀ n ≥ N,
        S12Margins n r₁ r₀ β γ (σ / 2) (σ / 4) ξ (1 / 10 ^ 4) (1 / 2) := by
  classical
  have hσle1 : σ ≤ 1 := by linarith only [hσ1]
  have hγ1 : γ ≤ 1 := by
    have h : (σ / 10 ^ 7) ^ 2 ≤ 1 := by nlinarith only [hσle1, hσ0]
    linarith only [hγσ, h]
  have hβ1 : β ≤ 1 := le_trans hβγ hγ1
  have hsqrt : Real.sqrt γ ≤ σ / 10 ^ 7 := by
    have h1 : Real.sqrt γ ≤ Real.sqrt ((σ / 10 ^ 7) ^ 2) := Real.sqrt_le_sqrt hγσ
    rwa [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)] at h1
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt γ := Real.sqrt_nonneg γ
  -- the constant hypotheses of `exists_S12Margins`
  have hA : 2 * (σ / 2) ≤ (1 / 10 ^ 4) / 2 := by nlinarith only [hσ1]
  have hB : (1000 : ℝ) * (1 / 10 ^ 4) ≤ 1 := by norm_num
  have hC : (σ / 2) * 2 ≤ (1 / 10 ^ 4) / 2 * 2 := by nlinarith only [hσ1]
  have hD : 8 * γ ≤ 1 / 10 ^ 4 := by
    have h : γ ≤ 1 / 10 ^ 15 := by nlinarith only [hγσ, hσ1, hσ0]
    linarith only [h]
  have hE : 1000 * (3 * γ / 2) ≤ σ / 4 * (1 / 10 ^ 4) := by
    have h : γ ≤ σ * 1 / 10 ^ 14 := by nlinarith only [hγσ, hσ1, hσ0]
    nlinarith only [h, hσ0, hσle1]
  have hF : (σ / 4 : ℝ) ≤ 1 := by nlinarith only [hσ1]
  have hG : 16 ≤ (β / 2) * (r₁ : ℝ) := by linarith only [hβr1]
  have hH : 10 * Real.sqrt γ < 3 * (1 / 10 ^ 4) := by nlinarith only [hsqrt, hσ1, hσ0]
  have hγ14 : γ ≤ σ ^ 2 / 10 ^ 14 := by
    have h2 : ((σ / 10 ^ 7) ^ 2 : ℝ) = σ ^ 2 / 10 ^ 14 := by ring
    linarith only [hγσ, h2.le, h2.ge]
  obtain ⟨ξ, hξ0, hξle, hξβ, hξγ, hξγρ, -, -, hN⟩ :=
    exists_S12Margins (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (ρ := σ / 2)
      (ρ_abs := σ / 4) (ε := 1 / 10 ^ 4) hβ0 hβ1 hγ0 hγ1 (by positivity) (by nlinarith only [hσ1])
      (by positivity) (by norm_num) (by norm_num) hr₁2 hr₀2 hr₁r₀ hβγ hβsq hβ4
      (by nlinarith only [hγ14, hσ0, hσle1])
      (by nlinarith only [hσ0])
      (by nlinarith only [hγσ, hσ1, hσ0])
      hB (by norm_num) hD hA hE hF hG hr₁β₀ (by linarith only [hr₀big]) hH
  refine ⟨ξ, hξ0, ?_, ?_, ?_, ?_, hN⟩
  · -- `30√γ ≤ σ/2`
    nlinarith only [hsqrt, hσ0]
  · -- `ξ + 15√γ ≤ ρε/2`
    have h1 : ξ ≤ γ * (σ / 4) / 10 ^ 4 := hξle
    have h2 : γ * (σ / 4) / 10 ^ 4 ≤ σ * (1 / 10 ^ 4) * (1 / 10 ^ 5) := by
      have h : γ ≤ σ * (1 / 10 ^ 5) := by nlinarith only [hγσ, hσ1, hσ0]
      nlinarith only [h, hσ0, hσle1]
    nlinarith only [h1, h2, hsqrt, hσ0, hξ0]
  · -- `8 ≤ ρεr₀`
    have h1 : 8 < γ * ((r₀ : ℝ) - 1) := by
      have h2 : 4 * (2 : ℝ) ≤ 4 * (r₁ : ℝ) := by
        have : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr₁2
        linarith only [this]
      nlinarith only [hr₀big, h2]
    have h2 : γ ≤ σ * (1 / 10 ^ 5) := by nlinarith only [hγσ, hσ1, hσ0]
    have h3 : (8 : ℝ) / γ < (r₀ : ℝ) := by
      rw [div_lt_iff₀ hγ0]
      linarith only [h1, hγ0, Nat.cast_nonneg (α := ℝ) r₀]
    have h3' : (8 : ℝ) / γ * (σ / 2 * (1 / 10 ^ 4)) <
        (r₀ : ℝ) * (σ / 2 * (1 / 10 ^ 4)) :=
      mul_lt_mul_of_pos_right h3 (by positivity)
    have h5 : (8 : ℝ) ≤ 4 * (1 / 10 ^ 4) * σ / γ := by
      rw [le_div_iff₀ hγ0]
      nlinarith only [h2, hσ0]
    have h6 : (8 : ℝ) / γ * (σ / 2 * (1 / 10 ^ 4)) = 4 * (1 / 10 ^ 4) * σ / γ := by ring
    rw [h6] at h3'
    linarith only [h3', h5]
  · -- `3γ ≤ √γ`
    have hγ9 : γ ≤ 1 / 9 := by nlinarith only [hγσ, hσ1, hσ0]
    have h1 : Real.sqrt γ ≤ 1 / 3 := by
      have h : Real.sqrt γ ≤ Real.sqrt ((1 / 3 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by linarith only [hγ9])
      rwa [show Real.sqrt ((1 / 3 : ℝ) ^ 2) = 1 / 3 from by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]] at h
    nlinarith only [h1, hγ0, hsqrt0, Real.sq_sqrt (le_of_lt hγ0)]

/-- **The Type B call site of `exists_S12Margins`.**  Here `γ := γ₂` is tiny
(`γ ≤ 10⁻²⁴`) and `ρ := 10⁻⁵`, `ρ_abs := ρ/2`, `ε := 10⁻⁴`, `κ := 1/2`; as in
the Type A case all the constant hypotheses follow from `s12_step1`'s
guarantees (`γ₂ ≤ 10⁻²⁴`, `32 ≤ βr₁`, `r₁ < (γ/4)(r₀-1)`). -/
theorem S12Margins_typeB {r₁ r₀ : ℕ} {β γ : ℝ}
    (hβ0 : 0 < β) (hγ0 : 0 < γ) (hβγ : β ≤ γ) (hβsq : 8 * β ≤ γ ^ 2)
    (hβ4 : β ≤ γ ^ 4 / 10 ^ 12)
    (hγ24 : γ ≤ (10 : ℝ) ^ (-24 : ℤ))
    (hr₁2 : 2 ≤ r₁) (hr₀2 : 2 ≤ r₀) (hr₁r₀ : r₁ < r₀)
    (hβr1 : 32 ≤ β * (r₁ : ℝ)) (hr₁β₀ : (r₁ : ℝ) ≤ β * ((r₀ : ℝ) - 1))
    (hr₀big : (r₁ : ℝ) < γ / 4 * ((r₀ : ℝ) - 1)) :
    ∃ ξ : ℝ, 0 < ξ ∧ (30 * Real.sqrt γ ≤ 1 / 10 ^ 5) ∧
      (ξ + 15 * Real.sqrt γ ≤ 1 / 10 ^ 5 * (1 / 10 ^ 4) / 2) ∧
      (8 ≤ 1 / 10 ^ 5 * (1 / 10 ^ 4) * (r₀ : ℝ)) ∧ (3 * γ ≤ Real.sqrt γ) ∧
      ∃ N : ℕ, ∀ n ≥ N,
        S12Margins n r₁ r₀ β γ (1 / 10 ^ 5) (1 / (2 * 10 ^ 5)) ξ (1 / 10 ^ 4) (1 / 2) := by
  classical
  have hγ24' : γ ≤ 1 / 10 ^ 24 := by
    have := hγ24
    norm_num at this ⊢
    exact this
  have hγ1 : γ ≤ 1 := by linarith only [hγ24']
  have hβ1 : β ≤ 1 := le_trans hβγ hγ1
  have hsqrt : Real.sqrt γ ≤ 1 / 10 ^ 12 := by
    have h : Real.sqrt γ ≤ Real.sqrt ((1 / 10 ^ 12 : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith only [hγ24'])
    rwa [show Real.sqrt ((1 / 10 ^ 12 : ℝ) ^ 2) = 1 / 10 ^ 12 from by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]] at h
  have hsqrt0 : (0 : ℝ) ≤ Real.sqrt γ := Real.sqrt_nonneg γ
  obtain ⟨ξ, hξ0, hξle, hξβ, hξγ, hξγρ, -, -, hN⟩ :=
    exists_S12Margins (r₁ := r₁) (r₀ := r₀) (β := β) (γ := γ) (ρ := 1 / 10 ^ 5)
      (ρ_abs := 1 / (2 * 10 ^ 5)) (ε := 1 / 10 ^ 4) hβ0 hβ1 hγ0 hγ1 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr₁2 hr₀2 hr₁r₀ hβγ hβsq hβ4
      (by nlinarith only [hγ24']) (by norm_num) (by nlinarith only [hγ24']) (by norm_num)
      (by norm_num) (by nlinarith only [hγ24']) (by norm_num) (by nlinarith only [hγ24'])
      (by norm_num) (by linarith only [hβr1]) hr₁β₀ (by linarith only [hr₀big])
      (by nlinarith only [hsqrt])
  refine ⟨ξ, hξ0, ?_, ?_, ?_, ?_, hN⟩
  · nlinarith only [hsqrt]
  · have h1 : ξ ≤ γ * (1 / (2 * 10 ^ 5)) / 10 ^ 4 := hξle
    nlinarith only [h1, hsqrt, hξ0, hγ24']
  · have h1 : 8 < γ * ((r₀ : ℝ) - 1) := by
      have h2 : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr₁2
      nlinarith only [hr₀big, h2]
    have h3 : (8 : ℝ) / γ < (r₀ : ℝ) := by
      rw [div_lt_iff₀ hγ0]
      linarith only [h1, hγ0, Nat.cast_nonneg (α := ℝ) r₀]
    have h3' : (8 : ℝ) / γ * (1 / 10 ^ 5 * (1 / 10 ^ 4)) <
        (r₀ : ℝ) * (1 / 10 ^ 5 * (1 / 10 ^ 4)) :=
      mul_lt_mul_of_pos_right h3 (by norm_num)
    have h5 : (8 : ℝ) ≤ 8 * (1 / 10 ^ 5 * (1 / 10 ^ 4)) / γ := by
      rw [le_div_iff₀ hγ0]
      nlinarith only [hγ24']
    have h6 : (8 : ℝ) / γ * (1 / 10 ^ 5 * (1 / 10 ^ 4)) =
        8 * (1 / 10 ^ 5 * (1 / 10 ^ 4)) / γ := by ring
    rw [h6] at h3'
    linarith only [h3', h5]
  · have hγ9 : γ ≤ 1 / 9 := by linarith only [hγ24']
    have h1 : Real.sqrt γ ≤ 1 / 3 := by
      have h : Real.sqrt γ ≤ Real.sqrt ((1 / 3 : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt (by linarith only [hγ9])
      rwa [show Real.sqrt ((1 / 3 : ℝ) ^ 2) = 1 / 3 from by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by norm_num)]] at h
    nlinarith only [h1, hγ0, hsqrt0, Real.sq_sqrt (le_of_lt hγ0)]

end

end ErdosFaberLovaszConjecture

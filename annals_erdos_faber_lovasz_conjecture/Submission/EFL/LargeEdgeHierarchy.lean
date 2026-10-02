import Submission.EFL.LargeEdgeCase22Main

/-!
# The parameter hierarchy of Theorem 6.1 (`large-edge-thm`)

This module discharges the numeric hypothesis bundle of
`LargeEdgeCases`/`LargeEdgeCase22Main` and hence deduces the paper's
Theorem 6.7 (`large-edge-thm`, `LargeEdgeThmStatement`) from the two deep
inputs `MolloyReedStatement` and `KahnStatement` together with Lemma 5.1.

The parameter hierarchy is `0 < 1/n₀ ≪ 1/r₀ ≪ 1/r₁, β ≪ γ₁ ≪ σ ≪ δ ≪ γ₂ ≪ 1`
(the paper's convention).  Concretely the thresholds are

* `δThr γ₂ = γ₂^5 / 10^40`,
* `σThr γ₂ δ = δ^5 / 10^20`,
* `γ₁Thr δ σ = σ^5 / 10^20`,
* `βThr σ γ₁ = γ₁^5 / 10^20`,
* `R₁Thr` is large enough for the two Reordering-Lemma applications App 1
  and App 2 (`app1_margins` and `reordering_threshold`),
* and `N₀` is large enough for the `n`-margins (`δ²n ≫ 1`, `σn ≫ 1/β²`, the
  `bigFinset` counts, the colour budgets, `r₀ < βn/4`, …).

All the arithmetic lives in the `*_margin` lemmas below.

The remaining step — the assembly of `LargeEdgeThmStatement`, i.e. choosing
the thresholds and discharging every `n`-margin — is in progress; the
elaborated draft (which already fixes and verifies the threshold chain
`δ₀, σ₀, γ₁₀, β₀, R₁, R₀, N₀`) is kept in
`Submission/EFL/LargeEdgeHierarchyWIP.txt` (not part of the build).
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-! ## Counting: there are few `bigFinset` edges -/

/-- **The `bigFinset` count.**  In a linear family on `Fin n` there are at most
`8/α₂²` edges of size at least `(α₂/2)n`. -/
theorem bigFinset_card_le {n : ℕ} {α₂ : ℝ} {𝓖 : Hypergraph (Fin n)} [Fintype 𝓖]
    (hlin : 𝓖.IsLinear) (hα : 0 < α₂) (hαn : 4 ≤ α₂ * (n : ℝ)) :
    (((bigFinset α₂ 𝓖).card : ℕ) : ℝ) ≤ 8 / α₂ ^ 2 := by
  classical
  have hn1 : 1 ≤ n := by
    by_contra hcon
    have hz : n = 0 := by omega
    subst hz
    simp only [Nat.cast_zero, mul_zero] at hαn
    linarith [hα]
  set s : ℕ := ⌈α₂ * (n : ℝ) / 2⌉₊ with hs
  have hs2 : 2 ≤ s := by
    rw [hs]
    have h2 : (2 : ℝ) ≤ α₂ * (n : ℝ) / 2 := by linarith
    calc (2 : ℕ) = ⌈(2 : ℝ)⌉₊ := by simp
      _ ≤ ⌈α₂ * (n : ℝ) / 2⌉₊ := Nat.ceil_mono h2
  have hsge : α₂ * (n : ℝ) / 2 ≤ (s : ℝ) := by
    rw [hs]; exact Nat.le_ceil _
  have hspos : (0 : ℝ) < (s : ℝ) := by
    have : (0 : ℕ) < s := by omega
    exact_mod_cast this
  have hsub : (bigFinset α₂ 𝓖).card ≤
      ((Finset.univ : Finset 𝓖).filter
        (fun e : 𝓖 => s ≤ edgeSize (e : Set (Fin n)))).card := by
    apply Finset.card_le_card
    intro e he
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hs]
    refine Nat.ceil_le.mpr ?_
    rw [show α₂ * (n : ℝ) / 2 = α₂ / 2 * (n : ℝ) by ring]
    exact (mem_bigFinset α₂ 𝓖 e).mp he
  have hcard := card_edges_size_ge_le (𝓗 := 𝓖) hlin hs2
  have hstep : ((bigFinset α₂ 𝓖).card : ℝ) ≤
      ((n * (n - 1) / (s * (s - 1)) : ℕ) : ℝ) := by
    exact_mod_cast le_trans hsub hcard
  have hcast : ((n * (n - 1) / (s * (s - 1)) : ℕ) : ℝ) ≤
      (n : ℝ) * ((n : ℝ) - 1) / ((s : ℝ) * ((s : ℝ) - 1)) := by
    refine le_trans Nat.cast_div_le ?_
    have h1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
    have h2 : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ s)]; norm_num
    rw [Nat.cast_mul, Nat.cast_mul, h1, h2]
  have hden : (0 : ℝ) < (s : ℝ) * ((s : ℝ) - 1) := by
    have : (1 : ℝ) < (s : ℝ) := by
      have : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs2
      linarith
    positivity
  have hnum : (n : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) ^ 2 := by
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  have hss : α₂ ^ 2 * (n : ℝ) ^ 2 / 8 ≤ (s : ℝ) * ((s : ℝ) - 1) := by
    have h1 : (s : ℝ) / 2 ≤ (s : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs2
      linarith
    have h2 : (s : ℝ) * ((s : ℝ) / 2) ≤ (s : ℝ) * ((s : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hspos)
    have h3 : α₂ ^ 2 * (n : ℝ) ^ 2 / 4 ≤ (s : ℝ) ^ 2 := by
      nlinarith [hsge, hα, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    nlinarith [h2, h3]
  have hfinal : (n : ℝ) * ((n : ℝ) - 1) / ((s : ℝ) * ((s : ℝ) - 1)) ≤ 8 / α₂ ^ 2 := by
    rw [div_le_div_iff₀ hden (by positivity : (0 : ℝ) < α₂ ^ 2)]
    nlinarith [hss, hnum, hα]
  linarith [hstep, hcast, hfinal]

def δThr (γ₂ : ℝ) : ℝ := γ₂ ^ 7 / 10 ^ 40

def σThr (δ : ℝ) : ℝ := δ ^ 12 / 10 ^ 6

/-- `volBound app3tau app3K ≥ 10^{-35}`: the App-3 volume bound is a
(fixed) positive constant. -/
theorem app3_volBound_ge : (1 : ℝ) / 10 ^ 35 ≤ volBound app3tau app3K := by
  have hK : ((app3K : ℕ) : ℝ) = 4000000 := by
    simp only [app3K]; norm_num
  have hτ : app3tau = 1 - 1 / 2000 := rfl
  have hτ1 : app3tau ≤ 1 := by rw [hτ]; norm_num
  have hτq_le : tauQuarter app3tau ≤ 1 := tauQuarter_le_one hτ1
  have hτq_nn : (0 : ℝ) ≤ tauQuarter app3tau := tauQuarter_nonneg _
  have hq : (1 : ℝ) / 4000 ≤ 1 - app3tau - 7 * tauQuarter app3tau / ((app3K : ℕ) : ℝ) := by
    have h1 : 1 - app3tau = 1 / 2000 := by rw [hτ]; norm_num
    have h2 : 7 * tauQuarter app3tau / ((app3K : ℕ) : ℝ) ≤ 7 / 4000000 := by
      rw [hK]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      linarith [hτq_le]
    linarith [h1, h2]
  have hA : 1 + 3 * tauQuarter app3tau * ((app3K : ℕ) : ℝ) ^ 4 ≤ 10 ^ 27 := by
    rw [hK]
    nlinarith [hτq_le, hτq_nn]
  have hsize : sizeFactor app3tau app3K =
      1 + 3 * tauQuarter app3tau * ((app3K : ℕ) : ℝ) ^ 4 := rfl
  rw [volBound, hsize]
  have hpos : (0 : ℝ) < 1 + 3 * tauQuarter app3tau * ((app3K : ℕ) : ℝ) ^ 4 := by positivity
  rw [le_div_iff₀ hpos]
  have hq2 : (1 : ℝ) / (4000 * 4000) ≤
      (1 - app3tau - 7 * tauQuarter app3tau / ((app3K : ℕ) : ℝ)) ^ 2 := by
    nlinarith [hq, (Nat.cast_nonneg (app3K : ℕ) : (0 : ℝ) ≤ ((app3K : ℕ) : ℝ))]
  nlinarith [hq2, hA]

/-- `tauQuarter (3σ) ≤ δ³/20` when `σ ≤ δ^{12}/10⁶` and `δ ≤ 1`. -/
theorem tauQuarter_three_sigma_le {δ σ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hσ0 : 0 < σ) (hσ : σ ≤ δ ^ 12 / 10 ^ 6) :
    tauQuarter (3 * σ) ≤ δ ^ 3 / 20 := by
  have hb : (0 : ℝ) < δ ^ 3 / 20 := by positivity
  have hσ4 : 3 * σ ≤ (δ ^ 3 / 20) ^ 4 := by
    have h1 : (δ ^ 3 / 20) ^ 4 = δ ^ 12 / 160000 := by ring
    rw [h1]
    have hd : (0 : ℝ) ≤ δ ^ 12 := by positivity
    have h5 : 3 * (δ ^ 12 / 10 ^ 6) ≤ δ ^ 12 / 160000 := by
      rw [show 3 * (δ ^ 12 / 10 ^ 6) = (3 / 10 ^ 6) * δ ^ 12 by ring,
        show δ ^ 12 / 160000 = (1 / 160000) * δ ^ 12 by ring]
      exact mul_le_mul_of_nonneg_right (by norm_num) hd
    linarith [hσ, h5]
  have hA : Real.sqrt (3 * σ) ≤ (δ ^ 3 / 20) ^ 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by nlinarith [hσ4, hb]⟩
  have hb2 : (0 : ℝ) ≤ (δ ^ 3 / 20) ^ 2 := by positivity
  have hB : Real.sqrt (Real.sqrt (3 * σ)) ≤ Real.sqrt ((δ ^ 3 / 20) ^ 2) :=
    Real.sqrt_le_sqrt hA
  rw [Real.sqrt_sq (le_of_lt hb)] at hB
  exact hB

/-- `volBound (3σ) 1 ≥ 1 − δ³` when `σ ≤ δ^{12}/10⁶` and `δ ≤ 1`. -/
theorem volBound_three_sigma_ge {δ σ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hσ0 : 0 < σ) (hσ : σ ≤ δ ^ 12 / 10 ^ 6) :
    (1 : ℝ) - δ ^ 3 ≤ volBound (3 * σ) 1 := by
  have ht := tauQuarter_three_sigma_le hδ0 hδ1 hσ0 hσ
  have ht0 : (0 : ℝ) ≤ tauQuarter (3 * σ) := tauQuarter_nonneg _
  have hσ3 : 3 * σ ≤ δ ^ 3 / 20 := by
    have h2 : 3 * σ ≤ 3 * (δ ^ 12 / 10 ^ 6) := by linarith [hσ]
    have h3 : 3 * (δ ^ 12 / 10 ^ 6) = (3 / 10 ^ 6) * δ ^ 12 := by ring
    have hδ9 : δ ^ 9 ≤ 1 := pow_le_one₀ (le_of_lt hδ0) (by linarith)
    have h4 : (3 / 10 ^ 6) * δ ^ 12 ≤ (1 / 20) * δ ^ 3 := by
      have hb : (0 : ℝ) < δ ^ 3 := by positivity
      nlinarith [hδ9, hb]
    nlinarith [h2, h3, h4]
  have hu1 : δ ^ 3 ≤ 1 := pow_le_one₀ (le_of_lt hδ0) hδ1
  have hu0 : (0 : ℝ) < δ ^ 3 := by positivity
  have hq : 1 - 2 * δ ^ 3 / 5 ≤ 1 - 3 * σ - 7 * tauQuarter (3 * σ) := by
    linarith [ht, hσ3]
  have hA : 3 * tauQuarter (3 * σ) ≤ δ ^ 3 / 5 := by linarith [ht]
  have hvol : volBound (3 * σ) 1 =
      (1 - 3 * σ - 7 * tauQuarter (3 * σ)) ^ 2 / (1 + 3 * tauQuarter (3 * σ)) := by
    simp only [volBound, sizeFactor, Nat.cast_one]
    norm_num
  rw [hvol]
  have hden : (0 : ℝ) < 1 + 3 * tauQuarter (3 * σ) := by linarith
  rw [le_div_iff₀ hden]
  have hqnn : (0 : ℝ) ≤ 1 - 2 * δ ^ 3 / 5 := by linarith
  have hq2 : (1 - 2 * δ ^ 3 / 5) ^ 2 ≤ (1 - 3 * σ - 7 * tauQuarter (3 * σ)) ^ 2 := by
    nlinarith [hq, hqnn]
  have hprod : (1 - δ ^ 3) * (1 + 3 * tauQuarter (3 * σ)) ≤
      (1 - δ ^ 3) * (1 + δ ^ 3 / 5) := by
    have h1 : (0 : ℝ) ≤ 1 - δ ^ 3 := by linarith
    nlinarith [hA, h1]
  have hcomp : (1 - δ ^ 3) * (1 + δ ^ 3 / 5) ≤ (1 - 2 * δ ^ 3 / 5) ^ 2 := by
    nlinarith [hu0]
  linarith [hq2, hprod, hcomp]

/-- `sizeFactor (3σ) 1 ≤ (1+δ)√(1−4σ)` when `σ ≤ δ^{12}/10⁶` and `δ ≤ 1`. -/
theorem sizeFactor_three_sigma_le {δ σ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hσ0 : 0 < σ) (hσ : σ ≤ δ ^ 12 / 10 ^ 6) :
    sizeFactor (3 * σ) 1 ≤ (1 + δ) * Real.sqrt (1 - 4 * σ) := by
  have ht := tauQuarter_three_sigma_le hδ0 hδ1 hσ0 hσ
  have hσ3 : 3 * σ ≤ δ ^ 3 / 20 := by
    have h2 : 3 * σ ≤ 3 * (δ ^ 12 / 10 ^ 6) := by linarith [hσ]
    have h3 : 3 * (δ ^ 12 / 10 ^ 6) = (3 / 10 ^ 6) * δ ^ 12 := by ring
    have hδ9 : δ ^ 9 ≤ 1 := pow_le_one₀ (le_of_lt hδ0) (by linarith)
    have h4 : (3 / 10 ^ 6) * δ ^ 12 ≤ (1 / 20) * δ ^ 3 := by
      have hb : (0 : ℝ) < δ ^ 3 := by positivity
      nlinarith [hδ9, hb]
    nlinarith [h2, h3, h4]
  have hσ4 : 4 * σ ≤ 1 / 2 := by
    have h1 : σ ≤ δ ^ 12 / 10 ^ 6 := hσ
    have h2 : δ ^ 12 ≤ 1 := pow_le_one₀ (le_of_lt hδ0) hδ1
    nlinarith [h1, h2, hσ0]
  have hsize : sizeFactor (3 * σ) 1 = 1 + 3 * tauQuarter (3 * σ) := by
    simp only [sizeFactor, Nat.cast_one]
    norm_num
  rw [hsize]
  have hsq : (1 : ℝ) - 4 * σ ≤ Real.sqrt (1 - 4 * σ) := by
    have h0' : (0 : ℝ) ≤ 1 - 4 * σ := by linarith [hσ4]
    rw [Real.le_sqrt h0' h0']
    nlinarith [hσ4]
  have hδ3 : δ ^ 3 ≤ δ := by
    have hδ2 : δ ^ 2 ≤ 1 := pow_le_one₀ (le_of_lt hδ0) hδ1
    nlinarith [hδ0, hδ2]
  have hkey : (1 : ℝ) + 3 * tauQuarter (3 * σ) ≤ 1 + δ / 2 := by
    have h1 : 3 * tauQuarter (3 * σ) ≤ 3 * (δ ^ 3 / 20) := by linarith [ht]
    have h2 : 3 * (δ ^ 3 / 20) ≤ δ / 2 := by linarith [hδ3]
    linarith [h1, h2]
  have hmain : (1 : ℝ) + δ / 2 ≤ (1 + δ) * Real.sqrt (1 - 4 * σ) := by
    have h1 : (1 : ℝ) + δ / 2 ≤ (1 + δ) * (1 - 4 * σ) := by
      nlinarith [hσ4, hσ0, hδ0, hδ1]
    exact le_trans h1 (mul_le_mul_of_nonneg_left hsq (by linarith))
  linarith [hkey, hmain]

/-- `volBound (app1tau γ₂) (app1K γ₂) > δ³` for `δ ≤ γ₂^7/10^{40}`. -/
theorem app1_volBound_gt {γ₂ δ : ℝ} (h0 : 0 < γ₂) (h1 : γ₂ ≤ 1 / 2000) (hδ0 : 0 < δ)
    (hδ : δ ≤ γ₂ ^ 7 / 10 ^ 40) :
    δ ^ 3 < volBound (app1tau γ₂) (app1K γ₂) := by
  have hvol := app1_volBound_ge h0 h1
  have hγ1 : γ₂ ≤ 1 := by linarith
  have hδ3 : δ ^ 3 ≤ γ₂ ^ 21 / 10 ^ 120 := by
    have h2 : δ ^ 3 ≤ (γ₂ ^ 7 / 10 ^ 40) ^ 3 :=
      pow_le_pow_left₀ (le_of_lt hδ0) hδ 3
    have h4 : (γ₂ ^ 7 / 10 ^ 40) ^ 3 = γ₂ ^ 21 / 10 ^ 120 := by ring
    rw [h4] at h2
    exact h2
  have hle : γ₂ ^ 21 / 10 ^ 120 < γ₂ ^ 21 := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 120)]
    have h5 : γ₂ ^ 21 * 1 < γ₂ ^ 21 * 10 ^ 120 :=
      mul_lt_mul_of_pos_left (by norm_num) (pow_pos h0 21)
    linarith [h5]
  have hmono : γ₂ ^ 21 ≤ γ₂ ^ 20 :=
    pow_le_pow_of_le_one (le_of_lt h0) hγ1 (by norm_num : 20 ≤ 21)
  linarith [hvol, hδ3, hle, hmono]

/-- `δ ≤ volBound app3tau app3K` for `δ ≤ γ₂^7/10^{40}`. -/
theorem δThr_le_app3 {γ₂ δ : ℝ} (h0 : 0 < γ₂) (h1 : γ₂ ≤ 1)
    (hδ : δ ≤ γ₂ ^ 7 / 10 ^ 40) :
    δ ≤ volBound app3tau app3K := by
  have hvol := app3_volBound_ge
  have h2 : γ₂ ^ 7 / 10 ^ 40 ≤ (1 : ℝ) / 10 ^ 40 := by
    have h3 : γ₂ ^ 7 ≤ 1 := pow_le_one₀ (le_of_lt h0) h1
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 40) (by norm_num : (0 : ℝ) < 10 ^ 40)]
    linarith [h3]
  have h4 : (1 : ℝ) / 10 ^ 40 ≤ 1 / 10 ^ 35 := by norm_num
  linarith [hδ, h2, h4, hvol]

variable {n : ℕ}

/-- `8 ≤ δ²n` from `n ≥ 8/δ²`. -/
theorem margin_sq_mul {δ : ℝ} (hδ0 : 0 < δ) {m : ℕ}
    (h : 8 / δ ^ 2 ≤ (m : ℝ)) : (8 : ℝ) ≤ δ ^ 2 * (m : ℝ) := by
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < δ ^ 2)] at h
  linarith [h]

/-- `(1+δ)√n ≤ δn/2` from `n ≥ 16/δ²` and `δ ≤ 1`. -/
theorem margin_sqrt {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {m : ℕ}
    (h : 16 / δ ^ 2 ≤ (m : ℝ)) : (1 + δ) * Real.sqrt (m : ℝ) ≤ δ * (m : ℝ) / 2 := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have h1 : (0 : ℝ) < 16 / δ ^ 2 := by positivity
    linarith
  have hsq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (le_of_lt hm0)
  have hspos : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
  have h2 : 4 / δ ≤ Real.sqrt (m : ℝ) := by
    refine (Real.le_sqrt (show (0 : ℝ) ≤ 4 / δ by positivity)
      (show (0 : ℝ) ≤ (m : ℝ) by positivity)).mpr ?_
    have h5 : (4 / δ) ^ 2 = 16 / δ ^ 2 := by ring
    rw [h5]; exact h
  have hmain : (1 + δ) ≤ δ * Real.sqrt (m : ℝ) / 2 := by
    have h3 : δ * (4 / δ) ≤ δ * Real.sqrt (m : ℝ) :=
      mul_le_mul_of_nonneg_left h2 (le_of_lt hδ0)
    have h4 : δ * (4 / δ) = 4 := by field_simp
    have h5 : 2 * (1 + δ) ≤ 4 := by linarith
    linarith [h3, h4, h5]
  calc (1 + δ) * Real.sqrt (m : ℝ) ≤ (δ * Real.sqrt (m : ℝ) / 2) * Real.sqrt (m : ℝ) :=
        mul_le_mul_of_nonneg_right hmain (le_of_lt hspos)
    _ = δ * (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)) / 2 := by ring
    _ = δ * (m : ℝ) / 2 := by rw [← pow_two, hsq]

/-- `(1−δ)√n ≤ βn/4` from `n ≥ 16/β²` and `δ ≤ 1/2`. -/
theorem margin_huge {δ β : ℝ} (hδ0 : 0 < δ) (hβ0 : 0 < β) (hδ1 : δ ≤ 1 / 2) {m : ℕ}
    (h : 16 / β ^ 2 ≤ (m : ℝ)) : (1 - δ) * Real.sqrt (m : ℝ) ≤ β * (m : ℝ) / 4 := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by
    have h1 : (0 : ℝ) < 16 / β ^ 2 := by positivity
    linarith
  have hsq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (le_of_lt hm0)
  have hspos : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
  have h2 : 4 / β ≤ Real.sqrt (m : ℝ) := by
    refine (Real.le_sqrt (show (0 : ℝ) ≤ 4 / β by positivity)
      (show (0 : ℝ) ≤ (m : ℝ) by positivity)).mpr ?_
    have h5 : (4 / β) ^ 2 = 16 / β ^ 2 := by ring
    rw [h5]; exact h
  have hmain : (1 - δ) ≤ β * Real.sqrt (m : ℝ) / 4 := by
    have h3 : β * (4 / β) ≤ β * Real.sqrt (m : ℝ) :=
      mul_le_mul_of_nonneg_left h2 (le_of_lt hβ0)
    have h4 : β * (4 / β) = 4 := by field_simp
    have h5 : 4 * (1 - δ) ≤ 4 := by linarith
    linarith [h3, h4, h5]
  calc (1 - δ) * Real.sqrt (m : ℝ) ≤ (β * Real.sqrt (m : ℝ) / 4) * Real.sqrt (m : ℝ) :=
        mul_le_mul_of_nonneg_right hmain (le_of_lt hspos)
    _ = β * (Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ)) / 4 := by ring
    _ = β * (m : ℝ) / 4 := by rw [← pow_two, hsq]


/-- `⌊γ₂n⌋₊ + ⌈32/β²⌉₊ ≤ n` for `n ≥ 64/β² + 4`, `0 < γ₂ ≤ 1/2`. -/
theorem margin_roomNat {β γ₂ : ℝ} (hβ0 : 0 < β) (hγ₂0 : 0 < γ₂) (hγ₂1 : γ₂ ≤ 1 / 2)
    {m : ℕ} (h : 64 / β ^ 2 + 4 ≤ (m : ℝ)) :
    ⌊γ₂ * (m : ℝ)⌋₊ + ⌈32 / β ^ 2⌉₊ ≤ m := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h1 : (⌊γ₂ * (m : ℝ)⌋₊ : ℝ) ≤ γ₂ * (m : ℝ) := Nat.floor_le (by positivity)
  have h2 : (⌈32 / β ^ 2⌉₊ : ℝ) < 32 / β ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have h3 : γ₂ * (m : ℝ) ≤ (m : ℝ) / 2 := by nlinarith [hγ₂1, hm0]
  have h4 : 32 / β ^ 2 + 1 ≤ (m : ℝ) / 2 := by
    have h' := div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)
    have h2 : (64 / β ^ 2 + 4) / 2 = 32 / β ^ 2 + 2 := by ring
    rw [h2] at h'
    linarith [h']
  have h5 : ((⌊γ₂ * (m : ℝ)⌋₊ + ⌈32 / β ^ 2⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) := by
    push_cast
    linarith [h1, h2, h3, h4]
  exact_mod_cast h5

/-- `#bigFinset (β/5) 𝓖 < σn/2` for a linear family and `n ≥ 401/(β²σ)`. -/
theorem margin_bigFinset {β σ : ℝ} (hβ0 : 0 < β) (hσ0 : 0 < σ) {m : ℕ}
    {𝓖 : Hypergraph (Fin m)} [Fintype 𝓖] (hlin : 𝓖.IsLinear)
    (h : 401 / (β ^ 2 * σ) ≤ (m : ℝ)) (h2 : 20 / β ≤ (m : ℝ)) :
    (((bigFinset (β / 5) 𝓖).card : ℕ) : ℝ) < σ * (m : ℝ) / 2 := by
  have hα : (0 : ℝ) < β / 5 := by positivity
  have h4 : 4 ≤ (β / 5) * (m : ℝ) := by
    rw [div_le_iff₀ hβ0] at h2
    nlinarith [h2, hβ0]
  have hc := bigFinset_card_le (α₂ := β / 5) hlin hα h4
  have hcn : (((bigFinset (β / 5) 𝓖).card : ℕ) : ℝ) ≤ 200 / β ^ 2 := by
    have h5 : (8 : ℝ) / (β / 5) ^ 2 = 200 / β ^ 2 := by ring
    rwa [h5] at hc
  have hgoal : 200 / β ^ 2 < σ * (m : ℝ) / 2 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < β ^ 2)]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < β ^ 2 * σ)] at h
    nlinarith [h, hβ0, hσ0]
  linarith [hcn, hgoal]

/-- `1 ≤ (γ₂/3)n`. -/
theorem margin_gamma2n {γ₂ : ℝ} (hγ₂0 : 0 < γ₂) {m : ℕ}
    (h : 3 / γ₂ ≤ (m : ℝ)) : (1 : ℝ) ≤ (γ₂ / 3) * (m : ℝ) := by
  rw [div_le_iff₀ hγ₂0] at h
  nlinarith [h, hγ₂0]

/-- `2r₀ ≤ γ₂^{10}(1−δ)√n` for `n ≥ (4r₀/γ₂^{10})²` and `δ ≤ 1/2`, `1 ≤ r₀`. -/
theorem margin_r0h {γ₂ δ : ℝ} (hγ₂0 : 0 < γ₂) (hδ1 : δ ≤ 1 / 2)
    {r₀ m : ℕ} (hr₀ : 1 ≤ r₀) (h : (4 * (r₀ : ℝ) / γ₂ ^ 10) ^ 2 ≤ (m : ℝ)) :
    2 * (r₀ : ℝ) ≤ γ₂ ^ 10 * (1 - δ) * Real.sqrt (m : ℝ) := by
  have hr₁ : (1 : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hr₀
  have hpos8 : (0 : ℝ) < 4 * (r₀ : ℝ) / γ₂ ^ 10 := by
    apply div_pos _ (by positivity)
    linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by nlinarith [h, hpos8]
  have hspos : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm0
  have h2 : 4 * (r₀ : ℝ) / γ₂ ^ 10 ≤ Real.sqrt (m : ℝ) :=
    (Real.le_sqrt (le_of_lt hpos8) (le_of_lt hm0)).mpr h
  have hγ10 : (0 : ℝ) < γ₂ ^ 10 := by positivity
  have hδ' : (1 : ℝ) / 2 ≤ 1 - δ := by linarith
  have hstep1 : 2 * (r₀ : ℝ) ≤ γ₂ ^ 10 * (1 / 2) * Real.sqrt (m : ℝ) := by
    have h4 : γ₂ ^ 10 * (1 / 2) * (4 * (r₀ : ℝ) / γ₂ ^ 10) ≤
        γ₂ ^ 10 * (1 / 2) * Real.sqrt (m : ℝ) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h5 : γ₂ ^ 10 * (1 / 2) * (4 * (r₀ : ℝ) / γ₂ ^ 10) = 2 * (r₀ : ℝ) := by
      field_simp
      ring
    rwa [h5] at h4
  have hstep2 : γ₂ ^ 10 * (1 / 2) * Real.sqrt (m : ℝ) ≤
      γ₂ ^ 10 * (1 - δ) * Real.sqrt (m : ℝ) := by
    have h3 : γ₂ ^ 10 * (1 / 2) ≤ γ₂ ^ 10 * (1 - δ) :=
      mul_le_mul_of_nonneg_left hδ' (le_of_lt hγ10)
    have := mul_le_mul_of_nonneg_right h3 (le_of_lt hspos)
    linarith [this]
  linarith [hstep1, hstep2]


/-- `#bigFinset (γ₁/2) 𝓖 = ∅` when all edges of `𝓖` are non-huge and `β ≤ γ₁`. -/
theorem bigFinset_eq_empty_of_nonHuge {β γ₁ : ℝ} (hβ0 : 0 < β) (hβγ₁ : β ≤ γ₁) {m : ℕ}
    {𝓖 : Hypergraph (Fin m)} [Fintype 𝓖]
    (hsub : ∀ e : 𝓖, (edgeSize (e : Set (Fin m)) : ℝ) < β * (m : ℝ) / 4) :
    bigFinset (γ₁ / 2) 𝓖 = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro e he
  have h1 := (mem_bigFinset (γ₁ / 2) 𝓖 e).mp he
  have h2 := hsub e
  have h3 : (γ₁ / 2 / 2) * (m : ℝ) = γ₁ * (m : ℝ) / 4 := by ring
  have h4 : β * (m : ℝ) / 4 ≤ γ₁ * (m : ℝ) / 4 := by
    have := mul_le_mul_of_nonneg_right hβγ₁ (Nat.cast_nonneg m)
    linarith [this]
  rw [h3] at h1
  linarith [h1, h2, h4]

/-- `8/σ² ≤ (1−3σ)n` for `σ ≤ 1/6` and `n ≥ 16/σ²`. -/
theorem margin_bigcase {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 6) {m : ℕ}
    (h : 16 / σ ^ 2 ≤ (m : ℝ)) : 8 / σ ^ 2 ≤ (1 - 3 * σ) * (m : ℝ) := by
  have h' : (16 : ℝ) ≤ σ ^ 2 * (m : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < σ ^ 2)] at h
    linarith [h]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < σ ^ 2)]
  nlinarith [h', hσ0, hσ1]

/-- `32/β² ≤ σn` for `n ≥ 32/(β²σ)`. -/
theorem margin_sigma_n {β σ : ℝ} (hβ0 : 0 < β) (hσ0 : 0 < σ) {m : ℕ}
    (h : 32 / (β ^ 2 * σ) ≤ (m : ℝ)) : 32 / β ^ 2 ≤ σ * (m : ℝ) := by
  have h' : (32 : ℝ) ≤ β ^ 2 * σ * (m : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < β ^ 2 * σ)] at h
    linarith [h]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < β ^ 2)]
  nlinarith [h']

/-- `8 ≤ βn` for `n ≥ 8/β`. -/
theorem margin_beta_n {β : ℝ} (hβ0 : 0 < β) {m : ℕ} (h : 8 / β ≤ (m : ℝ)) :
    (8 : ℝ) ≤ β * (m : ℝ) := by
  rw [div_le_iff₀ hβ0] at h
  linarith [h]

/-- `2 ≤ (β/5)n` for `n ≥ 10/β`. -/
theorem margin_two_beta5 {β : ℝ} (hβ0 : 0 < β) {m : ℕ} (h : 10 / β ≤ (m : ℝ)) :
    (2 : ℝ) ≤ (β / 5) * (m : ℝ) := by
  rw [div_le_iff₀ hβ0] at h
  nlinarith [h]

/-- `r₀ < βn/4` for `n ≥ 4(r₀+1)/β`. -/
theorem margin_r0_lt {β : ℝ} (hβ0 : 0 < β) {r₀ m : ℕ}
    (h : 4 * ((r₀ : ℝ) + 1) / β ≤ (m : ℝ)) : (r₀ : ℝ) < β * (m : ℝ) / 4 := by
  rw [div_le_iff₀ hβ0] at h
  nlinarith [h]

/-- `(γ₂/3)n + 32/β² ≤ (1−2σ)n` for small `γ₂, σ` and large `n`. -/
theorem margin_gamma_m {β γ₂ σ : ℝ} (hβ0 : 0 < β) (hσ0 : 0 < σ) (hγ₂ : γ₂ ≤ 3 / 4)
    (hσ1 : σ ≤ 1 / 8) {m : ℕ} (h : 64 / β ^ 2 ≤ (m : ℝ)) :
    (γ₂ / 3) * (m : ℝ) + 32 / β ^ 2 ≤ (1 - 2 * σ) * (m : ℝ) := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h' : 32 / β ^ 2 ≤ (m : ℝ) / 2 := by
    have h2 := div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)
    have h3 : (64 / β ^ 2) / 2 = 32 / β ^ 2 := by ring
    rwa [h3] at h2
  have h4 : (γ₂ / 3) * (m : ℝ) ≤ (m : ℝ) / 4 := by nlinarith [hγ₂, hm]
  have h5 : (1 : ℝ) - 2 * σ ≥ 3 / 4 := by linarith
  have h6 : (3 / 4) * (m : ℝ) ≤ (1 - 2 * σ) * (m : ℝ) :=
    mul_le_mul_of_nonneg_right h5 hm
  linarith [h', h4, h6]

/-- `32/β² + 2γ₂n/3 ≤ (1−2σ)n` for small `γ₂, σ` and large `n`. -/
theorem margin_A2 {β γ₂ σ : ℝ} (hβ0 : 0 < β) (hσ0 : 0 < σ) (hγ₂ : γ₂ ≤ 3 / 8)
    (hσ1 : σ ≤ 1 / 8) {m : ℕ} (h : 128 / β ^ 2 ≤ (m : ℝ)) :
    32 / β ^ 2 + 2 * γ₂ * (m : ℝ) / 3 ≤ (1 - 2 * σ) * (m : ℝ) := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h' : 32 / β ^ 2 ≤ (m : ℝ) / 2 := by
    have h2 := div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2)
    have h3 : (128 / β ^ 2) / 2 = 64 / β ^ 2 := by ring
    rw [h3] at h2
    have h4 : 32 / β ^ 2 ≤ 64 / β ^ 2 := by
      have hb : (0 : ℝ) < β ^ 2 := by positivity
      rw [div_le_div_iff₀ hb hb]
      nlinarith [hb]
    linarith [h2, h4]
  have h5 : 2 * γ₂ * (m : ℝ) / 3 ≤ (m : ℝ) / 4 := by nlinarith [hγ₂, hm]
  have h6 : (1 : ℝ) - 2 * σ ≥ 3 / 4 := by linarith
  have h7 : (3 / 4) * (m : ℝ) ≤ (1 - 2 * σ) * (m : ℝ) :=
    mul_le_mul_of_nonneg_right h6 hm
  linarith [h', h5, h7]

/-- `1 + 32/β² ≤ (σ/4)n` for `n ≥ 512/(β²σ)`. -/
theorem margin_slack {β σ : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hσ0 : 0 < σ) {m : ℕ}
    (h : 512 / (β ^ 2 * σ) ≤ (m : ℝ)) :
    (1 : ℝ) + 32 / β ^ 2 ≤ (σ / 4) * (m : ℝ) := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h' : (512 : ℝ) ≤ β ^ 2 * σ * (m : ℝ) := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < β ^ 2 * σ)] at h
    linarith [h]
  have hL : (1 : ℝ) + 32 / β ^ 2 = (β ^ 2 + 32) / β ^ 2 := by field_simp
  rw [hL, div_le_iff₀ (by positivity : (0 : ℝ) < β ^ 2)]
  have hb1 : β ^ 2 ≤ 1 := by nlinarith [hβ0, hβ1]
  nlinarith [h', hσ0, hβ0, hb1]

/-- `⌈(1−ζ/1000)n⌉₊ ≤ (univ ∖ Cmed).card` for the Case-2.1 colour set. -/
theorem margin_room1 {γ₁ : ℝ} (hγ₁0 : 0 < γ₁) (hγ₁ : γ₁ ≤ 1 / 40000) {n : ℕ}
    (Cmed : Finset (Fin n)) (hC : (Cmed.card : ℝ) ≤ γ₁ * (n : ℝ)) (hn : 1000000 ≤ n) :
    ⌈(3997 / 4000 : ℝ) * (n : ℝ)⌉₊ ≤ (Finset.univ \ Cmed).card := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnR : (1000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (↑(⌈(3997 / 4000 : ℝ) * (n : ℝ)⌉₊) : ℝ) < (3997 / 4000 : ℝ) * (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h3 : γ₁ * (n : ℝ) ≤ (1 / 40000) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hγ₁ hn0
  have h2 : (↑(⌈(3997 / 4000 : ℝ) * (n : ℝ)⌉₊) : ℝ) + (Cmed.card : ℝ) ≤ (n : ℝ) := by
    nlinarith [h1, hC, h3, hnR]
  have h5 : ⌈(3997 / 4000 : ℝ) * (n : ℝ)⌉₊ + Cmed.card ≤ n := by exact_mod_cast h2
  have h6 : (Finset.univ \ Cmed).card = n - Cmed.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  rw [h6]
  omega

/-- `⌈(1−ζ/1000)n⌉₊ + ⌈n/1500⌉₊ ≤ (univ ∖ Cmed).card`. -/
theorem margin_room2 {γ₁ : ℝ} (hγ₁0 : 0 < γ₁) (hγ₁ : γ₁ ≤ 1 / 40000) {n : ℕ}
    (Cmed : Finset (Fin n)) (hC : (Cmed.card : ℝ) ≤ γ₁ * (n : ℝ)) (hn : 1000000 ≤ n) :
    ⌈(3997 / 4000 : ℝ) * (n : ℝ)⌉₊ + ⌈(1 / 1500 : ℝ) * (n : ℝ)⌉₊ ≤
      (Finset.univ \ Cmed).card := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnR : (1000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (↑(⌈(3997 / 4000 : ℝ) * (n : ℝ)⌉₊) : ℝ) < (3997 / 4000 : ℝ) * (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h1' : (↑(⌈(1 / 1500 : ℝ) * (n : ℝ)⌉₊) : ℝ) < (1 / 1500 : ℝ) * (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h3 : γ₁ * (n : ℝ) ≤ (1 / 40000) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hγ₁ hn0
  have h2 : (↑(⌈(3997 / 4000 : ℝ) * (n : ℝ)⌉₊) : ℝ) +
      (↑(⌈(1 / 1500 : ℝ) * (n : ℝ)⌉₊) : ℝ) + (Cmed.card : ℝ) ≤ (n : ℝ) := by
    nlinarith [h1, h1', hC, h3, hnR]
  have h5 : ⌈(3997 / 4000 : ℝ) * (n : ℝ)⌉₊ + ⌈(1 / 1500 : ℝ) * (n : ℝ)⌉₊ + Cmed.card ≤ n := by
    exact_mod_cast h2
  have h6 : (Finset.univ \ Cmed).card = n - Cmed.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
  rw [h6]
  omega

/-- `⌈(1−ζ/1000)n⌉₊ + ⌈n/1500⌉₊ ≤ (1−2σ)n`. -/
theorem margin_budget0 {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 100000) {n : ℕ}
    (hn : 1000000 ≤ n) :
    ⌈(3997 / 4000 : ℝ) * (n : ℝ)⌉₊ + ⌈(1 / 1500 : ℝ) * (n : ℝ)⌉₊ ≤ (1 - 2 * σ) * (n : ℝ) := by
  have hnR : (1000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (↑(⌈(3997 / 4000 : ℝ) * (n : ℝ)⌉₊) : ℝ) < (3997 / 4000 : ℝ) * (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h1' : (↑(⌈(1 / 1500 : ℝ) * (n : ℝ)⌉₊) : ℝ) < (1 / 1500 : ℝ) * (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h2 : (↑(⌈(3997 / 4000 : ℝ) * (n : ℝ)⌉₊) : ℝ) +
      (↑(⌈(1 / 1500 : ℝ) * (n : ℝ)⌉₊) : ℝ) ≤ (1 - 2 * σ) * (n : ℝ) := by
    nlinarith [h1, h1', hnR, hσ1]
  exact_mod_cast h2

/-- `⌊(1−3σ/2)n⌋₊ + Cmed.card ≤ n`. -/
theorem margin_Kroom {σ γ₁ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2) (hγ₁0 : 0 < γ₁)
    (hγ₁σ : γ₁ ≤ 3 * σ / 2)
    {n : ℕ} (Cmed : Finset (Fin n)) (hC : (Cmed.card : ℝ) ≤ γ₁ * (n : ℝ)) :
    ⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊ + Cmed.card ≤ n := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h0 : (0 : ℝ) ≤ 1 - 3 * σ / 2 := by linarith
  have h1 : (↑(⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊) : ℝ) ≤ (1 - 3 * σ / 2) * (n : ℝ) :=
    Nat.floor_le (by positivity)
  have h2 : γ₁ * (n : ℝ) ≤ (3 * σ / 2) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hγ₁σ hn0
  have h3 : (↑(⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊) : ℝ) + (Cmed.card : ℝ) ≤ (n : ℝ) := by
    nlinarith [h1, hC, h2]
  exact_mod_cast h3

/-- `⌈(1−ζ/1000)n⌉₊ + ⌈n/1500⌉₊ ≤ ⌊(1−3σ/2)n⌋₊`. -/
theorem margin_C1K {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 100000) {n : ℕ}
    (hn : 1000000 ≤ n) :
    ⌈(3997 / 4000 : ℝ) * (n : ℝ)⌉₊ + ⌈(1 / 1500 : ℝ) * (n : ℝ)⌉₊ ≤
      ⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊ := by
  have hnR : (1000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (↑(⌈(3997 / 4000 : ℝ) * (n : ℝ)⌉₊) : ℝ) < (3997 / 4000 : ℝ) * (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h1' : (↑(⌈(1 / 1500 : ℝ) * (n : ℝ)⌉₊) : ℝ) < (1 / 1500 : ℝ) * (n : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h2 : (1 - 3 * σ / 2) * (n : ℝ) - 1 <
      (↑(⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊) : ℝ) := by
    have h2' := Nat.lt_floor_add_one ((1 - 3 * σ / 2) * (n : ℝ))
    linarith [h2']
  have h3 : (↑(⌈(3997 / 4000 : ℝ) * (n : ℝ)⌉₊) : ℝ) +
      (↑(⌈(1 / 1500 : ℝ) * (n : ℝ)⌉₊) : ℝ) ≤ (1 - 3 * σ / 2) * (n : ℝ) - 1 := by
    nlinarith [h1, h1', hnR, hσ1]
  have h4 : (↑(⌈(3997 / 4000 : ℝ) * (n : ℝ)⌉₊) : ℝ) +
      (↑(⌈(1 / 1500 : ℝ) * (n : ℝ)⌉₊) : ℝ) <
      (↑(⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊) : ℝ) := by linarith [h2, h3]
  have h5 : ⌈(3997 / 4000 : ℝ) * (n : ℝ)⌉₊ + ⌈(1 / 1500 : ℝ) * (n : ℝ)⌉₊ <
      ⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊ := by exact_mod_cast h4
  omega

/-- **The medium-edge colouring** (Proposition 6.10 with Kahn's theorem as
input).  The medium edges `r₁ < |e| ≤ r₀` of a linear hypergraph admit a
`γ₁`-bounded colouring using at most `γ₁n` colours, provided Kahn's theorem
applies with threshold `D₀ ≤ n/(r₁−1)`. -/
theorem medEdges_colouring_of_kahn {r₁ r₀ : ℕ} {γ₁ D₀ : ℝ}
    (hK : ∀ D : ℝ, D₀ ≤ D → ∀ (m : ℕ) (𝓖 : Hypergraph (Fin m)), 𝓖.IsLinear →
      ((hypergraphMaxDegree 𝓖 : ℕ) : ℝ) ≤ D →
      (∀ e : 𝓖, (edgeSize (e : Set (Fin m)) : ℝ) ≤ (r₀ : ℝ)) →
      ∀ c : ℕ, 2 * D ≤ (c : ℝ) → 𝓖.Colorable c)
    (hγ₁0 : 0 < γ₁) (hγ₁1 : γ₁ ≤ 1 / 2) (h2n : 2 ≤ n) (hr₁ : 2 ≤ r₁)
    (hr₁big : 32 / γ₁ ^ 3 + 8 / γ₁ ^ 2 + 8 / γ₁ ≤ (r₁ : ℝ))
    (hγ₁n : 2 ≤ γ₁ * (n : ℝ))
    {𝓗 : Hypergraph (Fin n)} (hlin : 𝓗.IsLinear)
    (hsize₁ : ∀ e ∈ 𝓗, r₁ ≤ edgeSize e)
    (hsize₀ : ∀ e : 𝓗.medEdges r₁ r₀, edgeSize (e : Set (Fin n)) ≤ r₀)
    (hD : D₀ ≤ (n : ℝ) / ((r₁ : ℝ) - 1)) :
    ∃ (C : Finset (Fin n)) (φ : (𝓗.medEdges r₁ r₀).Coloring (Fin n)),
      φ.UsesColourSet C ∧ (C.card : ℝ) ≤ γ₁ * (n : ℝ) ∧ φ.AlphaBounded γ₁ := by
  classical
  have hr₁1 : (2 : ℝ) ≤ (r₁ : ℝ) := by exact_mod_cast hr₁
  have hr₁pos : (0 : ℝ) < (r₁ : ℝ) := by linarith
  have hDpos : (0 : ℝ) < (r₁ : ℝ) - 1 := by linarith
  have hmedsub : 𝓗.medEdges r₁ r₀ ⊆ 𝓗 := medEdges_subset 𝓗 r₁ r₀
  have hlinmed : (𝓗.medEdges r₁ r₀).IsLinear := hlin.mono hmedsub
  have hsize₁' : ∀ e ∈ 𝓗.medEdges r₁ r₀, r₁ ≤ edgeSize e :=
    fun e he => hsize₁ e (hmedsub he)
  have hΔ : ((hypergraphMaxDegree (𝓗.medEdges r₁ r₀) : ℕ) : ℝ) ≤
      (n : ℝ) / ((r₁ : ℝ) - 1) :=
    maxDegree_le_div hlinmed hr₁ hsize₁'
  set c : ℕ := Nat.ceil (2 * (n : ℝ) / ((r₁ : ℝ) - 1)) with hc
  have h2D : 2 * ((n : ℝ) / ((r₁ : ℝ) - 1)) ≤ (c : ℝ) := by
    rw [hc]
    have h := Nat.le_ceil (2 * (n : ℝ) / ((r₁ : ℝ) - 1))
    have heq : 2 * (n : ℝ) / ((r₁ : ℝ) - 1) = 2 * ((n : ℝ) / ((r₁ : ℝ) - 1)) := by ring
    linarith [h, heq.le]
  have hsize₀' : ∀ e : 𝓗.medEdges r₁ r₀, (edgeSize (e : Set (Fin n)) : ℝ) ≤ (r₀ : ℝ) :=
    fun e => by exact_mod_cast hsize₀ e
  have hcol : (𝓗.medEdges r₁ r₀).Colorable c :=
    hK ((n : ℝ) / ((r₁ : ℝ) - 1)) hD n (𝓗.medEdges r₁ r₀) hlinmed hΔ hsize₀' c h2D
  have hc4 : (c : ℝ) ≤ 4 * (n : ℝ) / (r₁ : ℝ) + 1 := by
    rw [hc]
    have h1 : (↑(Nat.ceil (2 * (n : ℝ) / ((r₁ : ℝ) - 1))) : ℝ) <
        2 * (n : ℝ) / ((r₁ : ℝ) - 1) + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : 2 * (n : ℝ) / ((r₁ : ℝ) - 1) ≤ 4 * (n : ℝ) / (r₁ : ℝ) := by
      rw [div_le_div_iff₀ hDpos hr₁pos]
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)), hr₁1]
    linarith [h1, h2]
  exact medEdges_colouring_of_chi (𝓗 := 𝓗.medEdges r₁ r₀) hγ₁0 hγ₁1 h2n hr₁ hr₁big hγ₁n
    hlinmed hsize₁' ⟨c, hc4, hcol⟩

/-- The Case-2.1 parameter `ζ` of the hierarchy (`= 3/4`). -/
def ζc : ℝ := 3 / 4

/-- The `γ₁`-threshold of the hierarchy. -/
def γ₁Thr (σ : ℝ) : ℝ := σ ^ 5 / 10 ^ 20

/-- The `β`-threshold of the hierarchy. -/
def βThr (γ₁ : ℝ) : ℝ := γ₁ ^ 5 / 10 ^ 20

/-- The `n`-threshold of the hierarchy: large enough for every `n`-margin. -/
def N₀Thr (r₀ : ℕ) (β γ₂ σ δ : ℝ) : ℕ :=
  ⌈8 / δ ^ 2⌉₊ + ⌈16 / δ ^ 2⌉₊ + ⌈16 / β ^ 2⌉₊ + ⌈64 / β ^ 2⌉₊ + 4
  + ⌈3 / γ₂⌉₊ + ⌈20 / β⌉₊ + ⌈10 / β⌉₊ + ⌈8 / β⌉₊ + ⌈128 / β ^ 2⌉₊
  + ⌈(4 * (r₀ : ℝ) / γ₂ ^ 10) ^ 2⌉₊ + ⌈4 * ((r₀ : ℝ) + 1) / β⌉₊
  + ⌈32 / (β ^ 2 * σ)⌉₊ + ⌈512 / (β ^ 2 * σ)⌉₊ + ⌈401 / (β ^ 2 * σ)⌉₊
  + ⌈802 / (β ^ 2 * σ)⌉₊ + ⌈1604 / (β ^ 2 * σ)⌉₊ + ⌈2406000 / β ^ 2⌉₊
  + ⌈16 / σ ^ 2⌉₊ + 1000000

/-- `c ≤ m` from `⌈c⌉₊ ≤ N ≤ m`. -/
theorem ceil_le_of_le {c : ℝ} {N m : ℕ} (hN : Nat.ceil c ≤ N) (hm : N ≤ m) :
    c ≤ (m : ℝ) :=
  le_trans (Nat.le_ceil c) (by exact_mod_cast le_trans hN hm)


/-- `LargeEdgeExtremal` is monotone in `γ₂`. -/
theorem LargeEdgeExtremal_mono_γ₂ {n : ℕ} {δ γ₂ γ₂' γ₁ β r₁ r₀ : ℝ} {𝓗 : Hypergraph (Fin n)}
    (h : γ₂' ≤ γ₂) (hE : LargeEdgeExtremal n δ γ₂' γ₁ β r₁ r₀ 𝓗) :
    LargeEdgeExtremal n δ γ₂ γ₁ β r₁ r₀ 𝓗 := by
  obtain ⟨⟨W, hW1, hW2, hW3⟩, φ, Cmed, hC, hmed, hcls, hhuge, hother⟩ := hE
  exact ⟨⟨W, hW1, hW2, hW3⟩, φ, Cmed, le_trans hC (by
    have := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg n); linarith), hmed, hcls, hhuge, hother⟩

/-- `σThr δ ≤ δ` for `δ ≤ 1`. -/
theorem σThr_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : σThr δ ≤ δ := by
  have h := pow_le_pow_of_le_one (le_of_lt hδ0) hδ1 (n := 12) (m := 1) (by norm_num)
  have h10 : (1 : ℝ) ≤ 10 ^ 6 := by norm_num
  simp only [σThr]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 6)]
  nlinarith [h, hδ0]

/-- `γ₁Thr σ ≤ σ` for `σ ≤ 1`. -/
theorem γ₁Thr_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) : γ₁Thr σ ≤ σ := by
  have h := pow_le_pow_of_le_one (le_of_lt hσ0) hσ1 (n := 5) (m := 1) (by norm_num)
  simp only [γ₁Thr]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 20)]
  nlinarith [h, hσ0]

/-- `βThr γ₁ ≤ γ₁` for `γ₁ ≤ 1`. -/
theorem βThr_le {γ₁ : ℝ} (h0 : 0 < γ₁) (h1 : γ₁ ≤ 1) : βThr γ₁ ≤ γ₁ := by
  have h := pow_le_pow_of_le_one (le_of_lt h0) h1 (n := 5) (m := 1) (by norm_num)
  simp only [βThr]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 20)]
  nlinarith [h, h0]

/-- `N₀Thr` is positive. -/
theorem N₀Thr_pos (r₀ : ℕ) (β γ₂ σ δ : ℝ) : 0 < N₀Thr r₀ β γ₂ σ δ := by
  simp only [N₀Thr]; omega




/-- The `r₀`-threshold of the hierarchy: large enough for the Case-2.1 and
Case-2.2 ratio margins in `r₀`. -/
def R₀Thr (σ β : ℝ) : ℕ :=
  ⌈1000 / (σ * β)⌉₊ + ⌈280001 / β ^ 2⌉₊ + ⌈1000001 / β⌉₊ + 10

/-- The `r₁`-threshold of the hierarchy: large enough for the two Reordering
Lemma applications and the `r₁`-margins. -/
def R₁Thr (γ₂' γ₁ : ℝ) (Rapp : ℕ) : ℕ :=
  ⌈4 * (1 / (2 * γ₂')) ^ 20⌉₊ + Rapp + ⌈100 / (γ₂' * γ₁)⌉₊ + 10 ^ 8 + 10
  + ⌈32 / γ₁ ^ 3 + 8 / γ₁ ^ 2 + 8 / γ₁⌉₊

theorem R₀Thr_pos (σ β : ℝ) : 0 < R₀Thr σ β := by simp only [R₀Thr]; omega

theorem R₁Thr_pos (γ₂' γ₁ : ℝ) (Rapp : ℕ) : 0 < R₁Thr γ₂' γ₁ Rapp := by
  simp only [R₁Thr]; omega

/-- The empty hypergraph has the (trivial) non-extremal colouring. -/
theorem largeEdgeNonExtremal_empty {n : ℕ} {σ γ₁ β r₁ r₀ : ℝ} (hσ1 : σ ≤ 1)
    (hγ₁0 : 0 ≤ γ₁) (hβ0 : 0 ≤ β) :
    LargeEdgeNonExtremal n σ γ₁ β r₁ r₀ (∅ : Hypergraph (Fin n)) := by
  classical
  haveI : IsEmpty (↥(∅ : Set (Set (Fin n)))) := ⟨fun x => x.2⟩
  let φ : (∅ : Hypergraph (Fin n)).Coloring (Fin n) :=
    ⟨fun e => isEmptyElim e, fun e _ _ _ => isEmptyElim e⟩
  refine ⟨φ, ∅, ∅, ?_, ?_, Finset.Subset.refl _, ?_, ?_, ?_, ?_, ?_⟩
  · intro e; exact isEmptyElim e
  · rw [Finset.card_empty]
    push_cast
    nlinarith [hσ1, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  · rw [Finset.card_empty]
    push_cast
    nlinarith [hγ₁0, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  · intro e; exact isEmptyElim e
  · intro c hc; exact absurd hc (Finset.notMem_empty c)
  · intro c hc
    obtain ⟨e, -, -⟩ := hc
    exact isEmptyElim e
  · intro c _ _
    have hc : φ.colorClass c = ∅ := by
      ext e
      exact ⟨fun h => isEmptyElim e, fun h => absurd h (Set.notMem_empty e)⟩
    rw [classVertexCount_eq_zero_of_classVertices_eq_empty φ
      (classVertices_eq_empty_of_colorClass_eq_empty φ hc)]
    push_cast
    nlinarith [hβ0, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]

/-- `2n/((β/5)(r₀−1)) < σn/4` for `r₀ ≥ 1000/(σβ)`. -/
theorem margin_m22₂ {σ β : ℝ} (hσ0 : 0 < σ) (hβ0 : 0 < β) (hσβ : σ * β ≤ 1)
    {r₀ n : ℕ} (h : 1000 / (σ * β) ≤ (r₀ : ℝ)) (hn0 : 0 < n) :
    2 * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < σ * (n : ℝ) / 4 := by
  have hn0' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hσβpos : (0 : ℝ) < σ * β := mul_pos hσ0 hβ0
  have hr₀ : 1000 ≤ σ * β * (r₀ : ℝ) := by
    rw [div_le_iff₀ hσβpos] at h
    linarith [h]
  have hden : (0 : ℝ) < (β / 5) * ((r₀ : ℝ) - 1) := by
    have h1 : (1 : ℝ) < (r₀ : ℝ) := by
      have h2 : (1000 : ℝ) ≤ (r₀ : ℝ) := by nlinarith [hr₀, hσβ, (Nat.cast_nonneg r₀ : (0:ℝ) ≤ (r₀:ℝ))]
      linarith
    have h2 : (0 : ℝ) < β / 5 := by positivity
    nlinarith [h1, h2]
  rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)]
  have hkey : 160 < σ * β * ((r₀ : ℝ) - 1) := by
    have h2 : σ * β * (r₀ : ℝ) - σ * β ≥ 1000 - 1 := by linarith [hr₀, hσβ]
    nlinarith [h2]
  have h5 : (β / 5) * ((r₀ : ℝ) - 1) * 5 = β * ((r₀ : ℝ) - 1) := by ring
  have h6 : (1 : ℝ) < (r₀ : ℝ) := by
    have h2 : (1000 : ℝ) ≤ (r₀ : ℝ) := by nlinarith [hr₀, hσβ, (Nat.cast_nonneg r₀ : (0:ℝ) ≤ (r₀:ℝ))]
    linarith
  nlinarith [hkey, hn0', hβ0, h5, h6]

/-- `2n/((β/5)r₀) < ((σ/2)n)/4` for `r₀ ≥ 1000/(σβ)`. -/
theorem margin_margin {σ β : ℝ} (hσ0 : 0 < σ) (hβ0 : 0 < β) (hσβ : σ * β ≤ 1)
    {r₀ n : ℕ} (h : 1000 / (σ * β) ≤ (r₀ : ℝ)) (hn0 : 0 < n) :
    2 * (n : ℝ) / ((β / 5) * (r₀ : ℝ)) < ((σ / 2) * (n : ℝ)) / 4 := by
  have hn0' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hσβpos : (0 : ℝ) < σ * β := mul_pos hσ0 hβ0
  have hr₀ : 1000 ≤ σ * β * (r₀ : ℝ) := by
    rw [div_le_iff₀ hσβpos] at h
    linarith [h]
  have hden : (0 : ℝ) < (β / 5) * (r₀ : ℝ) := by
    have h1 : (0 : ℝ) < β / 5 := by positivity
    have h2 : (0 : ℝ) < (r₀ : ℝ) := by
      have h3 : (1000 : ℝ) ≤ (r₀ : ℝ) := by nlinarith [hr₀, hσβ, (Nat.cast_nonneg r₀ : (0:ℝ) ≤ (r₀:ℝ))]
      linarith
    positivity
  rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)]
  have h5 : (β / 5) * (r₀ : ℝ) * 5 = β * (r₀ : ℝ) := by ring
  nlinarith [hr₀, hn0', hβ0, h5]

/-- `2n/((β/5)(r₀−1)) < ((1/6000)n)/4` for `r₀ ≥ 1000001/β`. -/
theorem margin_69m {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) {r₀ n : ℕ}
    (h : 1000001 / β ≤ (r₀ : ℝ)) (hn0 : 0 < n) :
    2 * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < ((1 / 6000 : ℝ) * (n : ℝ)) / 4 := by
  have hn0' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hr₀ : 1000001 ≤ β * (r₀ : ℝ) := by
    rw [div_le_iff₀ hβ0] at h
    linarith [h]
  have hr₀ge : (1000001 : ℝ) ≤ (r₀ : ℝ) := by
    nlinarith [hr₀, hβ0, hβ1, (Nat.cast_nonneg r₀ : (0 : ℝ) ≤ (r₀ : ℝ))]
  have hden : (0 : ℝ) < (β / 5) * ((r₀ : ℝ) - 1) := by
    have h2 : (0 : ℝ) < β / 5 := by positivity
    nlinarith [hr₀ge, h2]
  rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)]
  have h7 : (960000 : ℝ) ≤ β * ((r₀ : ℝ) - 1) := by
    have h8 : β * ((r₀ : ℝ) - 1) = β * (r₀ : ℝ) - β := by ring
    nlinarith [hr₀, hβ0, hβ1, h8]
  have heq : (1 / 6000 : ℝ) * (n : ℝ) * ((β / 5) * ((r₀ : ℝ) - 1)) =
      (n : ℝ) * (β * ((r₀ : ℝ) - 1)) / 30000 := by ring
  rw [heq]
  have h9 : (n : ℝ) * (960000 : ℝ) / 30000 ≤ (n : ℝ) * (β * ((r₀ : ℝ) - 1)) / 30000 := by
    have h10 := mul_le_mul_of_nonneg_left h7 (le_of_lt hn0')
    linarith [h10]
  have h11 : 2 * (n : ℝ) * 4 < (n : ℝ) * (960000 : ℝ) / 30000 := by
    rw [show (n : ℝ) * (960000 : ℝ) / 30000 = 32 * (n : ℝ) by ring]
    linarith [hn0']
  linarith [h9, h11]

/-- `2n/((β/5)(r₀−1)) < ((σ/4)n)/4` for `r₀ ≥ 1000/(σβ)`. -/
theorem margin_69mσ {σ β : ℝ} (hσ0 : 0 < σ) (hβ0 : 0 < β) (hσβ : σ * β ≤ 1)
    {r₀ n : ℕ} (h : 1000 / (σ * β) ≤ (r₀ : ℝ)) (hn0 : 0 < n) :
    2 * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < ((σ / 4) * (n : ℝ)) / 4 := by
  have hn0' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hσβpos : (0 : ℝ) < σ * β := mul_pos hσ0 hβ0
  have hr₀ : 1000 ≤ σ * β * (r₀ : ℝ) := by
    rw [div_le_iff₀ hσβpos] at h
    linarith [h]
  have hden : (0 : ℝ) < (β / 5) * ((r₀ : ℝ) - 1) := by
    have h1 : (1 : ℝ) < (r₀ : ℝ) := by
      have h2 : (1000 : ℝ) ≤ (r₀ : ℝ) := by nlinarith [hr₀, hσβ, (Nat.cast_nonneg r₀ : (0:ℝ) ≤ (r₀:ℝ))]
      linarith
    have h2 : (0 : ℝ) < β / 5 := by positivity
    nlinarith [h1, h2]
  rw [div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)]
  have h5 : (β / 5) * ((r₀ : ℝ) - 1) * 5 = β * ((r₀ : ℝ) - 1) := by ring
  have h6 : (0 : ℝ) < (r₀ : ℝ) - 1 := by
    have h2 : (1000 : ℝ) ≤ (r₀ : ℝ) := by nlinarith [hr₀, hσβ, (Nat.cast_nonneg r₀ : (0:ℝ) ≤ (r₀:ℝ))]
    linarith
  have h7 : 640 < σ * β * ((r₀ : ℝ) - 1) := by nlinarith [hr₀, hσβ, h6]
  nlinarith [h7, hn0', hβ0, h5]

/-- The `ζ`-margin `(2/((β/5)/2)+1)·(n/(((β/5)/2)r₀)) ≤ ζn/1000` at
`ζ = 3/4`, for `r₀ ≥ 280001/β²`. -/
theorem margin_marginA {β : ℝ} (hβ0 : 0 < β) (hβ1 : β ≤ 1) {r₀ n : ℕ}
    (h : 280001 / β ^ 2 ≤ (r₀ : ℝ)) (hn0 : 0 < n) :
    ((2 : ℝ) / ((β / 5) / 2) + 1) * ((n : ℝ) / (((β / 5) / 2 : ℝ) * (r₀ : ℝ))) ≤
      ζc * (n : ℝ) / 1000 := by
  have hn0' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hβ2 : (0 : ℝ) < β ^ 2 := by positivity
  have hr₀ : 280001 ≤ β ^ 2 * (r₀ : ℝ) := by
    rw [div_le_iff₀ hβ2] at h
    linarith [h]
  have hr₀pos : (0 : ℝ) < (r₀ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (r₀ : ℝ) := by
      nlinarith [hr₀, hβ1, hβ0, (Nat.cast_nonneg r₀ : (0 : ℝ) ≤ (r₀ : ℝ))]
    linarith
  have hkey : (2 / ((β / 5) / 2) + 1) * (1 / (((β / 5) / 2 : ℝ) * (r₀ : ℝ))) ≤
      ζc / 1000 := by
    have hb : (0 : ℝ) < β ^ 2 * (r₀ : ℝ) := mul_pos hβ2 hr₀pos
    have hL : (2 / ((β / 5) / 2) + 1) * (1 / (((β / 5) / 2 : ℝ) * (r₀ : ℝ))) =
        (200 + 10 * β) / (β ^ 2 * (r₀ : ℝ)) := by
      field_simp
      ring
    rw [hL, ζc, show (3 : ℝ) / 4 / 1000 = 3 / 4000 by norm_num]
    rw [div_le_div_iff₀ hb (by norm_num : (0 : ℝ) < 4000)]
    nlinarith [hr₀, hβ0, hβ1]
  have hL2 : ((2 : ℝ) / ((β / 5) / 2) + 1) *
        ((n : ℝ) / (((β / 5) / 2 : ℝ) * (r₀ : ℝ))) =
      ((2 / ((β / 5) / 2) + 1) * (1 / (((β / 5) / 2 : ℝ) * (r₀ : ℝ)))) * (n : ℝ) := by
    ring
  rw [hL2]
  calc ((2 / ((β / 5) / 2) + 1) * (1 / (((β / 5) / 2 : ℝ) * (r₀ : ℝ)))) * (n : ℝ)
      ≤ (ζc / 1000) * (n : ℝ) := mul_le_mul_of_nonneg_right hkey (le_of_lt hn0')
    _ = ζc * (n : ℝ) / 1000 := by ring




end

end ErdosFaberLovaszConjecture

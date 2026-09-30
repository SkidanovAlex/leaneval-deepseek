import Mathlib
import Submission.Work.BMF.vkford_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `W`-product bound of the Ford extraction

Ford, *Vinogradov's integral and bounds for the Riemann zeta function*, §5, (5.7)--(5.11):
under the hypothesis set `M₁ ≥ M₂ ≥ 100g`, `s ≤ 2^g`, `r ≥ 13g`, `r ≥ s` the product
`W_h ⋯ W_g` is at most `2^{O(g²)} M₂^{h+(h+1)+⋯+g} N^{-H}` with
`H = Σ_{j=h}^{g} min(j μ₂, j - λ, λ - j(1-μ₁-μ₂))` (`M_i = N^{μ_i}`, `t = N^λ`).

The saving `N^{-H}` is the point of the whole extraction: it is the *oscillation* of the phase
`t log n`, converted into a power saving of size `≍ λ²` in the exponent.
-/

namespace Work.BMF

open Finset
open scoped BigOperators

/-- Gauss sum in the shape used by Ford: `Σ_{j=h}^{g} j = (h+g)(g-h+1)/2`. -/
lemma sum_Icc_id_cast {h g : ℕ} (hhg : h ≤ g) :
    (∑ j ∈ Finset.Icc h g, (j : ℝ)) = ((h : ℝ) + (g : ℝ)) * ((g : ℝ) - (h : ℝ) + 1) / 2 := by
  induction g with
  | zero =>
      have h0 : h = 0 := by omega
      subst h0
      simp
  | succ g ih =>
      rcases lt_or_ge h (g + 1) with hlt | hge
      · have hhg' : h ≤ g := by omega
        rw [Finset.sum_Icc_succ_top (by omega) (fun j => (j : ℝ)), ih hhg']
        push_cast
        ring
      · have hh : h = g + 1 := by omega
        subst hh
        rw [Finset.sum_Icc_succ_top (by omega) (fun j => (j : ℝ))]
        rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
        push_cast
        ring

/-- **The per-factor bound** of the extraction: for `1 ≤ j ≤ g`,
`W_j ≤ 2^{g+3} · max(1, t M₂^j/N^j, N^j/(t M₁^j))`.

Ford's argument: `W_j = min(2sM₂^j, 2sM₂^j/(rM₁^j) + stM₂^j/(πjN^j) + 4πj(2N)^j/(rtM₁^j) + 2)`,
and using `s ≤ r`, `M₂ ≤ M₁`, `s ≤ 2^g`, `r ≥ 13g`, `t ≥ 1` the second branch is at most
`4 + stM₂^j/(πN^j) + 13g2^gN^j/(rtM₁^j) ≤ 2^{g+3} max(1, tM₂^j/N^j, N^j/(tM₁^j))`. -/
lemma fordW_le_max (r s t N M₁ M₂ : ℝ) (g j : ℕ)
    (hN : 0 < N) (ht : 1 ≤ t) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM12 : M₂ ≤ M₁) (hsr : s ≤ r) (hs1 : 1 ≤ s) (hs2 : s ≤ (2 : ℝ) ^ g)
    (hr : 13 * (g : ℝ) ≤ r) (hg1 : 1 ≤ g) (hj1 : 1 ≤ j) (hjg : j ≤ g) :
    fordW r s t N M₁ M₂ j ≤ (2 : ℝ) ^ (g + 3) * max 1 (max (t * M₂ ^ j / N ^ j) (N ^ j / (t * M₁ ^ j))) := by
  have hgr : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg1
  have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
  have hjr' : (j : ℝ) ≤ (g : ℝ) := by exact_mod_cast hjg
  have hrpos : 0 < r := by nlinarith
  have hM₂M₁ : M₂ ^ j ≤ M₁ ^ j := pow_le_pow_left₀ (le_of_lt hM₂) hM12 j
  have hNp : 0 < N ^ j := pow_pos hN j
  have hM₁p : 0 < M₁ ^ j := pow_pos hM₁ j
  have hM₂p : 0 < M₂ ^ j := pow_pos hM₂ j
  have h2Np : 0 < (2 * N) ^ j := pow_pos (by linarith) j
  set m : ℝ := max 1 (max (t * M₂ ^ j / N ^ j) (N ^ j / (t * M₁ ^ j))) with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hmt : t * M₂ ^ j / N ^ j ≤ m := le_trans (le_max_left _ _) (le_max_right _ _)
  have hmN : N ^ j / (t * M₁ ^ j) ≤ m := le_trans (le_max_right _ _) (le_max_right _ _)
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm1
  have h2g3 : (4 : ℝ) ≤ (2 : ℝ) ^ (g + 3) := by
    have h2 : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (g + 3) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at h2 ⊢
    linarith
  have h2g3' : (2 : ℝ) ^ (g + 1) ≤ (2 : ℝ) ^ (g + 3) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have key : fordW r s t N M₁ M₂ j ≤
      2 * s * M₂ ^ j / (r * M₁ ^ j) + s * t * M₂ ^ j / (Real.pi * (j:ℝ) * N ^ j)
        + 4 * Real.pi * (j:ℝ) * (2 * N) ^ j / (r * t * M₁ ^ j) + 2 := by
    rw [fordW]
    exact min_le_right _ _
  refine le_trans key ?_
  -- term 1 + 2 ≤ 4 ≤ 2^{g+1} ≤ 2^{g+3} m
  have h1 : 2 * s * M₂ ^ j / (r * M₁ ^ j) ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hM₂M₁, hM₂p, hsr, mul_le_mul_of_nonneg_left hsr (le_of_lt hM₂p), hs1]
  have h2 : s * t * M₂ ^ j / (Real.pi * (j:ℝ) * N ^ j) ≤ (2:ℝ) ^ (g+1) * m := by
    have hsj : s / (Real.pi * (j:ℝ)) ≤ (2:ℝ) ^ g := by
      have hpi : 1 ≤ Real.pi * (j:ℝ) := by nlinarith [Real.pi_gt_three, hjr]
      have : s / (Real.pi * (j:ℝ)) ≤ s := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [hs1]
      linarith [hs2]
    have : s * t * M₂ ^ j / (Real.pi * (j:ℝ) * N ^ j)
        = (s / (Real.pi * (j:ℝ))) * (t * M₂ ^ j / N ^ j) := by ring
    rw [this]
    have hnn : 0 ≤ s / (Real.pi * (j:ℝ)) := by positivity
    calc (s / (Real.pi * (j:ℝ))) * (t * M₂ ^ j / N ^ j)
        ≤ (2:ℝ) ^ g * (t * M₂ ^ j / N ^ j) := by
          exact mul_le_mul_of_nonneg_right hsj (by positivity)
      _ ≤ (2:ℝ) ^ g * m := by exact mul_le_mul_of_nonneg_left hmt (by positivity)
      _ ≤ (2:ℝ) ^ (g+1) * m := by
          have : (2:ℝ)^g ≤ (2:ℝ)^(g+1) := pow_le_pow_right₀ (by norm_num) (by omega)
          exact mul_le_mul_of_nonneg_right this (le_of_lt hmpos)
  have h3 : 4 * Real.pi * (j:ℝ) * (2 * N) ^ j / (r * t * M₁ ^ j) ≤ (2:ℝ) ^ (g+1) * m := by
    have h2g : (0:ℝ) < (2:ℝ) ^ g := pow_pos (by norm_num) g
    have hnum : 4 * Real.pi * (j:ℝ) * (2:ℝ) ^ j ≤ 16 * (g:ℝ) * (2:ℝ) ^ g := by
      have hA : 4 * Real.pi * (j:ℝ) ≤ 16 * (g:ℝ) := by
        nlinarith [Real.pi_lt_four, hjr', Real.pi_pos]
      have hB : (2:ℝ) ^ j ≤ (2:ℝ) ^ g := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2j : (0:ℝ) < (2:ℝ) ^ j := pow_pos (by norm_num) j
      calc 4 * Real.pi * (j:ℝ) * (2:ℝ) ^ j ≤ (16 * (g:ℝ)) * (2:ℝ) ^ j :=
            mul_le_mul_of_nonneg_right hA (le_of_lt h2j)
        _ ≤ (16 * (g:ℝ)) * (2:ℝ) ^ g :=
            mul_le_mul_of_nonneg_left hB (by positivity)
    have hcoef : 4 * Real.pi * (j:ℝ) * (2:ℝ) ^ j / r ≤ (2:ℝ) ^ (g+1) := by
      rw [div_le_iff₀ (by positivity)]
      have hdecomp : (2:ℝ) ^ (g+1) = 2 * (2:ℝ) ^ g := by rw [pow_succ']
      have hstep : 16 * (g:ℝ) * (2:ℝ) ^ g ≤ (2:ℝ) ^ (g+1) * (13 * (g:ℝ)) := by
        rw [hdecomp]; nlinarith [h2g, hgr]
      have hstep2 : (2:ℝ) ^ (g+1) * (13 * (g:ℝ)) ≤ (2:ℝ) ^ (g+1) * r :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      linarith [hnum, hstep, hstep2]
    have hfac : 4 * Real.pi * (j:ℝ) * (2 * N) ^ j / (r * t * M₁ ^ j)
        = (4 * Real.pi * (j:ℝ) * (2:ℝ) ^ j / r) * (N ^ j / (t * M₁ ^ j)) := by
      have hrne : r ≠ 0 := ne_of_gt hrpos
      have htne : t ≠ 0 := by linarith
      have hM₁ne : M₁ ^ j ≠ 0 := ne_of_gt hM₁p
      have hNne : N ^ j ≠ 0 := ne_of_gt hNp
      rw [mul_pow]
      field_simp
    rw [hfac]
    calc (4 * Real.pi * (j:ℝ) * (2:ℝ) ^ j / r) * (N ^ j / (t * M₁ ^ j))
        ≤ (2:ℝ) ^ (g+1) * (N ^ j / (t * M₁ ^ j)) :=
          mul_le_mul_of_nonneg_right hcoef (by positivity)
      _ ≤ (2:ℝ) ^ (g+1) * m := mul_le_mul_of_nonneg_left hmN (by positivity)
  have h2g1 : (4:ℝ) ≤ (2:ℝ) ^ (g+1) := by
    have h2 : (2 : ℝ) ^ 2 ≤ (2 : ℝ) ^ (g + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at h2 ⊢
    linarith
  have h12 : 2 * s * M₂ ^ j / (r * M₁ ^ j) + 2 ≤ (2:ℝ) ^ (g+1) * m := by
    have hmul : (2:ℝ)^(g+1) * 1 ≤ (2:ℝ)^(g+1) * m :=
      mul_le_mul_of_nonneg_left hm1 (by positivity)
    linarith [h1, h2g1, hmul]
  have h3sum : (2:ℝ) ^ (g+1) * m + (2:ℝ) ^ (g+1) * m + (2:ℝ) ^ (g+1) * m
      ≤ (2:ℝ) ^ (g+3) * m := by
    have hdecomp : (2:ℝ) ^ (g+3) = 4 * (2:ℝ) ^ (g+1) := by
      rw [show g + 3 = (g+1) + 2 by omega, pow_add]; ring
    nlinarith [hmpos, pow_pos (show (0:ℝ) < 2 by norm_num) (g+1)]
  linarith [h12, h2, h3, h3sum]

end Work.BMF

namespace Work.BMF

open Finset
open scoped BigOperators

/-- Product form of `fordW_le_max`. -/
lemma prod_fordW_le_max (h g : ℕ) (r s t N M₁ M₂ : ℝ)
    (hN : 0 < N) (ht : 1 ≤ t) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM12 : M₂ ≤ M₁) (hsr : s ≤ r) (hs1 : 1 ≤ s) (hs2 : s ≤ (2 : ℝ) ^ g)
    (hr : 13 * (g : ℝ) ≤ r) (hg1 : 1 ≤ g) (hh : 1 ≤ h) (hhg : h ≤ g) :
    ∏ j ∈ Finset.Icc h g, fordW r s t N M₁ M₂ j
      ≤ (2 : ℝ) ^ ((g + 3) * (g - h + 1))
          * ∏ j ∈ Finset.Icc h g, max 1 (max (t * M₂ ^ j / N ^ j) (N ^ j / (t * M₁ ^ j))) := by
  have hcard : (Finset.Icc h g).card = g - h + 1 := by rw [Nat.card_Icc]; omega
  have hgr : (1:ℝ) ≤ (g:ℝ) := by exact_mod_cast hg1
  have hrpos : 0 < r := by nlinarith
  have hnonneg : ∀ j ∈ Finset.Icc h g, 0 ≤ fordW r s t N M₁ M₂ j := by
    intro j hj
    rw [fordW]
    refine le_min ?_ ?_
    · positivity
    · have h1 : 0 ≤ 2 * s * M₂ ^ j / (r * M₁ ^ j) := by positivity
      have h2 : 0 ≤ s * t * M₂ ^ j / (Real.pi * (j:ℝ) * N ^ j) := by positivity
      have h3 : 0 ≤ 4 * Real.pi * (j:ℝ) * (2 * N) ^ j / (r * t * M₁ ^ j) := by positivity
      linarith
  calc ∏ j ∈ Finset.Icc h g, fordW r s t N M₁ M₂ j
      ≤ ∏ j ∈ Finset.Icc h g,
          ((2 : ℝ) ^ (g + 3) * max 1 (max (t * M₂ ^ j / N ^ j) (N ^ j / (t * M₁ ^ j)))) := by
        apply Finset.prod_le_prod₀ hnonneg
        intro j hj
        obtain ⟨hj1, hjg⟩ := Finset.mem_Icc.mp hj
        exact fordW_le_max r s t N M₁ M₂ g j hN ht hM₁ hM₂ hM12 hsr hs1 hs2 hr hg1
          (le_trans hh hj1) hjg
    _ = (2 : ℝ) ^ ((g + 3) * (g - h + 1))
          * ∏ j ∈ Finset.Icc h g, max 1 (max (t * M₂ ^ j / N ^ j) (N ^ j / (t * M₁ ^ j))) := by
        have hsplit : ∏ j ∈ Finset.Icc h g,
            ((2 : ℝ) ^ (g + 3) * max 1 (max (t * M₂ ^ j / N ^ j) (N ^ j / (t * M₁ ^ j))))
            = ((2 : ℝ) ^ (g + 3)) ^ (Finset.Icc h g).card
              * ∏ j ∈ Finset.Icc h g, max 1 (max (t * M₂ ^ j / N ^ j) (N ^ j / (t * M₁ ^ j))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
        rw [hsplit, hcard, pow_mul]

/-- For each `j`, Ford's three-term maximum is a single power of `N`. -/
lemma max_term_le_rpow (t N M₁ M₂ μ₁ μ₂ lam : ℝ) (hN : 1 < N) (ht : 0 < t)
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₁eq : M₁ = N ^ μ₁) (hM₂eq : M₂ = N ^ μ₂)
    (hlam : lam = Real.log t / Real.log N) (j : ℕ) :
    max 1 (max (t * M₂ ^ j / N ^ j) (N ^ j / (t * M₁ ^ j)))
      ≤ N ^ (((j:ℝ) * μ₂) - min ((j:ℝ) * μ₂)
          (min ((j:ℝ) - lam) (lam - (j:ℝ) * (1 - μ₁ - μ₂)))) := by
  have hN0 : 0 < N := lt_trans zero_lt_one hN
  have hNne : Real.log N ≠ 0 := ne_of_gt (Real.log_pos hN)
  have ht_eq : t = N ^ lam := by
    have hlog : Real.log N * lam = Real.log t := by rw [hlam]; field_simp
    rw [Real.rpow_def_of_pos hN0, hlog, Real.exp_log ht]
  have hM₂pow : M₂ ^ j = N ^ ((j:ℝ) * μ₂) := by
    have h : (N ^ μ₂) ^ j = N ^ (μ₂ * (j:ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN0)]
    rw [hM₂eq, h, mul_comm]
  have hM₁pow : M₁ ^ j = N ^ ((j:ℝ) * μ₁) := by
    have h : (N ^ μ₁) ^ j = N ^ (μ₁ * (j:ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hN0)]
    rw [hM₁eq, h, mul_comm]
  have hNj : N ^ j = N ^ ((j:ℝ)) := by rw [Real.rpow_natCast]
  have hH₂ : min ((j:ℝ) * μ₂) (min ((j:ℝ) - lam) (lam - (j:ℝ) * (1 - μ₁ - μ₂)))
      ≤ (j:ℝ) * μ₂ := min_le_left _ _
  have hH₁ : min ((j:ℝ) * μ₂) (min ((j:ℝ) - lam) (lam - (j:ℝ) * (1 - μ₁ - μ₂)))
      ≤ (j:ℝ) - lam := le_trans (min_le_right _ _) (min_le_left _ _)
  have hH₀ : min ((j:ℝ) * μ₂) (min ((j:ℝ) - lam) (lam - (j:ℝ) * (1 - μ₁ - μ₂)))
      ≤ lam - (j:ℝ) * (1 - μ₁ - μ₂) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hbase : 1 < N := hN
  refine max_le ?_ (max_le ?_ ?_)
  · have h0 : (0:ℝ) ≤ (j:ℝ) * μ₂ - min ((j:ℝ) * μ₂)
        (min ((j:ℝ) - lam) (lam - (j:ℝ) * (1 - μ₁ - μ₂))) := by linarith
    have := Real.rpow_le_rpow_of_exponent_le (le_of_lt hbase) h0
    rwa [Real.rpow_zero] at this
  · have heq : t * M₂ ^ j / N ^ j = N ^ (lam + (j:ℝ) * μ₂ - (j:ℝ)) := by
      rw [ht_eq, hM₂pow, hNj, ← Real.rpow_add hN0, ← Real.rpow_sub hN0]
    rw [heq]
    have hle : lam + (j:ℝ) * μ₂ - (j:ℝ) ≤ (j:ℝ) * μ₂
        - min ((j:ℝ) * μ₂) (min ((j:ℝ) - lam) (lam - (j:ℝ) * (1 - μ₁ - μ₂))) := by
      linarith
    exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hbase) hle
  · have heq : N ^ j / (t * M₁ ^ j) = N ^ ((j:ℝ) - (j:ℝ) * μ₁ - lam) := by
      rw [hNj, ht_eq, hM₁pow, ← Real.rpow_add hN0, ← Real.rpow_sub hN0]
      congr 1
      ring
    rw [heq]
    have hle : (j:ℝ) - (j:ℝ) * μ₁ - lam ≤ (j:ℝ) * μ₂
        - min ((j:ℝ) * μ₂) (min ((j:ℝ) - lam) (lam - (j:ℝ) * (1 - μ₁ - μ₂))) := by
      linarith
    exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hbase) hle

/-- The product of the three-term maxima is bounded by `M₂^{Σ j} N^{-H}`. -/
lemma prod_max_le_pow (h g : ℕ) (hh : 1 ≤ h) (hhg : h ≤ g)
    (t N M₁ M₂ μ₁ μ₂ lam : ℝ) (hN : 1 < N) (ht : 0 < t)
    (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₁eq : M₁ = N ^ μ₁) (hM₂eq : M₂ = N ^ μ₂)
    (hlam : lam = Real.log t / Real.log N) :
    ∏ j ∈ Finset.Icc h g, max 1 (max (t * M₂ ^ j / N ^ j) (N ^ j / (t * M₁ ^ j)))
      ≤ M₂ ^ (((h:ℝ) + (g:ℝ)) * ((g:ℝ) - (h:ℝ) + 1) / 2)
          * N ^ (-(∑ j ∈ Finset.Icc h g,
              min ((j:ℝ) * μ₂) (min ((j:ℝ) - lam) (lam - (j:ℝ) * (1 - μ₁ - μ₂))))) := by
  have hN0 : 0 < N := lt_trans zero_lt_one hN
  have hstep : ∏ j ∈ Finset.Icc h g, max 1 (max (t * M₂ ^ j / N ^ j) (N ^ j / (t * M₁ ^ j)))
      ≤ ∏ j ∈ Finset.Icc h g, N ^ (((j:ℝ) * μ₂)
          - min ((j:ℝ) * μ₂) (min ((j:ℝ) - lam) (lam - (j:ℝ) * (1 - μ₁ - μ₂)))) := by
    apply Finset.prod_le_prod₀
    · intro j hj
      have := le_max_left (1:ℝ) (max (t * M₂ ^ j / N ^ j) (N ^ j / (t * M₁ ^ j)))
      linarith
    · intro j hj
      exact max_term_le_rpow t N M₁ M₂ μ₁ μ₂ lam hN ht hM₁ hM₂ hM₁eq hM₂eq hlam j
  refine hstep.trans (le_of_eq ?_)
  rw [← Real.rpow_sum_of_pos hN0]
  have hsum : (∑ j ∈ Finset.Icc h g, ((j:ℝ) * μ₂
        - min ((j:ℝ) * μ₂) (min ((j:ℝ) - lam) (lam - (j:ℝ) * (1 - μ₁ - μ₂)))))
      = μ₂ * (∑ j ∈ Finset.Icc h g, (j:ℝ))
        - ∑ j ∈ Finset.Icc h g, min ((j:ℝ) * μ₂)
            (min ((j:ℝ) - lam) (lam - (j:ℝ) * (1 - μ₁ - μ₂))) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum, sum_Icc_id_cast hhg]
  have hexp : μ₂ * (((h:ℝ) + (g:ℝ)) * ((g:ℝ) - (h:ℝ) + 1) / 2)
      - (∑ j ∈ Finset.Icc h g, min ((j:ℝ) * μ₂)
          (min ((j:ℝ) - lam) (lam - (j:ℝ) * (1 - μ₁ - μ₂))))
      = (μ₂ * (((h:ℝ) + (g:ℝ)) * ((g:ℝ) - (h:ℝ) + 1) / 2))
        + (-(∑ j ∈ Finset.Icc h g, min ((j:ℝ) * μ₂)
          (min ((j:ℝ) - lam) (lam - (j:ℝ) * (1 - μ₁ - μ₂))))) := by ring
  rw [hexp, Real.rpow_add hN0]
  congr 1
  rw [hM₂eq, Real.rpow_mul (le_of_lt hN0)]


/-- **Ford's `W`-product bound** (`(5.10)`--`(5.11)` of the reference), proved from
`prod_fordW_le_max` and `prod_max_le_pow`. -/
theorem vkford_Wproduct_self
    (h g : ℕ) (hh : 1 ≤ h) (hhg : h ≤ g)
    (r s t N M₁ M₂ μ₁ μ₂ lam : ℝ) (hN : 1 < N) (ht : 1 ≤ t) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM₁eq : M₁ = N ^ μ₁) (hM₂eq : M₂ = N ^ μ₂)
    (hμ : μ₂ ≤ μ₁) (hsum : μ₁ + μ₂ < 1) (hlam : lam = Real.log t / Real.log N)
    (hs1 : 1 ≤ s) (hr : 13 * (g : ℝ) ≤ r) (hs2 : s ≤ (2 : ℝ) ^ g) (hrs : s ≤ r) :
    (∏ j ∈ Finset.Icc h g, fordW r s t N M₁ M₂ j)
      ≤ (2 : ℝ) ^ ((g + 3) * (g - h + 1))
          * M₂ ^ (((h:ℝ) + (g:ℝ)) * ((g:ℝ) - (h:ℝ) + 1) / 2)
          * N ^ (-(∑ j ∈ Finset.Icc h g,
              min ((j:ℝ) * μ₂) (min ((j:ℝ) - lam) (lam - (j:ℝ) * (1 - μ₁ - μ₂))))) := by
  have hN0 : 0 < N := lt_trans zero_lt_one hN
  have hg1 : 1 ≤ g := le_trans hh hhg
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hM12 : M₂ ≤ M₁ := by
    rw [hM₁eq, hM₂eq]
    exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hN) hμ
  have hH : ∏ j ∈ Finset.Icc h g, fordW r s t N M₁ M₂ j
      ≤ (2 : ℝ) ^ ((g + 3) * (g - h + 1))
          * ∏ j ∈ Finset.Icc h g, max 1 (max (t * M₂ ^ j / N ^ j) (N ^ j / (t * M₁ ^ j))) :=
    prod_fordW_le_max h g r s t N M₁ M₂ hN0 ht hM₁ hM₂ hM12 hrs hs1 hs2 hr hg1 hh hhg
  have hM : ∏ j ∈ Finset.Icc h g, max 1 (max (t * M₂ ^ j / N ^ j) (N ^ j / (t * M₁ ^ j)))
      ≤ M₂ ^ (((h:ℝ) + (g:ℝ)) * ((g:ℝ) - (h:ℝ) + 1) / 2)
          * N ^ (-(∑ j ∈ Finset.Icc h g,
              min ((j:ℝ) * μ₂) (min ((j:ℝ) - lam) (lam - (j:ℝ) * (1 - μ₁ - μ₂))))) :=
    prod_max_le_pow h g hh hhg t N M₁ M₂ μ₁ μ₂ lam hN ht0 hM₁ hM₂ hM₁eq hM₂eq hlam
  calc ∏ j ∈ Finset.Icc h g, fordW r s t N M₁ M₂ j
      ≤ (2 : ℝ) ^ ((g + 3) * (g - h + 1))
          * ∏ j ∈ Finset.Icc h g, max 1 (max (t * M₂ ^ j / N ^ j) (N ^ j / (t * M₁ ^ j))) := hH
    _ ≤ (2 : ℝ) ^ ((g + 3) * (g - h + 1))
          * (M₂ ^ (((h:ℝ) + (g:ℝ)) * ((g:ℝ) - (h:ℝ) + 1) / 2)
            * N ^ (-(∑ j ∈ Finset.Icc h g,
                min ((j:ℝ) * μ₂) (min ((j:ℝ) - lam) (lam - (j:ℝ) * (1 - μ₁ - μ₂)))))) :=
        mul_le_mul_of_nonneg_left hM (by positivity)
    _ = (2 : ℝ) ^ ((g + 3) * (g - h + 1))
          * M₂ ^ (((h:ℝ) + (g:ℝ)) * ((g:ℝ) - (h:ℝ) + 1) / 2)
          * N ^ (-(∑ j ∈ Finset.Icc h g,
              min ((j:ℝ) * μ₂) (min ((j:ℝ) - lam) (lam - (j:ℝ) * (1 - μ₁ - μ₂))))) := by
        ring

end Work.BMF

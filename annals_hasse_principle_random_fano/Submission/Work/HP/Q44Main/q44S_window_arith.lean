import Mathlib
import Submission.Work.HP.Q44Main.q44S_window_inputs

/-!
# `Work.HP.Q44Main.q44S_window_arith`

Dyadic-window arithmetic for the `q44S` sum: for `Kmink ≥ 1` there is `K > 0` such that,
with `N = ⌈logb 2 (8 Kmink (Δ+1))⌉₊` and `Δ ≥ 1`,

* `Σ_{k monotone, Σ k ≤ N} 2 ^ (2 Σ k) ≤ K Δ^2 (log (2Δ))^2`,
* `Σ_{k monotone, Σ k ≤ N} 2 ^ (4 k₀ + 2 k₁ + 2 k₂) ≤ K Δ^3 (log (2Δ))^2`,

the sums being over the box `∏_{j<3} {0,…,N}` of monotone triples.

## Proof

The two sums are dominated by the single windowed sum
`Σ_{k ∈ box} [Monotone k ∧ Σ k ≤ N] r ^ (Σ k)` for `r = 4` and `r = 8` respectively:

* `2 ^ (2 Σ k) = 4 ^ (Σ k)`, and
* `2 ^ (4k₀+2k₁+2k₂) ≤ 8 ^ (Σ k)` because `4k₀+2k₁+2k₂ ≤ 3(k₀+k₁+k₂)`, i.e. `k₀ ≤ k₁ + k₂`,
  which holds for monotone `k`.

`q44S_mono_window_sum_le` bounds that windowed sum by `(N+1)^2 · Σ_{s ≤ N} r^s`: grouping the
sum by the value `s = Σ k` (`Finset.sum_fiberwise_of_maps_to`) and using that the `s`-fiber of
monotone triples has at most `(s+1)^2` elements (`q44S_mono_fiber_card_le`, by the injection
`k ↦ (k₀,k₁)`, injective because `k₂ = s - k₀ - k₁`).

`q44S_geom_le` evaluates the geometric factor as `≤ r^(N+1)/(r-1)`.  Thus the two sums are
`≤ (N+1)^2 · 4^(N+1)/3` and `≤ (N+1)^2 · 8^(N+1)/7`, and with `2^N ≤ 32 Kmink Δ` and
`N+1 ≤ Clog log (2Δ)` (`q44S_window_inputs`) this is `O(Δ^2 (log Δ)^2)` and
`O(Δ^3 (log Δ)^2)`.
-/

open scoped BigOperators

namespace Work.HP.Q44Main

/-- The `s`-fiber of monotone triples with coordinate sum `s` has at most `(s+1)^2` elements.
Indeed `k ↦ (k 0, k 1)` is injective on it (`k 2 = s - k 0 - k 1`) and takes values in
`{0,…,s} × {0,…,s}`. -/
private lemma q44S_mono_fiber_card_le (b : ℕ) (S : Finset (Fin 3 → ℕ))
    (hS : ∀ k ∈ S, Monotone k ∧ (∑ j : Fin 3, k j) = b) :
    S.card ≤ (b + 1) ^ 2 := by
  have hsum : ∀ k ∈ S, k 0 + k 1 + k 2 = b := by
    intro k hk
    have h := (hS k hk).2
    rwa [Fin.sum_univ_three] at h
  have hmaps : Set.MapsTo (fun k : Fin 3 → ℕ => (k 0, k 1)) (↑S)
      (↑((Finset.range (b + 1)).product (Finset.range (b + 1)))) := by
    intro k hk
    change (k 0, k 1) ∈ (Finset.range (b + 1)) ×ˢ (Finset.range (b + 1))
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
    have h : k 0 + k 1 + k 2 = b := hsum k (by simpa using hk)
    omega
  have hinj : Set.InjOn (fun k : Fin 3 → ℕ => (k 0, k 1)) (↑S) := by
    intro k hk k' hk' heq
    have h0 : k 0 = k' 0 := congrArg Prod.fst heq
    have h1 : k 1 = k' 1 := congrArg Prod.snd heq
    have hs := hsum k (by simpa using hk)
    have hs' := hsum k' (by simpa using hk')
    funext j
    fin_cases j
    · exact h0
    · exact h1
    · show k (2 : Fin 3) = k' (2 : Fin 3)
      omega
  have h := Finset.card_le_card_of_injOn (fun k : Fin 3 → ℕ => (k 0, k 1)) hmaps hinj
  have h2 : ((Finset.range (b + 1)).product (Finset.range (b + 1))).card = (b + 1) ^ 2 := by
    rw [show (Finset.range (b+1)).product (Finset.range (b+1))
        = (Finset.range (b+1)) ×ˢ (Finset.range (b+1)) from rfl]
    rw [Finset.card_product, Finset.card_range]; ring
  exact le_trans h (le_of_eq h2)

/-- The windowed sum `Σ_{k ∈ box, Monotone k, Σ k ≤ N} r ^ (Σ k)` is at most
`(N+1)^2 · Σ_{s ≤ N} r^s`: group by `s` and use the fiber count `(s+1)^2 ≤ (N+1)^2`. -/
private lemma q44S_mono_window_sum_le (r : ℝ) (hr : 1 ≤ r) (N : ℕ) :
    (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then r ^ (∑ j : Fin 3, k j) else 0))
      ≤ ((N : ℝ) + 1) ^ 2 * (∑ b ∈ Finset.range (N + 1), r ^ b) := by
  classical
  set G : Finset (Fin 3 → ℕ) :=
    (Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1))).filter
      (fun k => Monotone k ∧ (∑ j : Fin 3, k j) ≤ N) with hG
  rw [show (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then r ^ (∑ j : Fin 3, k j) else 0))
      = ∑ k ∈ G, r ^ (∑ j : Fin 3, k j) from by rw [hG, Finset.sum_filter]]
  have hmaps : ∀ k ∈ G, (∑ j : Fin 3, k j) ∈ Finset.range (N + 1) := by
    intro k hk
    rw [hG, Finset.mem_filter] at hk
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le hk.2.2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun k => r ^ (∑ j : Fin 3, k j))]
  have hinner : ∀ b ∈ Finset.range (N + 1),
      (∑ k ∈ G.filter (fun k => (∑ j : Fin 3, k j) = b), r ^ (∑ j : Fin 3, k j))
        ≤ ((N : ℝ) + 1) ^ 2 * r ^ b := by
    intro b hb
    have hbN : (b : ℝ) ≤ (N : ℝ) := by
      have := Finset.mem_range.mp hb
      exact_mod_cast Nat.le_of_lt_succ this
    have hcard : ((G.filter (fun k => (∑ j : Fin 3, k j) = b)).card : ℝ) ≤ ((b : ℝ) + 1) ^ 2 := by
      have h := q44S_mono_fiber_card_le b (G.filter (fun k => (∑ j : Fin 3, k j) = b)) (by
        intro k hk
        rw [Finset.mem_filter] at hk
        have hkG := hk.1
        rw [hG, Finset.mem_filter] at hkG
        exact ⟨hkG.2.1, hk.2⟩)
      calc ((G.filter (fun k => (∑ j : Fin 3, k j) = b)).card : ℝ)
            ≤ (((b + 1) ^ 2 : ℕ) : ℝ) := by exact_mod_cast h
        _ = ((b : ℝ) + 1) ^ 2 := by push_cast; ring
    have hconst1 : ∀ k ∈ G.filter (fun k => (∑ j : Fin 3, k j) = b),
        r ^ (∑ j : Fin 3, k j) = r ^ b := by
      intro k hk
      rw [Finset.mem_filter] at hk
      rw [hk.2]
    have hconst : (∑ k ∈ G.filter (fun k => (∑ j : Fin 3, k j) = b), r ^ (∑ j : Fin 3, k j))
        = (G.filter (fun k => (∑ j : Fin 3, k j) = b)).card * r ^ b := by
      rw [Finset.sum_congr rfl hconst1, Finset.sum_const, nsmul_eq_mul]
    rw [hconst]
    have hrb : 0 ≤ r ^ b := pow_nonneg (le_trans zero_le_one hr) b
    calc ((G.filter (fun k => (∑ j : Fin 3, k j) = b)).card : ℝ) * r ^ b
        ≤ ((b : ℝ) + 1) ^ 2 * r ^ b := mul_le_mul_of_nonneg_right hcard hrb
      _ ≤ ((N : ℝ) + 1) ^ 2 * r ^ b := by
          apply mul_le_mul_of_nonneg_right _ hrb
          exact pow_le_pow_left₀ (by positivity) (by linarith) 2
  calc ∑ b ∈ Finset.range (N + 1),
        (∑ k ∈ G.filter (fun k => (∑ j : Fin 3, k j) = b), r ^ (∑ j : Fin 3, k j))
      ≤ ∑ b ∈ Finset.range (N + 1), ((N : ℝ) + 1) ^ 2 * r ^ b := Finset.sum_le_sum hinner
    _ = ((N : ℝ) + 1) ^ 2 * (∑ b ∈ Finset.range (N + 1), r ^ b) := (Finset.mul_sum _ _ _).symm

/-- Geometric-series bound `Σ_{b < K} r^b ≤ r^K / (r - 1)` for `1 < r`. -/
private lemma q44S_geom_le (r : ℝ) (hr : 1 < r) (K : ℕ) :
    (∑ b ∈ Finset.range K, r ^ b) ≤ r ^ K / (r - 1) := by
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    rw [Finset.range_zero, Finset.sum_empty]
    exact div_nonneg zero_le_one (by linarith)
  · rw [geom_sum_eq (ne_of_gt hr) K]
    apply div_le_div_of_nonneg_right _ (by linarith)
    have : 0 < r ^ K := pow_pos (by linarith) K
    linarith

/-- `4^(N+1) ≤ 4 (a Δ)^2` from `2^N ≤ a Δ`. -/
private lemma q44S_pow4 (N : ℕ) (a Δ : ℝ) (hpow : (2:ℝ)^N ≤ a * Δ) (hpos : 0 ≤ a * Δ) :
    (4:ℝ)^(N+1) ≤ 4 * (a * Δ)^2 := by
  have h4N : (4:ℝ)^N = ((2:ℝ)^N)^2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, ← pow_mul]
    rw [← pow_mul, Nat.mul_comm]
  rw [pow_succ', h4N]
  have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (2:ℝ)^N) hpow 2
  linarith [this, hpos]

/-- `8^(N+1) ≤ 8 (a Δ)^3` from `2^N ≤ a Δ`. -/
private lemma q44S_pow8 (N : ℕ) (a Δ : ℝ) (hpow : (2:ℝ)^N ≤ a * Δ) (hpos : 0 ≤ a * Δ) :
    (8:ℝ)^(N+1) ≤ 8 * (a * Δ)^3 := by
  have h8N : (8:ℝ)^N = ((2:ℝ)^N)^3 := by
    rw [show (8:ℝ) = 2^3 by norm_num, ← pow_mul]
    rw [← pow_mul, Nat.mul_comm]
  rw [pow_succ', h8N]
  have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (2:ℝ)^N) hpow 3
  linarith [this, hpos]

/-- Assembly: the two windowed sums are `O(Δ^2 (log Δ)^2)` and `O(Δ^3 (log Δ)^2)`, given the
two arithmetic inputs on `N = ⌈logb 2 (8 Kmink (Δ+1))⌉₊`. -/
private theorem q44S_aux (Kmink : ℝ) (hKmink : 1 ≤ Kmink)
    (Clog : ℝ) (hClogpos : 0 < Clog)
    (hinputs : ∀ Δ : ℝ, 1 ≤ Δ →
      (2 : ℝ) ^ (⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊) ≤ 32 * Kmink * Δ
      ∧ ((⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ : ℕ) : ℝ) + 1 ≤ Clog * Real.log (2 * Δ)) :
    ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℝ, 1 ≤ Δ →
      (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ + 1)),
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ ⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊
          then (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j)) else 0))
        ≤ K * Δ ^ 2 * (Real.log (2 * Δ)) ^ 2
      ∧ (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ + 1)),
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ ⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊
          then (2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2) else 0))
        ≤ K * Δ ^ 3 * (Real.log (2 * Δ)) ^ 2 := by
  refine ⟨(4/3) * Clog^2 * (32 * Kmink)^2 + (8/7) * Clog^2 * (32 * Kmink)^3 + 1, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ Clog^2 := sq_nonneg Clog
    have h2 : (0:ℝ) ≤ (32*Kmink)^2 := sq_nonneg _
    have h3 : (0:ℝ) ≤ (32*Kmink)^3 := by positivity
    nlinarith [h1, h2, h3]
  · intro Δ hΔ
    obtain ⟨hpow, hlog⟩ := hinputs Δ hΔ
    set N : ℕ := ⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ with hN
    set L : ℝ := Real.log (2 * Δ) with hL
    have hLpos : 0 < L := by rw [hL]; exact Real.log_pos (by linarith)
    have hLnn : 0 ≤ L := le_of_lt hLpos
    have hCLnn : 0 ≤ Clog := le_of_lt hClogpos
    have hΔnn : (0:ℝ) ≤ Δ := by linarith
    have hNsq : ((N : ℝ) + 1)^2 ≤ Clog^2 * L^2 := by
      have h1 : 0 ≤ (N:ℝ) + 1 := by positivity
      have h2 : ((N:ℝ)+1)^2 ≤ (Clog * L)^2 := pow_le_pow_left₀ h1 hlog 2
      have h3 : (Clog * L)^2 = Clog^2 * L^2 := by ring
      linarith [h2, h3]
    have h4 : (4:ℝ)^(N+1) ≤ 4 * ((32*Kmink) * Δ)^2 := q44S_pow4 N (32*Kmink) Δ hpow (by positivity)
    have h8 : (8:ℝ)^(N+1) ≤ 8 * ((32*Kmink) * Δ)^3 := q44S_pow8 N (32*Kmink) Δ hpow (by positivity)
    have hS1eq : (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j)) else 0))
        = (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then (4 : ℝ) ^ (∑ j : Fin 3, k j) else 0)) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hc : Monotone k ∧ (∑ j : Fin 3, k j) ≤ N
      · rw [if_pos hc, if_pos hc]
        rw [show (4:ℝ) = 2^2 by norm_num, ← pow_mul]
      · rw [if_neg hc, if_neg hc]
    have hS1bound : (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j)) else 0))
        ≤ (4/3) * Clog^2 * (32*Kmink)^2 * Δ^2 * L^2 := by
      rw [hS1eq]
      have hgeom4 : (∑ b ∈ Finset.range (N+1), (4:ℝ)^b) ≤ (4:ℝ)^(N+1) / 3 := by
        have h := q44S_geom_le 4 (by norm_num) (N+1); norm_num at h; exact h
      have hS1a : (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
          (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then (4 : ℝ) ^ (∑ j : Fin 3, k j) else 0))
          ≤ ((N:ℝ)+1)^2 * (∑ b ∈ Finset.range (N+1), (4:ℝ)^b) :=
        q44S_mono_window_sum_le 4 (by norm_num) N
      calc (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
            (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then (4 : ℝ) ^ (∑ j : Fin 3, k j) else 0))
          ≤ ((N:ℝ)+1)^2 * (∑ b ∈ Finset.range (N+1), (4:ℝ)^b) := hS1a
        _ ≤ ((N:ℝ)+1)^2 * ((4:ℝ)^(N+1) / 3) := mul_le_mul_of_nonneg_left hgeom4 (by positivity)
        _ ≤ (Clog^2 * L^2) * ((4 * ((32*Kmink)*Δ)^2) / 3) := by
            apply mul_le_mul hNsq (div_le_div_of_nonneg_right h4 (by norm_num))
            · positivity
            · positivity
        _ = (4/3) * Clog^2 * (32*Kmink)^2 * Δ^2 * L^2 := by ring
    have hS2le : (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then (2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2) else 0))
        ≤ (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then (8 : ℝ) ^ (∑ j : Fin 3, k j) else 0)) := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hc : Monotone k ∧ (∑ j : Fin 3, k j) ≤ N
      · rw [if_pos hc, if_pos hc]
        have hk01 : k 0 ≤ k 1 := hc.1 (by decide)
        have he : 4 * k 0 + 2 * k 1 + 2 * k 2 ≤ 3 * (k 0 + k 1 + k 2) := by omega
        have hs : (∑ j : Fin 3, k j) = k 0 + k 1 + k 2 := Fin.sum_univ_three k
        rw [hs, show (8:ℝ) = 2^3 by norm_num, ← pow_mul]
        exact pow_le_pow_right₀ (by norm_num) he
      · rw [if_neg hc, if_neg hc]
    have hS2bound : (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then (2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2) else 0))
        ≤ (8/7) * Clog^2 * (32*Kmink)^3 * Δ^3 * L^2 := by
      have hgeom8 : (∑ b ∈ Finset.range (N+1), (8:ℝ)^b) ≤ (8:ℝ)^(N+1) / 7 := by
        have h := q44S_geom_le 8 (by norm_num) (N+1); norm_num at h; exact h
      have hS2a : (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
          (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then (8 : ℝ) ^ (∑ j : Fin 3, k j) else 0))
          ≤ ((N:ℝ)+1)^2 * (∑ b ∈ Finset.range (N+1), (8:ℝ)^b) :=
        q44S_mono_window_sum_le 8 (by norm_num) N
      calc (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
            (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then (2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2) else 0))
          ≤ (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
              (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then (8 : ℝ) ^ (∑ j : Fin 3, k j) else 0)) := hS2le
        _ ≤ ((N:ℝ)+1)^2 * (∑ b ∈ Finset.range (N+1), (8:ℝ)^b) := hS2a
        _ ≤ ((N:ℝ)+1)^2 * ((8:ℝ)^(N+1) / 7) := mul_le_mul_of_nonneg_left hgeom8 (by positivity)
        _ ≤ (Clog^2 * L^2) * ((8 * ((32*Kmink)*Δ)^3) / 7) := by
            apply mul_le_mul hNsq (div_le_div_of_nonneg_right h8 (by norm_num))
            · positivity
            · positivity
        _ = (8/7) * Clog^2 * (32*Kmink)^3 * Δ^3 * L^2 := by ring
    refine ⟨?_, ?_⟩
    · calc (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
            (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j)) else 0))
          ≤ (4/3) * Clog^2 * (32*Kmink)^2 * Δ^2 * L^2 := hS1bound
        _ ≤ ((4/3) * Clog^2 * (32 * Kmink)^2 + (8/7) * Clog^2 * (32 * Kmink)^3 + 1) * Δ^2 * L^2 := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right _ (sq_nonneg Δ)) (sq_nonneg L)
            have hB : 0 ≤ (8/7) * Clog^2 * (32*Kmink)^3 + 1 := by positivity
            linarith
    · calc (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)),
            (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then (2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2) else 0))
          ≤ (8/7) * Clog^2 * (32*Kmink)^3 * Δ^3 * L^2 := hS2bound
        _ ≤ ((4/3) * Clog^2 * (32 * Kmink)^2 + (8/7) * Clog^2 * (32 * Kmink)^3 + 1) * Δ^3 * L^2 := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right _ (by positivity : (0:ℝ) ≤ Δ^3)) (sq_nonneg L)
            have hB : 0 ≤ (4/3) * Clog^2 * (32*Kmink)^2 + 1 := by positivity
            linarith

theorem q44S_window_arith (Kmink : ℝ) (hKmink : 1 ≤ Kmink) :
    ∃ K : ℝ, 0 < K ∧ ∀ Δ : ℝ, 1 ≤ Δ →
      (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ + 1)),
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ ⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊
          then (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j)) else 0))
        ≤ K * Δ ^ 2 * (Real.log (2 * Δ)) ^ 2
      ∧ (∑ k ∈ Fintype.piFinset (fun _ : Fin 3 => Finset.range (⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ + 1)),
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ ⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊
          then (2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2) else 0))
        ≤ K * Δ ^ 3 * (Real.log (2 * Δ)) ^ 2 := by
  obtain ⟨Clog, hClogpos, _hClog1, hinputs⟩ := q44S_window_inputs Kmink hKmink
  exact q44S_aux Kmink hKmink Clog hClogpos hinputs

end Work.HP.Q44Main

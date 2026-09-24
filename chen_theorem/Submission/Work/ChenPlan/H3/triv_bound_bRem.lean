import Mathlib
import Submission.Work.ChenPlan.H3.Defs
import Submission.Work.NumberTheory.Chen.BTermCount.Basic
import Submission.Work.ChenPlan.H1.weighted_triv_bound

/-!
# The trivial `9^{ω(d)}`-weighted bound for the `B`-term remainder

This file proves the elementary (Bombieri--Vinogradov independent) bound

`Σ_{d ∣ P, d < D} 9^{ω(d)} |bRem x M Y d| ≤ C · x · (log x)^10`

for the ternary remainder `bRem x M Y d = #{n ∈ B̄ : d ∣ n - 2} - #B̄/φ(d)` of Chen's `h3`,
valid for every window top `Y`, every sift limit `M` and every level `D ≤ √x`.  It is the
`h3` analogue of `Submission.Work.ChenPlan.H1.weighted_triv_bound`.

The proof is the trivial one: `|bRem d| ≤ (x+2)/d + 1 + (x+2)/φ(d)`, and the `9^{ω(d)}`-weighted
divisor sums are dominated by Euler products,
`Σ_{d ∣ P, d ≤ N} 9^{ω(d)}/d ≤ ∏_{p ≤ N} (1 + 9/p) ≤ C (log N)^9`,
`Σ_{d ∣ P, d ≤ N} 9^{ω(d)}/φ(d) ≤ ∏_{p ≤ N} (1 + 9/(p-1)) ≤ C (log N)^9`.
-/

open Finset
open scoped BigOperators
open scoped ArithmeticFunction.Omega

namespace Work.ChenPlan.H3

noncomputable section

attribute [local instance] Classical.propDecidable

open Commons.NumberTheory.Chen.ChenEight
open Work.NumberTheory.Chen.BTermCount

/-! ## Elementary counting lemmas about the `B`-product set -/

/-- Every element of `B̄` lies in `[2, x+2]`. -/
lemma mem_bProdSet_le (x M Y n : ℕ) (hn : n ∈ bProdSet x M Y) : n ≤ x + 2 :=
  (Finset.mem_Icc.mp (bProdSet_subset_Icc x M Y hn)).2

/-- `B̄` has at most `x + 1` elements. -/
lemma card_bProdSet_le (x M Y : ℕ) : (bProdSet x M Y).card ≤ x + 1 := by
  have h := Finset.card_le_card (bProdSet_subset_Icc x M Y)
  rw [Nat.card_Icc] at h
  omega

/-- The number of `n ∈ B̄` with `d ∣ n - 2` is at most `x / d + 1`: the map
`n ↦ (n-2)/d` is injective there and takes values in `{0, …, x/d}`. -/
lemma card_filter_dvd_sub_le (x M Y d : ℕ) (hd : 1 ≤ d) :
    ((bProdSet x M Y).filter (fun n => d ∣ n - 2)).card ≤ x / d + 1 := by
  set S : Finset ℕ := (bProdSet x M Y).filter (fun n => d ∣ n - 2) with hS
  have hmaps : ∀ n ∈ S, (n - 2) / d ∈ Finset.range (x / d + 1) := by
    intro n hn
    rw [Finset.mem_range]
    have hle : n - 2 ≤ x := by
      have := mem_bProdSet_le x M Y n (Finset.mem_filter.mp (by rw [← hS]; exact hn)).1
      omega
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hle)
  have hinj : Set.InjOn (fun n : ℕ => (n - 2) / d) (↑S : Set ℕ) := by
    intro a ha b hb heq
    rw [Finset.mem_coe, hS, Finset.mem_filter] at ha hb
    have ha' : d ∣ a - 2 := ha.2
    have hb' : d ∣ b - 2 := hb.2
    have h2a : 2 ≤ a := two_le_of_mem_bProdSet ha.1
    have h2b : 2 ≤ b := two_le_of_mem_bProdSet hb.1
    have hq : (a - 2) / d = (b - 2) / d := heq
    have : a - 2 = b - 2 := by
      rw [← Nat.mul_div_cancel' ha', ← Nat.mul_div_cancel' hb', hq]
    omega
  calc S.card = (S.image (fun n => (n - 2) / d)).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (x / d + 1)).card := by
        refine Finset.card_le_card ?_
        intro k hk
        rw [Finset.mem_image] at hk
        obtain ⟨n, hn, rfl⟩ := hk
        exact hmaps n hn
    _ = x / d + 1 := Finset.card_range _

/-! ## The target bound -/

/-- **The trivial `9^{ω(d)}`-weighted bound for the `B`-term remainder.**  With
`bRem x M Y d = #{n ∈ B̄ : d ∣ n - 2} - #B̄/φ(d)` and `B̄ = bProdSet x M Y` (products of three
primes with `M ≤ q < Y ≤ q₂ ≤ q₃`), for a sift limit `M ≥ x^{1/10}`, window top `Y ≤ 2x^{1/3}` and
level `D ≤ √x`,
`Σ_{d ∣ oddPrimLt Y, d < D} 9^{ω(d)} |bRem x M Y d| ≤ C x (log x)^{10}`.

The proof is the elementary one: `|bRem d| ≤ (x+2)/d + 1 + (x+2)/φ(d)`
(since `#B̄ ≤ x+1` and `#{n ∈ B̄ : d ∣ n-2} ≤ (x+2)/d + 1`), and the `9^{ω(d)}`-weighted divisor
sums are dominated by the Euler products `∏_{p ≤ Y}(1 + 9/p)` and `∏_{p ≤ Y}(1 + 9/(p-1))`,
each `≪ (log Y)^9`; the remaining `Σ_{d < D} 9^{ω(d)}` is `≪ D(log D)^8 ≤ √x (log x)^8`.
The `h1` analogue of this lemma, `Submission.Work.ChenPlan.H1.weighted_triv_bound`
(in `Submission.Work.ChenPlan.H1.weighted_triv_bound`), is proved and can be copied, replacing the
shifted-prime remainder `rD x d` by `bRem x M Y d`. -/
theorem triv_bound_bRem :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℕ in Filter.atTop, ∀ (M Y : ℕ) (D : ℝ),
      (x : ℝ) ^ ((1 : ℝ) / 10) ≤ (M : ℝ) →
      (Y : ℝ) ≤ 2 * (x : ℝ) ^ ((1 : ℝ) / 3) →
      4 ≤ D → D ≤ Real.sqrt (x : ℝ) →
      ∑ d ∈ (Commons.NumberTheory.Chen.ChenEight.oddPrimLt Y).divisors.filter
            (fun d : ℕ => (d : ℝ) < D),
          (9 : ℝ) ^ d.primeFactors.card *
            |Work.NumberTheory.Chen.BTermCount.bRem x M Y d|
        ≤ C * (x : ℝ) * (Real.log (x : ℝ)) ^ 10 := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.ChenPlan.H1.prod_primes_one_add_nine_div_le
  obtain ⟨C2, hC2pos, hC2⟩ := Work.ChenPlan.H1.prod_primes_one_add_nine_div_pred_le
  refine ⟨3 * (2 * C1 + C2), by positivity, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 16] with x hx16
  intro M Y D _hM _hY hD4 hDle
  set P : ℕ := oddPrimLt Y with hPdef
  set N : ℕ := ⌊Real.sqrt (x : ℝ)⌋₊ with hNdef
  set L : ℝ := Real.log (x : ℝ) with hLdef
  have hx2 : 2 ≤ x := by omega
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have h16R : (16 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx16
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef]
    have h16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num, Real.log_pow]; norm_num
    have h2 : (1 : ℝ) ≤ Real.log (16 : ℝ) := by rw [h16]; nlinarith [Real.log_two_gt_d9]
    exact le_trans h2 (Real.log_le_log (by norm_num) h16R)
  have hLnn : (0 : ℝ) ≤ L := le_trans zero_le_one hL1
  have hN2 : 2 ≤ N := by
    rw [hNdef, Nat.le_floor_iff (Real.sqrt_nonneg _)]
    have h4 : (4 : ℝ) ≤ Real.sqrt (x : ℝ) := by
      have hsqrt16 : Real.sqrt (16 : ℝ) = 4 := by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      calc (4 : ℝ) = Real.sqrt 16 := hsqrt16.symm
        _ ≤ Real.sqrt (x : ℝ) := Real.sqrt_le_sqrt h16R
    exact le_trans (by norm_num) h4
  have hNx : (N : ℝ) ≤ (x : ℝ) := by
    rw [hNdef]
    refine le_trans (Nat.floor_le (Real.sqrt_nonneg _)) ?_
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith [h16R]⟩
  have hlogNle : Real.log (N : ℝ) ≤ L := by
    rw [hLdef]
    exact Real.log_le_log (by positivity) hNx
  have hPsq : Squarefree P := by rw [hPdef]; exact squarefree_oddPrimLt Y
  set F : Finset ℕ := P.divisors.filter (fun d : ℕ => (d : ℝ) < D) with hFdef
  set G : Finset ℕ := P.divisors.filter (fun d : ℕ => d ≤ N) with hGdef
  have hFG : F ⊆ G := by
    intro d hd
    rw [hFdef, Finset.mem_filter] at hd
    rw [hGdef, Finset.mem_filter]
    refine ⟨hd.1, ?_⟩
    rw [hNdef, Nat.le_floor_iff (Real.sqrt_nonneg _)]
    exact le_of_lt (lt_of_lt_of_le hd.2 hDle)
  -- `√x ≤ x + 2`, so every `d < D ≤ √x` satisfies `d < x+2`.
  have hsqrt_le : Real.sqrt (x : ℝ) ≤ (x : ℝ) + 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith [hxpos]⟩
  -- ## Step 1: the per-divisor bound
  have hterm : ∀ d ∈ F, (9 : ℝ) ^ d.primeFactors.card * |bRem x M Y d|
      ≤ (9 : ℝ) ^ d.primeFactors.card *
        (2 * ((x : ℝ) + 2) / (d : ℝ) + ((x : ℝ) + 2) / (Nat.totient d : ℝ)) := by
    intro d hd
    have hdF : d ∈ P.divisors.filter (fun d : ℕ => (d : ℝ) < D) := by rw [← hFdef]; exact hd
    have hdvd : d ∈ P.divisors := (Finset.mem_filter.mp hdF).1
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hdvd
    have hdle : (d : ℝ) < D := (Finset.mem_filter.mp hdF).2
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hdx : (d : ℝ) < (x : ℝ) + 2 := lt_of_lt_of_le (lt_of_lt_of_le hdle hDle) hsqrt_le
    have hdiv1 : (1 : ℝ) ≤ ((x : ℝ) + 2) / (d : ℝ) := (one_le_div hdpos).mpr (le_of_lt hdx)
    have hphi_pos : (0 : ℝ) < (Nat.totient d : ℝ) :=
      Nat.cast_pos.mpr (Nat.totient_pos.mpr (by omega : 0 < d))
    have hScard : (((bProdSet x M Y).filter (fun n => d ∣ n - 2)).card : ℝ)
        ≤ (x : ℝ) / (d : ℝ) + 1 := by
      have hS := card_filter_dvd_sub_le x M Y d hd1
      have hS' : ((((bProdSet x M Y).filter (fun n => d ∣ n - 2)).card : ℕ) : ℝ)
          ≤ (((x / d + 1 : ℕ)) : ℝ) := by exact_mod_cast hS
      have hcast : (((x / d + 1 : ℕ)) : ℝ) = (((x / d : ℕ)) : ℝ) + 1 := by push_cast; ring
      have hc : (((x / d : ℕ)) : ℝ) ≤ (x : ℝ) / (d : ℝ) := Nat.cast_div_le
      calc (((bProdSet x M Y).filter (fun n => d ∣ n - 2)).card : ℝ)
          ≤ (((x / d + 1 : ℕ)) : ℝ) := hS'
        _ = (((x / d : ℕ)) : ℝ) + 1 := hcast
        _ ≤ (x : ℝ) / (d : ℝ) + 1 := add_le_add hc le_rfl
    have hBcard : (((bProdSet x M Y).card : ℕ) : ℝ) ≤ (x : ℝ) + 1 := by
      have hB : ((bProdSet x M Y).card : ℕ) ≤ x + 1 := card_bProdSet_le x M Y
      have hcast : (((x + 1 : ℕ)) : ℝ) = (x : ℝ) + 1 := by push_cast; ring
      calc (((bProdSet x M Y).card : ℕ) : ℝ) ≤ (((x + 1 : ℕ)) : ℝ) := by exact_mod_cast hB
        _ = (x : ℝ) + 1 := hcast
    have habs : |bRem x M Y d|
        ≤ (((bProdSet x M Y).filter (fun n => d ∣ n - 2)).card : ℝ)
          + (((bProdSet x M Y).card : ℕ) : ℝ) / (Nat.totient d : ℝ) := by
      rw [bRem, abs_sub_le_iff]
      constructor
      · have h2 : (0 : ℝ) ≤ (((bProdSet x M Y).card : ℕ) : ℝ) / (Nat.totient d : ℝ) :=
          div_nonneg (Nat.cast_nonneg _) (le_of_lt hphi_pos)
        linarith
      · have h2 : (0 : ℝ) ≤ (((bProdSet x M Y).filter (fun n => d ∣ n - 2)).card : ℝ) :=
          Nat.cast_nonneg _
        linarith
    have hmain : |bRem x M Y d|
        ≤ 2 * ((x : ℝ) + 2) / (d : ℝ) + ((x : ℝ) + 2) / (Nat.totient d : ℝ) := by
      have hφle : (((bProdSet x M Y).card : ℕ) : ℝ) / (Nat.totient d : ℝ)
          ≤ ((x : ℝ) + 2) / (Nat.totient d : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) (le_of_lt hphi_pos)
      have hxdiv : (x : ℝ) / (d : ℝ) + 1 ≤ 2 * ((x : ℝ) + 2) / (d : ℝ) := by
        have hsum : (x : ℝ) / (d : ℝ) + ((x : ℝ) + 2) / (d : ℝ)
            = (2 * (x : ℝ) + 2) / (d : ℝ) := by
          rw [← add_div]; ring
        have hmono : (x : ℝ) / (d : ℝ) + 1
            ≤ (x : ℝ) / (d : ℝ) + ((x : ℝ) + 2) / (d : ℝ) :=
          add_le_add le_rfl hdiv1
        rw [hsum] at hmono
        have hnum : 2 * (x : ℝ) + 2 ≤ 2 * ((x : ℝ) + 2) := by linarith
        exact le_trans hmono (div_le_div_of_nonneg_right hnum (le_of_lt hdpos))
      calc |bRem x M Y d|
          ≤ (((bProdSet x M Y).filter (fun n => d ∣ n - 2)).card : ℝ)
            + (((bProdSet x M Y).card : ℕ) : ℝ) / (Nat.totient d : ℝ) := habs
        _ ≤ ((x : ℝ) / (d : ℝ) + 1) + ((x : ℝ) + 2) / (Nat.totient d : ℝ) :=
            add_le_add hScard hφle
        _ ≤ (2 * ((x : ℝ) + 2) / (d : ℝ)) + ((x : ℝ) + 2) / (Nat.totient d : ℝ) :=
            add_le_add hxdiv le_rfl
    exact mul_le_mul_of_nonneg_left hmain (by positivity)
  -- ## Step 2: sum
  have hsumstep : ∑ d ∈ F, (9 : ℝ) ^ d.primeFactors.card * |bRem x M Y d|
      ≤ (2 * ((x : ℝ) + 2)) * (∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card / (d : ℝ))
        + ((x : ℝ) + 2)
          * (∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ)) := by
    have hsub : ∑ d ∈ F, (9 : ℝ) ^ d.primeFactors.card * |bRem x M Y d|
        ≤ ∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card *
            (2 * ((x : ℝ) + 2) / (d : ℝ) + ((x : ℝ) + 2) / (Nat.totient d : ℝ)) := by
      refine le_trans (Finset.sum_le_sum hterm) ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg hFG (fun d _ _ => ?_)
      refine mul_nonneg (by positivity) ?_
      exact add_nonneg (div_nonneg (by linarith [hxpos]) (Nat.cast_nonneg d))
        (div_nonneg (by linarith [hxpos]) (Nat.cast_nonneg _))
    refine le_trans hsub (le_of_eq ?_)
    have hS1eq : (∑ d ∈ G,
          (9 : ℝ) ^ d.primeFactors.card * (2 * ((x : ℝ) + 2) / (d : ℝ)))
        = (2 * ((x : ℝ) + 2)) * (∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card / (d : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun d _ => by ring)
    have hS2eq : (∑ d ∈ G,
          (9 : ℝ) ^ d.primeFactors.card * (((x : ℝ) + 2) / (Nat.totient d : ℝ)))
        = ((x : ℝ) + 2)
          * (∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun d _ => by ring)
    calc ∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card *
            (2 * ((x : ℝ) + 2) / (d : ℝ) + ((x : ℝ) + 2) / (Nat.totient d : ℝ))
        = (∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card * (2 * ((x : ℝ) + 2) / (d : ℝ)))
          + ∑ d ∈ G,
              (9 : ℝ) ^ d.primeFactors.card * (((x : ℝ) + 2) / (Nat.totient d : ℝ)) := by
          simp only [mul_add, Finset.sum_add_distrib]
      _ = (2 * ((x : ℝ) + 2)) * (∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card / (d : ℝ))
          + ((x : ℝ) + 2)
            * (∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ)) := by
          rw [hS1eq, hS2eq]
  -- ## Step 3: the two divisor sums
  have hsubPN : P.primeFactors.filter (fun p : ℕ => p ≤ N) ⊆ Nat.primesBelow (N + 1) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    rw [Nat.mem_primesBelow]
    exact ⟨by omega, (Nat.mem_primeFactors.mp hp.1).1⟩
  have hS1 : ∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card / (d : ℝ) ≤ C1 * L ^ 9 := by
    have h1 := Work.ChenPlan.H1.sum_div_nine_pow_div_le P N hPsq
    rw [← hGdef] at h1
    refine le_trans h1 ?_
    have hmono : (∏ p ∈ P.primeFactors.filter (fun p : ℕ => p ≤ N), (1 + 9 / (p : ℝ)))
        ≤ ∏ p ∈ Nat.primesBelow (N + 1), (1 + 9 / (p : ℝ)) :=
      Finset.prod_le_prod_of_subset_of_one_le₀ hsubPN
        (fun p _ => by
          have h9 : (0 : ℝ) ≤ 9 / (p : ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg p)
          exact add_nonneg zero_le_one h9)
        (fun p _ _ => by
          have h9 : (0 : ℝ) ≤ 9 / (p : ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg p)
          exact le_add_of_nonneg_right h9)
    have hbig := hC1 N hN2
    refine le_trans (le_trans hmono hbig) ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))) hlogNle 9)
      (le_of_lt hC1pos)
  have hS2 : ∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ) ≤ C2 * L ^ 9 := by
    have h1 := Work.ChenPlan.H1.sum_div_nine_pow_totient_le P N hPsq
    rw [← hGdef] at h1
    refine le_trans h1 ?_
    have hmono : (∏ p ∈ P.primeFactors.filter (fun p : ℕ => p ≤ N),
          (1 + 9 / ((p : ℝ) - 1)))
        ≤ ∏ p ∈ Nat.primesBelow (N + 1), (1 + 9 / ((p : ℝ) - 1)) :=
      Finset.prod_le_prod_of_subset_of_one_le₀ hsubPN
        (fun p hp => by
          have hp2 : 2 ≤ p := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).1.two_le
          have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
          have h9 : (0 : ℝ) ≤ 9 / ((p : ℝ) - 1) := div_nonneg (by norm_num) (by linarith)
          exact add_nonneg zero_le_one h9)
        (fun p hp _ => by
          have hp2 : 2 ≤ p := Nat.two_le_of_mem_primesBelow hp
          have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
          have h9 : (0 : ℝ) ≤ 9 / ((p : ℝ) - 1) := div_nonneg (by norm_num) (by linarith)
          exact le_add_of_nonneg_right h9)
    have hbig := hC2 N hN2
    refine le_trans (le_trans hmono hbig) ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))) hlogNle 9)
      (le_of_lt hC2pos)
  -- ## Step 4: assemble
  have hfin : (2 * ((x : ℝ) + 2)) * (C1 * L ^ 9) + ((x : ℝ) + 2) * (C2 * L ^ 9)
      ≤ (3 * (2 * C1 + C2)) * (x : ℝ) * L ^ 10 := by
    have hA : (0 : ℝ) ≤ 2 * C1 + C2 := by linarith
    have hx3 : (x : ℝ) + 2 ≤ 3 * (x : ℝ) := by linarith
    have hL9nn : (0 : ℝ) ≤ L ^ 9 := pow_nonneg hLnn 9
    have hL9le : L ^ 9 ≤ L ^ 10 := by
      have h := mul_le_mul_of_nonneg_left hL1 hL9nn
      simpa [pow_succ] using h
    have h1 : (2 * ((x : ℝ) + 2)) * (C1 * L ^ 9) + ((x : ℝ) + 2) * (C2 * L ^ 9)
        = ((x : ℝ) + 2) * (2 * C1 + C2) * L ^ 9 := by ring
    have h2 : ((x : ℝ) + 2) * (2 * C1 + C2) * L ^ 9
        ≤ (3 * (x : ℝ)) * (2 * C1 + C2) * L ^ 9 := by
      have h := mul_le_mul_of_nonneg_right hx3 hA
      exact mul_le_mul_of_nonneg_right h hL9nn
    have h3 : (3 * (x : ℝ)) * (2 * C1 + C2) * L ^ 9
        ≤ (3 * (x : ℝ)) * (2 * C1 + C2) * L ^ 10 :=
      mul_le_mul_of_nonneg_left hL9le (by positivity)
    have h4 : (3 * (x : ℝ)) * (2 * C1 + C2) * L ^ 10
        = (3 * (2 * C1 + C2)) * (x : ℝ) * L ^ 10 := by ring
    calc (2 * ((x : ℝ) + 2)) * (C1 * L ^ 9) + ((x : ℝ) + 2) * (C2 * L ^ 9)
        = ((x : ℝ) + 2) * (2 * C1 + C2) * L ^ 9 := h1
      _ ≤ (3 * (x : ℝ)) * (2 * C1 + C2) * L ^ 9 := h2
      _ ≤ (3 * (x : ℝ)) * (2 * C1 + C2) * L ^ 10 := h3
      _ = (3 * (2 * C1 + C2)) * (x : ℝ) * L ^ 10 := h4
  calc ∑ d ∈ F, (9 : ℝ) ^ d.primeFactors.card * |bRem x M Y d|
      ≤ (2 * ((x : ℝ) + 2)) * (∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card / (d : ℝ))
        + ((x : ℝ) + 2)
          * (∑ d ∈ G, (9 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ)) := hsumstep
    _ ≤ (2 * ((x : ℝ) + 2)) * (C1 * L ^ 9) + ((x : ℝ) + 2) * (C2 * L ^ 9) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left hS1 (by positivity)
        · exact mul_le_mul_of_nonneg_left hS2 (by positivity)
    _ ≤ (3 * (2 * C1 + C2)) * (x : ℝ) * L ^ 10 := hfin

end

end Work.ChenPlan.H3

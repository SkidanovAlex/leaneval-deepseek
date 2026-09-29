import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.nnDist
import Submission.Work.TMC16Core.Basic.rational_block_prod
import Submission.Work.TMC16Core.Trig.rat_prod_min_removed_v2
import Submission.Work.TMC16Core.Trig.rat_prod_erase_le
import Submission.Work.TMC16Core.Trig.grid_sep
import Submission.Work.TMC16Core.Trig.harmonic_sum_le_log
import Submission.Work.TMC16Core.Core.grid_card_bad
import Submission.Work.TMC16Core.Core.coprime_sep_gen
import Submission.Work.TMC16Core.Core.abs_log_sin_sub_le
import Submission.Work.TMC16Core.Core.inv_sum_card_filter

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1200000

namespace Work.TMC16Core.Core

open Finset
open Work.TMC16Core.Basic

/-! ## Elementary facts about `nn` (distance to `ℤ`) and `S w = |sin (π w)|` -/

lemma nn_neg_aux (w : ℝ) : nn (-w) = nn w := by
  apply le_antisymm
  · simp only [nn]
    calc |-w - ↑(round (-w))| ≤ |-w + ↑(round w)| := by
          simpa using round_le (-w) (-(round w))
      _ = |w - ↑(round w)| := by
          rw [show (-w : ℝ) + ↑(round w) = -(w - ↑(round w)) by ring, abs_neg]
  · simp only [nn]
    calc |w - ↑(round w)| ≤ |w + ↑(round (-w))| := by
          simpa using round_le w (-(round (-w)))
      _ = |-w - ↑(round (-w))| := by
          rw [show (w : ℝ) + ↑(round (-w)) = -(-w - ↑(round (-w))) by ring, abs_neg]

lemma nn_sub_le_aux (a b : ℝ) : nn (a - b) ≤ nn a + nn b := by
  have h : a - b = a + (-b) := by ring
  rw [h]
  calc nn (a + -b) ≤ nn a + nn (-b) := nn_add_le a (-b)
    _ = nn a + nn b := by rw [nn_neg_aux]

lemma two_mul_nn_le_S_aux (t : ℝ) : 2 * nn t ≤ S t := by
  have h := two_div_pi_mul_le_S t
  have hpi : (2 : ℝ) / Real.pi * (Real.pi * nn t) = 2 * nn t := by field_simp
  rwa [hpi] at h

lemma S_le_iff_nn_le_aux (a b : ℝ) : S a ≤ S b ↔ nn a ≤ nn b := by
  rw [S_eq_sin_nn, S_eq_sin_nn]
  have ha : Real.pi * nn a ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [Set.mem_Icc]
    exact ⟨by nlinarith [Real.pi_pos, nn_nonneg a], by nlinarith [Real.pi_pos, nn_le_half a]⟩
  have hb : Real.pi * nn b ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [Set.mem_Icc]
    exact ⟨by nlinarith [Real.pi_pos, nn_nonneg b], by nlinarith [Real.pi_pos, nn_le_half b]⟩
  rw [Real.strictMonoOn_sin.le_iff_le ha hb]
  constructor <;> intro h <;> nlinarith [Real.pi_pos]

lemma block_term (α x : ℝ) (k : ℕ) :
    |Real.sin (2 * Real.pi * (x + (k : ℝ) * α / 2))| = S (2 * x + (k : ℝ) * α) := by
  rw [S]; congr 1; ring_nf

lemma block_term_rat (p : ℤ) (q : ℕ) (x : ℝ) (k : ℕ) :
    |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| =
      S (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) := by
  rw [S]; congr 1; ring_nf

lemma fracDist_eq_nn_aux (t : ℝ) : Work.TMC16Core.fracDist t = nn t := rfl

lemma log_four_le_two : Real.log 4 ≤ 2 := by
  have h : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h, Real.log_pow]; push_cast
  have := Real.log_two_lt_d9; linarith

lemma log_two_div_pi_ge : -(1 : ℝ) ≤ Real.log (2 / Real.pi) := by
  have h1 : Real.log (2 / Real.pi) = -Real.log (Real.pi / 2) := by
    rw [show (2 : ℝ) / Real.pi = (Real.pi / 2)⁻¹ by field_simp, Real.log_inv]
  have h2 : Real.log (Real.pi / 2) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < Real.pi / 2)
    linarith [Real.pi_le_four]
  linarith



/-- **AJ §9, Lemma 9.6 (`irrat-1`): the irrational block product with the minimal factor
removed, in the general regime `q * Δ < 1`.**

`α` is real, `q ≥ 1`, `Δ > 0` with `|q * α - p| ≤ Δ` for some integer `p`, `q * Δ < 1`, and the
block sites are pairwise separated modulo `ℤ`: `fracDist ((k-l) * α) ≥ 1/(2q)` for
`1 ≤ k, l ≤ q`, `k ≠ l`.  Then for every `x : ℝ` and every index `k₀ ∈ {1,…,q}` at which
`|sin (2π (x + k α/2))|` is minimal, the product of the remaining factors is `2^{-(q-1)}` up to
a factor `q^{32}`:

  `|log (∏_{k ≠ k₀} |sin (2π (x + k α/2))|) + (q-1) * log 2| ≤ 32 * log q`.

The existing statement `Submission.Work.TMC16Core.Basic.irrat_block_prod` is this with the
stronger smallness hypothesis `q * Δ ≤ 1/8`; the general hypothesis `q * Δ < 1` is what the
continued-fraction applications supply (`Δ < 1/q_next`, so `q * Δ` can be as large as `1 - ε`,
e.g. `q = F_m`, `Δ = ‖F_m α‖` for the golden ratio gives `q * Δ ≈ 0.446`).  A proof must
therefore not bound every term of the comparison sum uniformly.

Suggested route (the paper's proof, with the comparison sum split by size).  Notation:
`S_k = |sin (2π (x + kα/2))|`, `B_k = |sin (2π (x + k p/(2q)))|`, `k₁` the minimiser of `B`,
`G = (Icc 1 q).erase k₀ \ {k₁}` the double-erase.  Then
`log (∏_{k≠k₀} 2S_k) = Σ_{k∈G} (log 2S_k - log 2B_k) + log (∏_{k≠k₁} 2B_k) - log (2B_{k₀}) + log (2S_{k₁})`.
* `Nat.Coprime p.natAbs q` follows from `hsep` and `q * Δ < 1` (cf. `Trig.coprime_of_sep`,
  whose proof only uses `q * Δ ≤ 1/8` as a convenient constant), so `Trig.grid_sep` gives
  `1/(2q) ≤ nn (2x + k p/q)` for `k ≠ k₁`, i.e. `B_k ≥ 1/q`; and `Basic.nnDist` gives
  `S_k = sin (π * nn (ξ + kα))` and `2 nn ≤ S`.
* Rational side: `Basic.rational_block_prod` gives `∏_{k=1}^q 2B_k = 2 |sin (2π q x)| ≤ 2`;
  `Basic.rational_prod_min_removed` gives `∏_{k≠k₁} |sin| ≥ q (2/π) / 2^{q-1}`, i.e.
  `log (∏_{k≠k₁} 2B_k) ∈ [log (2q/π), log q]`; the two special terms are bounded by
  `|log (2B_{k₀})| ≤ log (2πq)` and, by `hsep`/minimality, `|log (2S_{k₁})| ≤ log (4q)`.
* Comparison, with `a_k = nn (2x + kα)`, `b_k = nn (2x + kp/q)`: `|a_k - b_k| ≤ πΔ`, and
  `|log (S_k/B_k)| ≤ |log (a_k/b_k)|`.  Split at `b_k ≥ 4πΔ`: on the good set,
  `|log (a_k/b_k)| ≤ (4πΔ/3) / b_k`, and `Σ_{k∈G} 1/b_k ≤ 2q(1 + log q)` (the grid points,
  sorted by their `nn`-value, satisfy `b_(j) ≥ j/q` by `Trig.grid_sep`; `Trig.harmonic_sum_le_log`
  bounds the harmonic sum); on the bad set, `|G ∩ {b < γ}| ≤ 2γq + 1` (same sortedness) and
  `Σ_{k bad} log (1 + πΔ/b_k) ≤ Σ_{j ≤ 4πΔq+1} log (1 + 2πΔq/j) ≤ C` for an absolute constant
  `C` (e.g. `C = 12` suffices for `2πΔq ≤ 2π`).  The constants work out: the total is at most
  `(4π + 3) log q + 40 ≤ 32 log q` for `q ≥ 7`, and for `q ≤ 6` the crude bounds
  `-(q-1) log q ≤ log (∏_{k∈F} 2S_k) ≤ (q-1) log 2` (from `2nn ≤ S ≤ 1`) suffice. -/
theorem irrat_block_gen {α : ℝ} {q : ℕ} {Δ : ℝ}
    (hq : 0 < q) (hΔ : 0 < Δ)
    (happ : ∃ p : ℤ, |(q : ℝ) * α - (p : ℝ)| ≤ Δ)
    (hsmall : (q : ℝ) * Δ < 1)
    (hsep : ∀ k l : ℕ, 1 ≤ k → k ≤ q → 1 ≤ l → l ≤ q → k ≠ l →
      1 / (2 * (q : ℝ)) ≤ Work.TMC16Core.fracDist ((((k : ℤ) - (l : ℤ) : ℤ) : ℝ) * α))
    (x : ℝ) {k₀ : ℕ} (hk₀ : k₀ ∈ Finset.Icc 1 q)
    (hmin : ∀ k ∈ Finset.Icc 1 q,
      |Real.sin (2 * Real.pi * (x + (k : ℝ) * α / 2))| ≥
      |Real.sin (2 * Real.pi * (x + (k₀ : ℝ) * α / 2))|) :
    |Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀,
        |Real.sin (2 * Real.pi * (x + (k : ℝ) * α / 2))|) + ((q : ℝ) - 1) * Real.log 2|
      ≤ 32 * Real.log q := by
  obtain ⟨p, hp⟩ := happ
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1 : 1 ≤ q := by omega
  rcases eq_or_lt_of_le hq1 with hq_eq | hq_gt
  · -- ## `q = 1`: the product is empty
    subst hq_eq
    have hk : k₀ = 1 := by
      have h := hk₀
      simp only [Finset.mem_Icc] at h
      omega
    subst hk
    simp
  · -- ## `q ≥ 2`
    have hq2 : 2 ≤ q := hq_gt
    have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
    set Sf : ℕ → ℝ := fun k => |Real.sin (2 * Real.pi * (x + (k : ℝ) * α / 2))| with hSf
    have hS_eq : ∀ k : ℕ, Sf k = S (2 * x + (k : ℝ) * α) := by
      intro k
      rw [hSf]
      exact block_term α x k
    -- minimality of `k₀` in terms of `nn`
    have hminA_nn : ∀ k ∈ Finset.Icc 1 q, nn (2 * x + (k : ℝ) * α) ≥ nn (2 * x + (k₀ : ℝ) * α) := by
      intro k hk
      have h := hmin k hk
      rw [block_term α x k, block_term α x k₀] at h
      exact (S_le_iff_nn_le_aux _ _).mp h
    -- separation of the `α`-grid at `k₀`
    have hsep_w : ∀ k ∈ Finset.Icc 1 q, k ≠ k₀ →
        1 / (2 * (q : ℝ)) ≤ nn (2 * x + (k : ℝ) * α - (2 * x + (k₀ : ℝ) * α)) := by
      intro k hk hkne
      have h1 := hsep k k₀ (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
        (Finset.mem_Icc.mp hk₀).1 (Finset.mem_Icc.mp hk₀).2 hkne
      have h2 : ((((k : ℤ) - (k₀ : ℤ) : ℤ) : ℝ) * α) =
          2 * x + (k : ℝ) * α - (2 * x + (k₀ : ℝ) * α) := by
        push_cast; ring
      rwa [h2, fracDist_eq_nn_aux] at h1
    have hnn_w : ∀ k ∈ Finset.Icc 1 q, k ≠ k₀ → 1 / (4 * (q : ℝ)) ≤ nn (2 * x + (k : ℝ) * α) := by
      intro k hk hkne
      have h1 := hsep_w k hk hkne
      have h2 := nn_sub_le_aux (2 * x + (k : ℝ) * α) (2 * x + (k₀ : ℝ) * α)
      have h3 := hminA_nn k hk
      have h4 : (1 : ℝ) / (4 * (q : ℝ)) = (1 / 2) * (1 / (2 * (q : ℝ))) := by
        rw [one_div_mul_one_div]; ring_nf
      have h5 : (1 / 2 : ℝ) * (1 / (2 * (q : ℝ))) ≤
          (1 / 2 : ℝ) * (nn (2 * x + (k : ℝ) * α) + nn (2 * x + (k₀ : ℝ) * α)) :=
        mul_le_mul_of_nonneg_left (le_trans h1 h2) (by norm_num)
      have h6 : (1 / 2 : ℝ) * (nn (2 * x + (k : ℝ) * α) + nn (2 * x + (k₀ : ℝ) * α))
          ≤ nn (2 * x + (k : ℝ) * α) := by linarith
      rw [h4]; linarith
    have hA_lb : ∀ k ∈ Finset.Icc 1 q, k ≠ k₀ → 1 / (2 * (q : ℝ)) ≤ Sf k := by
      intro k hk hkne
      have h1 := hnn_w k hk hkne
      have h2 := two_mul_nn_le_S_aux (2 * x + (k : ℝ) * α)
      have h3 : 2 * (1 / (4 * (q : ℝ))) = 1 / (2 * (q : ℝ)) := by
        rw [mul_one_div]; ring_nf
      rw [hS_eq k]; linarith
    -- ## crude bounds: valid for every `q ≥ 2`, used when `q ≤ 33`
    have hSf_pos : ∀ k ∈ (Finset.Icc 1 q).erase k₀, 0 < Sf k := by
      intro k hk
      have h1 := hA_lb k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)
      have h2 : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
      linarith
    have hSf_le1 : ∀ k ∈ (Finset.Icc 1 q).erase k₀, Sf k ≤ 1 := by
      intro k hk
      rw [hS_eq k]
      rw [S]
      exact Real.abs_sin_le_one _
    have hcard₀ : ((Finset.Icc 1 q).erase k₀).card = q - 1 := by
      rw [Finset.card_erase_of_mem hk₀, Nat.card_Icc]
      omega
    have hlog_ub : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀, Sf k) ≤ 0 := by
      refine Real.log_nonpos (le_of_lt (Finset.prod_pos hSf_pos)) ?_
      calc ∏ k ∈ (Finset.Icc 1 q).erase k₀, Sf k
          ≤ ∏ k ∈ (Finset.Icc 1 q).erase k₀, (1 : ℝ) :=
            Finset.prod_le_prod₀ (fun k hk => le_of_lt (hSf_pos k hk)) hSf_le1
        _ = 1 := by simp
    have hlog_lb : -(((q : ℝ) - 1) * Real.log q) ≤
        Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀, Sf k) + ((q : ℝ) - 1) * Real.log 2 := by
      have hge : (1 / (2 * (q : ℝ))) ^ ((Finset.Icc 1 q).erase k₀).card ≤
          ∏ k ∈ (Finset.Icc 1 q).erase k₀, Sf k := by
        calc (1 / (2 * (q : ℝ))) ^ ((Finset.Icc 1 q).erase k₀).card
            = ∏ k ∈ (Finset.Icc 1 q).erase k₀, (1 / (2 * (q : ℝ))) := by
              rw [Finset.prod_const]
          _ ≤ ∏ k ∈ (Finset.Icc 1 q).erase k₀, Sf k := by
              refine Finset.prod_le_prod₀ (fun k hk => by positivity) ?_
              intro k hk
              exact hA_lb k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)
      have h1 : Real.log ((1 / (2 * (q : ℝ))) ^ ((Finset.Icc 1 q).erase k₀).card) ≤
          Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀, Sf k) :=
        Real.log_le_log (by positivity) hge
      rw [Real.log_pow, hcard₀] at h1
      have h4 : Real.log (1 / (2 * (q : ℝ))) = -(Real.log 2 + Real.log q) := by
        rw [one_div, Real.log_inv, Real.log_mul (by norm_num) (ne_of_gt hqR)]
      have h5 : ((q - 1 : ℕ) : ℝ) * Real.log (1 / (2 * (q : ℝ))) =
          -(((q : ℝ) - 1) * Real.log q) - ((q : ℝ) - 1) * Real.log 2 := by
        rw [h4, Nat.cast_sub (by omega : 1 ≤ q)]
        push_cast
        ring
      rw [h5] at h1
      linarith [h1]
    have hcrude : |Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀, Sf k) + ((q : ℝ) - 1) * Real.log 2|
        ≤ ((q : ℝ) - 1) * Real.log q := by
      have hlog2le : Real.log 2 ≤ Real.log q :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hq2)
      have hql : (0 : ℝ) ≤ (q : ℝ) - 1 := by linarith [hq1R]
      have h7 : ((q : ℝ) - 1) * Real.log 2 ≤ ((q : ℝ) - 1) * Real.log q :=
        mul_le_mul_of_nonneg_left hlog2le hql
      rw [abs_le]
      exact ⟨by linarith [hlog_lb], by linarith [hlog_ub, h7]⟩
    by_cases hq33 : q ≤ 33
    · -- ## the crude case `q ≤ 33`
      have h1 : ((q : ℝ) - 1) * Real.log q ≤ 32 * Real.log q := by
        have h3 : (q : ℝ) - 1 ≤ 32 := by
          have h3' : ((q - 1 : ℕ) : ℝ) ≤ 32 := by
            exact_mod_cast (by omega : q - 1 ≤ 32)
          rw [Nat.cast_sub (show 1 ≤ q by omega), Nat.cast_one] at h3'
          exact h3'
        have h4 : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
        exact mul_le_mul_of_nonneg_right h3 h4
      calc |Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀, Sf k) + ((q : ℝ) - 1) * Real.log 2|
          ≤ ((q : ℝ) - 1) * Real.log q := hcrude
        _ ≤ 32 * Real.log q := h1
    · -- ## the delicate case `q ≥ 34`
      have hq34 : 34 ≤ q := by omega
      have hq34R : (34 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq34
      have hlog2_nonneg : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hlog2_le_one : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
      have hlogq_ge : (345 / 100 : ℝ) ≤ Real.log q := by
        have h1 : (32 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 32 ≤ q)
        have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 32) h1
        have h3 : Real.log (32 : ℝ) = 5 * Real.log 2 := by
          rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
          push_cast; ring
        rw [h3] at h2
        linarith [h2, Real.log_two_gt_d9]
      have hlogq_nonneg : (0 : ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
      have hΔlt : Δ < 1 / (q : ℝ) := by
        rw [lt_div_iff₀ hqR]
        linarith [hsmall]
      have h4Δ_half : 4 * Δ ≤ 1 / 2 := by
        have h1 : 4 * Δ < 4 / (q : ℝ) := by
          have hh := mul_lt_mul_of_pos_left hΔlt (by norm_num : (0 : ℝ) < 4)
          have hh2 : 4 * (1 / (q : ℝ)) = 4 / (q : ℝ) := by ring
          linarith [hh, hh2]
        have h2 : 4 / (q : ℝ) ≤ 1 / 2 := by
          rw [div_le_iff₀ hqR]
          linarith [hq34R]
        linarith
      -- ### the rational block
      have hcop : Nat.Coprime p.natAbs q := coprime_sep_gen hq hΔ hp hsep hsmall
      set Bf : ℕ → ℝ :=
        fun k => |Real.sin (2 * Real.pi * (x + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| with hBf
      obtain ⟨k₁, hk₁, hminB⟩ := Finset.exists_min_image (Finset.Icc 1 q) Bf ⟨k₀, hk₀⟩
      have hB_eq : ∀ k : ℕ, Bf k = S (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) := by
        intro k
        rw [hBf]
        exact block_term_rat p q x k
      have hminB_nn : ∀ k ∈ Finset.Icc 1 q,
          nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) ≥
            nn (2 * x + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ))) := by
        intro k hk
        have h := hminB k hk
        rw [hB_eq k₁, hB_eq k] at h
        exact (S_le_iff_nn_le_aux _ _).mp h
      obtain ⟨hgrid_sep, hgrid_min⟩ := Work.TMC16Core.Trig.grid_sep hq hcop x hk₁ hminB_nn
      set g : ℕ → ℝ := fun k => nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) with hg
      set f : ℕ → ℝ := fun k => nn (2 * x + (k : ℝ) * α) with hf
      have hB_lb : ∀ k ∈ Finset.Icc 1 q, k ≠ k₁ → 1 / (q : ℝ) ≤ Bf k := by
        intro k hk hkne
        have h1 := hgrid_sep k hk hkne
        have h2 := two_mul_nn_le_S_aux (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ)))
        have h3 : 2 * (1 / (2 * (q : ℝ))) = 1 / (q : ℝ) := by rw [mul_one_div]; ring_nf
        rw [hB_eq k]; linarith
      have hB_pos1 : ∀ k ∈ Finset.Icc 1 q, k ≠ k₁ → 0 < Bf k := by
        intro k hk hkne
        have h1 := hB_lb k hk hkne
        have h2 : (0 : ℝ) < 1 / (q : ℝ) := by positivity
        linarith
      have hProdB_pos : 0 < ∏ k ∈ (Finset.Icc 1 q).erase k₁, Bf k :=
        Finset.prod_pos (fun k hk =>
          hB_pos1 k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk))
      have hcard₁ : ((Finset.Icc 1 q).erase k₁).card = q - 1 := by
        rw [Finset.card_erase_of_mem hk₁, Nat.card_Icc]
        omega
      have hRatUB : ∏ k ∈ (Finset.Icc 1 q).erase k₁, Bf k ≤ 4 * (q : ℝ) ^ 2 / 2 ^ (q - 1) := by
        have h := Work.TMC16Core.Trig.rat_prod_erase_le hq hcop x hk₁ (fun k hk => by
          have h1 := hminB k hk
          simpa only [hBf] using h1)
        simpa only [hBf] using h
      have hRatLB : (q : ℝ) * (2 / Real.pi) / 2 ^ (q - 1) ≤
          ∏ k ∈ (Finset.Icc 1 q).erase k₁, Bf k := by
        have h := Work.TMC16Core.Trig.rat_prod_min_removed_v2 hq hcop x hk₁ (fun k hk => by
          have h1 := hminB k hk
          simpa only [hBf] using h1)
        simpa only [hBf] using h
      have hprod2B : ∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k)
          = 2 ^ (q - 1) * ∏ k ∈ (Finset.Icc 1 q).erase k₁, Bf k := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, hcard₁]
      have hlog2B_eq : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))
          = ((q : ℝ) - 1) * Real.log 2
            + Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, Bf k) := by
        rw [hprod2B, Real.log_mul (by positivity) (ne_of_gt hProdB_pos), Real.log_pow]
        rw [Nat.cast_sub (by omega : 1 ≤ q)]
        push_cast
        ring
      have hlog2B_abs : |Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))|
          ≤ 2 * Real.log q + 2 := by
        have hpos : 0 < ∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k) :=
          Finset.prod_pos (fun k hk => by
            have h1 := hB_pos1 k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)
            linarith)
        have hub : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))
            ≤ 2 * Real.log q + 2 := by
          have h2 : ∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k) ≤ 4 * (q : ℝ) ^ 2 := by
            rw [hprod2B]
            have hp : (0 : ℝ) < 2 ^ (q - 1) := by positivity
            calc 2 ^ (q - 1) * ∏ k ∈ (Finset.Icc 1 q).erase k₁, Bf k
                ≤ 2 ^ (q - 1) * (4 * (q : ℝ) ^ 2 / 2 ^ (q - 1)) :=
                  mul_le_mul_of_nonneg_left hRatUB (le_of_lt hp)
              _ = 4 * (q : ℝ) ^ 2 := by field_simp
          calc Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))
              ≤ Real.log (4 * (q : ℝ) ^ 2) := Real.log_le_log hpos h2
            _ = Real.log 4 + 2 * Real.log q := by
                rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
                push_cast; ring
            _ ≤ 2 * Real.log q + 2 := by linarith [log_four_le_two]
        have hlb : -(2 * Real.log q + 2) ≤
            Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k)) := by
          have h2 : 2 * (q : ℝ) / Real.pi ≤ ∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k) := by
            rw [hprod2B]
            have hp : (0 : ℝ) < 2 ^ (q - 1) := by positivity
            calc 2 * (q : ℝ) / Real.pi
                = 2 ^ (q - 1) * ((q : ℝ) * (2 / Real.pi) / 2 ^ (q - 1)) := by field_simp
              _ ≤ 2 ^ (q - 1) * ∏ k ∈ (Finset.Icc 1 q).erase k₁, Bf k :=
                  mul_le_mul_of_nonneg_left hRatLB (le_of_lt hp)
          have h3 : Real.log (2 * (q : ℝ) / Real.pi)
              = Real.log 2 + Real.log q - Real.log Real.pi := by
            rw [Real.log_div (by positivity) (ne_of_gt Real.pi_pos),
                Real.log_mul (by norm_num) (ne_of_gt hqR)]
          have h4 : Real.log Real.pi ≤ 2 := by
            have hh : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log Real.pi_pos Real.pi_le_four
            linarith [hh, log_four_le_two]
          calc -(2 * Real.log q + 2) ≤ Real.log 2 + Real.log q - Real.log Real.pi := by
                linarith [h4, hlogq_nonneg, hlog2_nonneg]
            _ = Real.log (2 * (q : ℝ) / Real.pi) := h3.symm
            _ ≤ Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k)) :=
                Real.log_le_log (by positivity) h2
        rw [abs_le]
        exact ⟨hlb, hub⟩
      -- ### the harmonic sum over the rational grid
      have hcard_bound : ∀ γ : ℝ, 0 < γ →
          ((((Finset.Icc 1 q).erase k₁).filter (fun k => g k < γ)).card : ℝ)
            ≤ 2 * (q : ℝ) * γ + 2 := by
        intro γ hγ
        by_cases hγ2 : γ ≤ 1 / 2
        · have h := grid_card_bad hq hcop x γ (le_of_lt hγ) hγ2 hk₁
          have h' : ((((Finset.Icc 1 q).erase k₁).filter (fun k => g k < γ)).card : ℝ)
              ≤ 2 * γ * (q : ℝ) + 2 := by
            simpa only [hg] using h
          linarith [h']
        · have hγ2' : 1 / 2 < γ := not_le.mp hγ2
          have h1 : ((((Finset.Icc 1 q).erase k₁).filter (fun k => g k < γ)).card : ℝ)
              ≤ ((q - 1 : ℕ) : ℝ) := by
            have hh := Finset.card_filter_le ((Finset.Icc 1 q).erase k₁) (fun k => g k < γ)
            rw [hcard₁] at hh
            exact_mod_cast hh
          have h3 : ((q - 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) * γ + 2 := by
            rw [Nat.cast_sub (by omega : 1 ≤ q)]
            push_cast
            nlinarith [hγ2', hqR]
          linarith [h1, h3]
      have hHarm := inv_sum_card_filter ((Finset.Icc 1 q).erase k₁) g
        (A := 2 * (q : ℝ)) (B := 2) (c := 1 / (2 * (q : ℝ)))
        (by positivity) (by positivity)
        (fun k hk => hgrid_sep k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk))
        hcard_bound
      have hHarm' : ∑ k ∈ (Finset.Icc 1 q).erase k₁, (g k)⁻¹
          ≤ 2 * (q : ℝ) * Real.log q + 8 * (q : ℝ) := by
        have h2 : ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
        rw [h2, hcard₁] at hHarm
        have h3 : (3 : ℝ) / (1 / (2 * (q : ℝ))) = 6 * (q : ℝ) := by
          field_simp
          ring
        rw [h3] at hHarm
        have h4 : Real.log (((q - 1 : ℕ)) : ℝ) ≤ Real.log (q : ℝ) := by
          apply Real.log_le_log
          · rw [Nat.cast_sub (by omega : 1 ≤ q)]; push_cast; linarith [hqR]
          · rw [Nat.cast_sub (by omega : 1 ≤ q)]; push_cast; linarith
        have h5 : 2 * (q : ℝ) * (1 + Real.log (((q - 1 : ℕ)) : ℝ))
            ≤ 2 * (q : ℝ) * (1 + Real.log (q : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith [h4]) (by positivity)
        linarith [hHarm, h5]
      -- ### comparison of the two blocks
      have hab : ∀ k ∈ Finset.Icc 1 q, |f k - g k| ≤ Δ := by
        intro k hk
        have h1 : |(2 * x + (k : ℝ) * α) - (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ)))| ≤ Δ := by
          have h3 : (2 * x + (k : ℝ) * α) - (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ)))
              = (k : ℝ) * (α - (p : ℝ) / (q : ℝ)) := by ring
          rw [h3, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
          have h4 : (k : ℝ) ≤ (q : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).2
          have h5 : |α - (p : ℝ) / (q : ℝ)| * (q : ℝ) = |(q : ℝ) * α - (p : ℝ)| := by
            calc |α - (p : ℝ) / (q : ℝ)| * (q : ℝ)
                = |α - (p : ℝ) / (q : ℝ)| * |(q : ℝ)| := by rw [abs_of_nonneg hqR.le]
              _ = |(α - (p : ℝ) / (q : ℝ)) * (q : ℝ)| := by rw [abs_mul]
              _ = |(q : ℝ) * α - (p : ℝ)| := by
                  congr 1
                  rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hqR)]
                  ring
          nlinarith [h4, h5, hp, abs_nonneg (α - (p : ℝ) / (q : ℝ))]
        have h2 : |f k - g k| ≤
            |(2 * x + (k : ℝ) * α) - (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ)))| := by
          have h7 := nn_sub_le_abs (2 * x + (k : ℝ) * α) (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ)))
          have h8 := nn_sub_le_abs (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) (2 * x + (k : ℝ) * α)
          simp only [hf, hg]
          rw [abs_sub_le_iff]
          constructor
          · linarith [h7]
          · rw [abs_sub_comm]
            linarith [h8]
        linarith
      set T : Finset ℕ := ((Finset.Icc 1 q).erase k₀).erase k₁ with hT
      have hTmem : ∀ k ∈ T, k ∈ Finset.Icc 1 q ∧ k ≠ k₀ ∧ k ≠ k₁ := by
        intro k hk
        have hk' : k ∈ ((Finset.Icc 1 q).erase k₀).erase k₁ := hT ▸ hk
        exact ⟨Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hk'),
          Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk'), Finset.ne_of_mem_erase hk'⟩
      have hTsub : T ⊆ (Finset.Icc 1 q).erase k₁ := by
        intro k hk
        obtain ⟨hkI, hkne₀, hkne₁⟩ := hTmem k hk
        exact Finset.mem_erase.mpr ⟨hkne₁, hkI⟩
      have hterm : ∀ k ∈ T, |Real.log (Sf k) - Real.log (Bf k)| ≤ Δ / min (f k) (g k) := by
        intro k hk
        obtain ⟨hkI, hkne₀, hkne₁⟩ := hTmem k hk
        have hf0 : 0 < f k :=
          lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (4 * (q : ℝ))) (hnn_w k hkI hkne₀)
        have hf2 : f k ≤ 1 / 2 := by rw [hf]; exact nn_le_half _
        have hg0 : 0 < g k :=
          lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (2 * (q : ℝ))) (hgrid_sep k hkI hkne₁)
        have hg2 : g k ≤ 1 / 2 := by rw [hg]; exact nn_le_half _
        have h := abs_log_sin_sub_le hf0 hg0 hf2 hg2
        have e1 : Sf k = Real.sin (Real.pi * f k) := by rw [hS_eq k, S_eq_sin_nn]
        have e2 : Bf k = Real.sin (Real.pi * g k) := by rw [hB_eq k, S_eq_sin_nn]
        refine le_trans ?_ (div_le_div_of_nonneg_right (hab k hkI) (le_of_lt (lt_min hf0 hg0)))
        rwa [e1, e2]
      have hgood : ∑ k ∈ T.filter (fun k => 4 * Δ ≤ g k),
            |Real.log (Sf k) - Real.log (Bf k)|
          ≤ (4 / 3) * Δ * (∑ k ∈ (Finset.Icc 1 q).erase k₁, (g k)⁻¹) := by
        have hstep : ∑ k ∈ T.filter (fun k => 4 * Δ ≤ g k),
              |Real.log (Sf k) - Real.log (Bf k)|
            ≤ ∑ k ∈ T.filter (fun k => 4 * Δ ≤ g k), (4 / 3) * Δ * (g k)⁻¹ := by
          refine Finset.sum_le_sum (fun k hk => ?_)
          have hkT : k ∈ T := Finset.mem_of_mem_filter k hk
          obtain ⟨hkI, hkne₀, hkne₁⟩ := hTmem k hkT
          have h4d : 4 * Δ ≤ g k := (Finset.mem_filter.mp hk).2
          have hg0 : 0 < g k :=
            lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (2 * (q : ℝ)))
              (hgrid_sep k hkI hkne₁)
          have hf0 : 0 < f k :=
            lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (4 * (q : ℝ))) (hnn_w k hkI hkne₀)
          have habk := hab k hkI
          have hmin_ge : (3 / 4) * g k ≤ min (f k) (g k) := by
            have h1 : g k - Δ ≤ f k := by linarith [(abs_le.mp habk).1]
            exact le_min (by linarith) (by linarith)
          have hminpos : 0 < min (f k) (g k) := lt_min hf0 hg0
          have hfin : Δ / min (f k) (g k) ≤ (4 / 3) * Δ * (g k)⁻¹ := by
            rw [← div_eq_mul_inv]
            rw [div_le_div_iff₀ hminpos hg0]
            have h1 : g k ≤ (4 / 3) * min (f k) (g k) := by linarith [hmin_ge]
            nlinarith [h1, le_of_lt hΔ]
          exact le_trans (hterm k hkT) hfin
        calc ∑ k ∈ T.filter (fun k => 4 * Δ ≤ g k), |Real.log (Sf k) - Real.log (Bf k)|
            ≤ ∑ k ∈ T.filter (fun k => 4 * Δ ≤ g k), (4 / 3) * Δ * (g k)⁻¹ := hstep
          _ = (4 / 3) * Δ * ∑ k ∈ T.filter (fun k => 4 * Δ ≤ g k), (g k)⁻¹ := by
              rw [Finset.mul_sum]
          _ ≤ (4 / 3) * Δ * ∑ k ∈ (Finset.Icc 1 q).erase k₁, (g k)⁻¹ := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro k hk
                exact hTsub (Finset.mem_of_mem_filter k hk)
              · intro k hk _
                have hk1 : k ∈ Finset.Icc 1 q := Finset.mem_of_mem_erase hk
                have hk2 : k ≠ k₁ := Finset.ne_of_mem_erase hk
                have h4 := hgrid_sep k hk1 hk2
                have h5 : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
                exact inv_nonneg.mpr (by linarith)
      have hbad_card : ((T.filter (fun k => ¬ (4 * Δ ≤ g k))).card : ℝ)
          ≤ 2 * (4 * Δ) * (q : ℝ) + 2 := by
        have hsub : T.filter (fun k => ¬ (4 * Δ ≤ g k))
            ⊆ ((Finset.Icc 1 q).erase k₁).filter
                (fun k : ℕ => nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) < 4 * Δ) := by
          intro k hk
          have hkT : k ∈ T := Finset.mem_of_mem_filter k hk
          obtain ⟨hkI, hkne₀, hkne₁⟩ := hTmem k hkT
          have h2 : ¬ (4 * Δ ≤ g k) := (Finset.mem_filter.mp hk).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hkne₁, hkI⟩, ?_⟩
          simpa only [hg] using not_le.mp h2
        have hcardR : ((T.filter (fun k => ¬ (4 * Δ ≤ g k))).card : ℝ)
            ≤ ((((Finset.Icc 1 q).erase k₁).filter
                (fun k : ℕ => nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) < 4 * Δ)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
        have h3 := grid_card_bad hq hcop x (4 * Δ) (by positivity) h4Δ_half hk₁
        linarith [hcardR, h3]
      have hbad : ∑ k ∈ T.filter (fun k => ¬ (4 * Δ ≤ g k)),
            |Real.log (Sf k) - Real.log (Bf k)| ≤ 40 := by
        have h1 : ∀ k ∈ T.filter (fun k => ¬ (4 * Δ ≤ g k)),
            |Real.log (Sf k) - Real.log (Bf k)| ≤ 4 := by
          intro k hk
          have hkT : k ∈ T := Finset.mem_of_mem_filter k hk
          obtain ⟨hkI, hkne₀, hkne₁⟩ := hTmem k hkT
          have h1 : 1 / (4 * (q : ℝ)) ≤ f k := hnn_w k hkI hkne₀
          have h2 : 1 / (2 * (q : ℝ)) ≤ g k := hgrid_sep k hkI hkne₁
          have hmin_ge : 1 / (4 * (q : ℝ)) ≤ min (f k) (g k) :=
            le_min h1 (by
              have h2b : (1 : ℝ) / (4 * (q : ℝ)) ≤ 1 / (2 * (q : ℝ)) := by
                rw [div_le_div_iff₀ (by positivity) (by positivity)]
                linarith [hqR]
              linarith [h2, h2b])
          calc |Real.log (Sf k) - Real.log (Bf k)| ≤ Δ / min (f k) (g k) := hterm k hkT
            _ ≤ Δ / (1 / (4 * (q : ℝ))) :=
                div_le_div_of_nonneg_left (le_of_lt hΔ) (by positivity) hmin_ge
            _ = 4 * (q : ℝ) * Δ := by field_simp
            _ ≤ 4 := by nlinarith [hsmall]
        have hsum : ∑ k ∈ T.filter (fun k => ¬ (4 * Δ ≤ g k)),
              |Real.log (Sf k) - Real.log (Bf k)|
            ≤ ∑ k ∈ T.filter (fun k => ¬ (4 * Δ ≤ g k)), (4 : ℝ) := Finset.sum_le_sum h1
        have hcard4 : ∑ k ∈ T.filter (fun k => ¬ (4 * Δ ≤ g k)), (4 : ℝ)
            = ((T.filter (fun k => ¬ (4 * Δ ≤ g k))).card : ℝ) * 4 := by
          rw [Finset.sum_const, nsmul_eq_mul]
        rw [hcard4] at hsum
        have h3 : ((T.filter (fun k => ¬ (4 * Δ ≤ g k))).card : ℝ) ≤ 8 * (q : ℝ) * Δ + 2 := by
          linarith [hbad_card]
        have h4 : ((T.filter (fun k => ¬ (4 * Δ ≤ g k))).card : ℝ) * 4
            ≤ (8 * (q : ℝ) * Δ + 2) * 4 := mul_le_mul_of_nonneg_right h3 (by norm_num)
        have h5 : (8 * (q : ℝ) * Δ + 2) * 4 ≤ 40 := by
          have h6 : (q : ℝ) * Δ ≤ 1 := by linarith [hsmall]
          linarith [h6]
        linarith [hsum, h4, h5]
      have hcmp : |∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k))|
          ≤ (8 / 3) * Real.log q + 51 := by
        have h1 : |∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k))|
            ≤ ∑ k ∈ T, |Real.log (Sf k) - Real.log (Bf k)| := Finset.abs_sum_le_sum_abs _ _
        have hsplit := Finset.sum_filter_add_sum_filter_not T (fun k => 4 * Δ ≤ g k)
          (fun k => |Real.log (Sf k) - Real.log (Bf k)|)
        have hg' : ∑ k ∈ T.filter (fun k => 4 * Δ ≤ g k), |Real.log (Sf k) - Real.log (Bf k)|
            ≤ (4 / 3) * Δ * (2 * (q : ℝ) * Real.log q + 8 * (q : ℝ)) :=
          le_trans hgood (mul_le_mul_of_nonneg_left hHarm' (by positivity))
        have hnum : (4 / 3) * Δ * (2 * (q : ℝ) * Real.log q + 8 * (q : ℝ)) + 40
            ≤ (8 / 3) * Real.log q + 51 := by
          have h3 : (q : ℝ) * Δ ≤ 1 := by linarith [hsmall]
          have h5 : (0 : ℝ) ≤ 2 * Real.log q + 8 := by linarith [hlogq_nonneg]
          have h4 : (q : ℝ) * Δ * (2 * Real.log q + 8) ≤ 2 * Real.log q + 8 := by
            calc (q : ℝ) * Δ * (2 * Real.log q + 8) ≤ 1 * (2 * Real.log q + 8) :=
                  mul_le_mul_of_nonneg_right h3 h5
              _ = 2 * Real.log q + 8 := by ring
          have h6 : (4 / 3) * Δ * (2 * (q : ℝ) * Real.log q + 8 * (q : ℝ))
              = (4 / 3) * ((q : ℝ) * Δ * (2 * Real.log q + 8)) := by ring
          have h7 := mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 4 / 3)
          rw [h6]
          linarith [h7]
        calc |∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k))|
            ≤ ∑ k ∈ T, |Real.log (Sf k) - Real.log (Bf k)| := h1
          _ = ∑ k ∈ T.filter (fun k => 4 * Δ ≤ g k), |Real.log (Sf k) - Real.log (Bf k)|
              + ∑ k ∈ T.filter (fun k => ¬ (4 * Δ ≤ g k)), |Real.log (Sf k) - Real.log (Bf k)| :=
              hsplit.symm
          _ ≤ (4 / 3) * Δ * (2 * (q : ℝ) * Real.log q + 8 * (q : ℝ)) + 40 :=
              add_le_add hg' hbad
          _ ≤ (8 / 3) * Real.log q + 51 := hnum
      -- ### the log of the product of the doubled factors
      have hlogSf2 : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀, (2 * Sf k))
          = Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀, Sf k) + ((q : ℝ) - 1) * Real.log 2 := by
        have hpos : 0 < ∏ k ∈ (Finset.Icc 1 q).erase k₀, Sf k := Finset.prod_pos hSf_pos
        have h : ∏ k ∈ (Finset.Icc 1 q).erase k₀, (2 * Sf k)
            = 2 ^ (q - 1) * ∏ k ∈ (Finset.Icc 1 q).erase k₀, Sf k := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, hcard₀]
        rw [h, Real.log_mul (by positivity) (ne_of_gt hpos), Real.log_pow]
        rw [Nat.cast_sub (by omega : 1 ≤ q)]
        push_cast
        ring
      -- ### case A: the two minimisers agree
      by_cases hkk : k₁ = k₀
      · have h1 : (Finset.Icc 1 q).erase k₁ = (Finset.Icc 1 q).erase k₀ := by rw [hkk]
        have h2 : T = (Finset.Icc 1 q).erase k₀ := by rw [hT, hkk, Finset.erase_idem]
        have hid : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀, (2 * Sf k))
            = (∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k)))
              + Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k)) := by
          have hlogA : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀, (2 * Sf k))
              = ∑ k ∈ (Finset.Icc 1 q).erase k₀, Real.log (2 * Sf k) :=
            Real.log_prod (fun k hk => ne_of_gt (by
              have h3 := hSf_pos k hk
              linarith))
          have hlogB : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))
              = ∑ k ∈ (Finset.Icc 1 q).erase k₀, Real.log (2 * Bf k) := by
            rw [h1]
            exact Real.log_prod (fun k hk => ne_of_gt (by
              have h3 : k ∈ Finset.Icc 1 q := Finset.mem_of_mem_erase hk
              have h4 : k ≠ k₁ := by rw [hkk]; exact Finset.ne_of_mem_erase hk
              have h5 := hB_pos1 k h3 h4
              linarith))
          have hpt : ∀ k ∈ (Finset.Icc 1 q).erase k₀,
              Real.log (Sf k) - Real.log (Bf k)
                = Real.log (2 * Sf k) - Real.log (2 * Bf k) := by
            intro k hk
            have h3 : k ∈ Finset.Icc 1 q := Finset.mem_of_mem_erase hk
            have h4 : k ≠ k₁ := by rw [hkk]; exact Finset.ne_of_mem_erase hk
            rw [Real.log_mul (by norm_num) (ne_of_gt (hSf_pos k hk)),
                Real.log_mul (by norm_num) (ne_of_gt (hB_pos1 k h3 h4))]
            ring
          have hstep : ∑ k ∈ (Finset.Icc 1 q).erase k₀, Real.log (2 * Sf k)
              = (∑ k ∈ (Finset.Icc 1 q).erase k₀,
                  (Real.log (Sf k) - Real.log (Bf k)))
                + ∑ k ∈ (Finset.Icc 1 q).erase k₀, Real.log (2 * Bf k) := by
            have hs : ∑ k ∈ (Finset.Icc 1 q).erase k₀,
                (Real.log (2 * Sf k) - Real.log (2 * Bf k))
                = ∑ k ∈ (Finset.Icc 1 q).erase k₀,
                    (Real.log (Sf k) - Real.log (Bf k)) :=
              Finset.sum_congr rfl (fun k hk => (hpt k hk).symm)
            have hs2 : ∑ k ∈ (Finset.Icc 1 q).erase k₀,
                (Real.log (2 * Sf k) - Real.log (2 * Bf k))
                = (∑ k ∈ (Finset.Icc 1 q).erase k₀, Real.log (2 * Sf k))
                  - ∑ k ∈ (Finset.Icc 1 q).erase k₀, Real.log (2 * Bf k) :=
              Finset.sum_sub_distrib _ _
            linarith [hs, hs2]
          calc Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀, (2 * Sf k))
              = ∑ k ∈ (Finset.Icc 1 q).erase k₀, Real.log (2 * Sf k) := hlogA
            _ = (∑ k ∈ (Finset.Icc 1 q).erase k₀,
                  (Real.log (Sf k) - Real.log (Bf k)))
                + ∑ k ∈ (Finset.Icc 1 q).erase k₀, Real.log (2 * Bf k) := hstep
            _ = (∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k)))
                + Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k)) := by
                rw [← hlogB, ← h2]
        have h3 : |(∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k)))
              + Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))|
            ≤ (8 / 3) * Real.log q + 51 + (2 * Real.log q + 2) := by
          have hh : |(∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k)))
                + Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))|
              ≤ |∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k))|
                + |Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))| :=
            abs_add_le _ _
          linarith [hh, hcmp, hlog2B_abs]
        have h4 : (8 / 3) * Real.log q + 51 + (2 * Real.log q + 2) ≤ 32 * Real.log q := by
          linarith [hlogq_ge]
        rw [← hlogSf2, hid]
        linarith [h3, h4]
      · -- ### case B: the two minimisers differ
        have hkkne : k₁ ≠ k₀ := hkk
        have hk₀ne : k₀ ≠ k₁ := fun h => hkk h.symm
        have hk₁_mem : k₁ ∈ (Finset.Icc 1 q).erase k₀ := Finset.mem_erase.mpr ⟨hkkne, hk₁⟩
        have hk₀_mem : k₀ ∈ (Finset.Icc 1 q).erase k₁ := Finset.mem_erase.mpr ⟨hk₀ne, hk₀⟩
        have hTeq : T = ((Finset.Icc 1 q).erase k₁).erase k₀ := by
          rw [hT]
          ext t
          simp only [Finset.mem_erase]
          tauto
        have hp1 : (∏ k ∈ ((Finset.Icc 1 q).erase k₀).erase k₁, (2 * Sf k)) * (2 * Sf k₁)
            = ∏ k ∈ (Finset.Icc 1 q).erase k₀, (2 * Sf k) :=
          Finset.prod_erase_mul _ _ hk₁_mem
        have hp2 : (∏ k ∈ ((Finset.Icc 1 q).erase k₁).erase k₀, (2 * Bf k)) * (2 * Bf k₀)
            = ∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k) :=
          Finset.prod_erase_mul _ _ hk₀_mem
        have hposS : 0 < ∏ k ∈ ((Finset.Icc 1 q).erase k₀).erase k₁, (2 * Sf k) :=
          Finset.prod_pos (fun k hk => by
            have h1 : k ∈ (Finset.Icc 1 q).erase k₀ := Finset.mem_of_mem_erase hk
            have h2 := hSf_pos k h1
            linarith)
        have hposB : 0 < ∏ k ∈ ((Finset.Icc 1 q).erase k₁).erase k₀, (2 * Bf k) :=
          Finset.prod_pos (fun k hk => by
            have h1 : k ∈ (Finset.Icc 1 q).erase k₁ := Finset.mem_of_mem_erase hk
            have h2 := hB_pos1 k (Finset.mem_of_mem_erase h1) (Finset.ne_of_mem_erase h1)
            linarith)
        have hposS1 : 0 < 2 * Sf k₁ := by
          have h1 := hA_lb k₁ hk₁ hkkne
          have h2 : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
          linarith
        have hposB0 : 0 < 2 * Bf k₀ := by
          have h1 := hB_lb k₀ hk₀ hk₀ne
          have h2 : (0 : ℝ) < 1 / (q : ℝ) := by positivity
          linarith
        have hidB : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀, (2 * Sf k))
            = (∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k)))
              + Real.log (2 * Sf k₁) - Real.log (2 * Bf k₀)
              + Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k)) := by
          have hposST : 0 < ∏ k ∈ T, (2 * Sf k) :=
            Finset.prod_pos (fun k hk => by
              obtain ⟨hkI, hkne₀, _⟩ := hTmem k hk
              have h1 := hA_lb k hkI hkne₀
              have h2 : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
              linarith)
          have hposBT : 0 < ∏ k ∈ T, (2 * Bf k) :=
            Finset.prod_pos (fun k hk => by
              obtain ⟨hkI, _, hkne₁⟩ := hTmem k hk
              have h1 := hB_lb k hkI hkne₁
              have h2 : (0 : ℝ) < 1 / (q : ℝ) := by positivity
              linarith)
          have e : ((Finset.Icc 1 q).erase k₀).erase k₁ = T := hT.symm
          have hp1' : (∏ k ∈ T, (2 * Sf k)) * (2 * Sf k₁)
              = ∏ k ∈ (Finset.Icc 1 q).erase k₀, (2 * Sf k) := by
            rw [← e]
            exact hp1
          have hp2' : (∏ k ∈ T, (2 * Bf k)) * (2 * Bf k₀)
              = ∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k) := by
            rw [hTeq]
            exact hp2
          have hlogST : Real.log (∏ k ∈ T, (2 * Sf k)) = ∑ k ∈ T, Real.log (2 * Sf k) :=
            Real.log_prod (fun k hk => ne_of_gt (by
              obtain ⟨hkI, hkne₀, _⟩ := hTmem k hk
              have h1 := hA_lb k hkI hkne₀
              have h2 : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
              linarith))
          have hlogBT : Real.log (∏ k ∈ T, (2 * Bf k)) = ∑ k ∈ T, Real.log (2 * Bf k) :=
            Real.log_prod (fun k hk => ne_of_gt (by
              obtain ⟨hkI, _, hkne₁⟩ := hTmem k hk
              have h1 := hB_lb k hkI hkne₁
              have h2 : (0 : ℝ) < 1 / (q : ℝ) := by positivity
              linarith))
          have hptT : ∀ k ∈ T, Real.log (2 * Sf k) - Real.log (2 * Bf k)
                = Real.log (Sf k) - Real.log (Bf k) := by
            intro k hk
            obtain ⟨hkI, hkne₀, hkne₁⟩ := hTmem k hk
            rw [Real.log_mul (by norm_num) (ne_of_gt (by
                  have h1 := hA_lb k hkI hkne₀
                  have h2 : (0 : ℝ) < 1 / (2 * (q : ℝ)) := by positivity
                  linarith)),
                Real.log_mul (by norm_num) (ne_of_gt (by
                  have h1 := hB_lb k hkI hkne₁
                  have h2 : (0 : ℝ) < 1 / (q : ℝ) := by positivity
                  linarith))]
            ring
          have hstep1 : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀, (2 * Sf k))
              = Real.log (∏ k ∈ T, (2 * Sf k)) + Real.log (2 * Sf k₁) := by
            rw [← hp1', Real.log_mul (ne_of_gt hposST) (ne_of_gt hposS1)]
          have hstep2 : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))
              = Real.log (∏ k ∈ T, (2 * Bf k)) + Real.log (2 * Bf k₀) := by
            rw [← hp2', Real.log_mul (ne_of_gt hposBT) (ne_of_gt hposB0)]
          have hstep2' : Real.log (∏ k ∈ T, (2 * Bf k))
              = Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))
                - Real.log (2 * Bf k₀) := by
            rw [hstep2]
            ring
          have hstep3 : ∑ k ∈ T, Real.log (2 * Sf k)
              = (∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k)))
                + ∑ k ∈ T, Real.log (2 * Bf k) := by
            have hs : ∑ k ∈ T, (Real.log (2 * Sf k) - Real.log (2 * Bf k))
                = ∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k)) :=
              Finset.sum_congr rfl hptT
            have hs2 : ∑ k ∈ T, (Real.log (2 * Sf k) - Real.log (2 * Bf k))
                = (∑ k ∈ T, Real.log (2 * Sf k)) - ∑ k ∈ T, Real.log (2 * Bf k) :=
              Finset.sum_sub_distrib _ _
            linarith [hs, hs2]
          calc Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀, (2 * Sf k))
              = Real.log (∏ k ∈ T, (2 * Sf k)) + Real.log (2 * Sf k₁) := hstep1
            _ = (∑ k ∈ T, Real.log (2 * Sf k)) + Real.log (2 * Sf k₁) := by rw [hlogST]
            _ = ((∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k)))
                  + ∑ k ∈ T, Real.log (2 * Bf k)) + Real.log (2 * Sf k₁) := by rw [hstep3]
            _ = ((∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k)))
                  + Real.log (∏ k ∈ T, (2 * Bf k))) + Real.log (2 * Sf k₁) := by rw [← hlogBT]
            _ = ((∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k)))
                  + (Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))
                      - Real.log (2 * Bf k₀))) + Real.log (2 * Sf k₁) := by rw [hstep2']
            _ = (∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k)))
                + Real.log (2 * Sf k₁) - Real.log (2 * Bf k₀)
                + Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k)) := by ring
        have hA1 : |Real.log (2 * Sf k₁)| ≤ Real.log q + 1 := by
          have hpos : 0 < 2 * Sf k₁ := hposS1
          have hlo : 1 / (q : ℝ) ≤ 2 * Sf k₁ := by
            have h1 := hA_lb k₁ hk₁ hkkne
            have h2 : 2 * (1 / (2 * (q : ℝ))) = 1 / (q : ℝ) := by rw [mul_one_div]; ring_nf
            linarith
          have hhi : 2 * Sf k₁ ≤ 2 := by
            have h1 : Sf k₁ ≤ 1 := hSf_le1 k₁ (Finset.mem_erase.mpr ⟨hkkne, hk₁⟩)
            linarith
          rw [abs_le]
          constructor
          · have hh := Real.log_le_log (by positivity : (0 : ℝ) < 1 / (q : ℝ)) hlo
            rw [one_div, Real.log_inv] at hh
            linarith [hh, hlogq_nonneg]
          · have hh := Real.log_le_log hpos hhi
            linarith [hh, hlog2_le_one, hlogq_nonneg]
        have hB0 : |Real.log (2 * Bf k₀)| ≤ Real.log q + 1 := by
          have hpos : 0 < 2 * Bf k₀ := hposB0
          have hlo : 1 / (q : ℝ) ≤ 2 * Bf k₀ := by
            have h1 := hB_lb k₀ hk₀ hk₀ne
            have h3 : 1 / (q : ℝ) ≤ 2 * (1 / (q : ℝ)) := by
              have h4 : (0 : ℝ) < 1 / (q : ℝ) := by positivity
              linarith
            linarith
          have hhi : 2 * Bf k₀ ≤ 2 := by
            have h1 : Bf k₀ ≤ 1 := by
              rw [hB_eq k₀, S]
              exact Real.abs_sin_le_one _
            linarith
          rw [abs_le]
          constructor
          · have hh := Real.log_le_log (by positivity : (0 : ℝ) < 1 / (q : ℝ)) hlo
            rw [one_div, Real.log_inv] at hh
            linarith [hh, hlogq_nonneg]
          · have hh := Real.log_le_log hpos hhi
            linarith [hh, hlog2_le_one, hlogq_nonneg]
        have h3 : |(∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k))) + Real.log (2 * Sf k₁)
              - Real.log (2 * Bf k₀) + Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))|
            ≤ (8 / 3) * Real.log q + 51 + (Real.log q + 1) + (Real.log q + 1)
              + (2 * Real.log q + 2) := by
          have hh : |(∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k))) + Real.log (2 * Sf k₁)
                - Real.log (2 * Bf k₀) + Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))|
              ≤ |∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k))| + |Real.log (2 * Sf k₁)|
                + |Real.log (2 * Bf k₀)|
                + |Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))| := by
            have a1 : |(∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k))) + Real.log (2 * Sf k₁)
                  - Real.log (2 * Bf k₀)
                  + Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))|
                ≤ |(∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k))) + Real.log (2 * Sf k₁)
                    - Real.log (2 * Bf k₀)|
                  + |Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))| :=
              abs_add_le _ _
            have a2 : |(∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k))) + Real.log (2 * Sf k₁)
                    - Real.log (2 * Bf k₀)|
                ≤ |(∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k))) + Real.log (2 * Sf k₁)|
                  + |Real.log (2 * Bf k₀)| := by
              have h := abs_add_le ((∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k)))
                + Real.log (2 * Sf k₁)) (-(Real.log (2 * Bf k₀)))
              rw [abs_neg] at h
              simpa only [sub_eq_add_neg] using h
            have a3 : |(∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k))) + Real.log (2 * Sf k₁)|
                ≤ |∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k))| + |Real.log (2 * Sf k₁)| :=
              abs_add_le _ _
            linarith [a1, a2, a3]
          linarith [hh, hcmp, hA1, hB0, hlog2B_abs]
        have h4 : (8 / 3) * Real.log q + 51 + (Real.log q + 1) + (Real.log q + 1)
              + (2 * Real.log q + 2) ≤ 32 * Real.log q := by
          linarith [hlogq_ge]
        rw [← hlogSf2, hidB]
        linarith [h3, h4]

end Work.TMC16Core.Core

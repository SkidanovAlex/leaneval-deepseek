import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Core.irrat_block_gen
import Submission.Work.TMC16Core.Core.grid_card_bad
import Submission.Work.TMC16Core.Core.inv_sum_card_filter
import Submission.Work.TMC16Core.Core.abs_log_sin_sub_le
import Submission.Work.TMC16Core.Trig.grid_sep
import Submission.Work.TMC16Core.Trig.rat_prod_erase_le
import Submission.Work.TMC16Core.Trig.rat_prod_min_removed_v2

set_option maxHeartbeats 1600000

namespace Work.TMC16Core.Trig

open Finset
open Work.TMC16Core.Basic

/-!
# The shifted block estimate in the relaxed regime (`shift_block_relaxed`)

`shift_block_gen` with the two numerical hypotheses relaxed: the smallness hypothesis
`q (Δ + A Δr) ≤ 1` becomes `q (Δ + A Δr) ≤ 3/2`, and the separation of the shifted sites
becomes `1/(5q)` (instead of `1/(2q)`), at the price of the constant `70 log q` in place of
`100 log q`.

The shifted block is compared with the rational block `k ↦ k p/q`, whose one-factor-removed
product is estimated by `rat_prod_erase_le` / `rat_prod_min_removed_v2`.  The separation of
the shifted sites enters through `nn (v k) ≥ 1/(10 q)` and `S (v k) ≥ 1/(5 q)`; the harmonic
sum over the shifted sites is then bounded from these lower bounds together with the
counting bound `grid_card_bad` for the rational grid.
-/

/-- `|nn a - nn b| ≤ nn (a - b)`: the distance to `ℤ` is `1`-Lipschitz in the `nn` distance. -/
private lemma nn_abs_sub_le (a b : ℝ) : |nn a - nn b| ≤ nn (a - b) := by
  have key : ∀ x y : ℝ, nn x ≤ nn (x - y) + nn y := by
    intro x y
    have h := nn_le_abs_sub_intCast x (round y + round (x - y))
    have e : x - (((round y + round (x - y) : ℤ)) : ℝ)
        = ((x - y) - ((round (x - y) : ℤ) : ℝ)) + (y - ((round y : ℤ) : ℝ)) := by
      push_cast; ring
    calc nn x ≤ |x - (((round y + round (x - y) : ℤ)) : ℝ)| := h
      _ = |((x - y) - ((round (x - y) : ℤ) : ℝ)) + (y - ((round y : ℤ) : ℝ))| := by rw [e]
      _ ≤ |(x - y) - ((round (x - y) : ℤ) : ℝ)| + |y - ((round y : ℤ) : ℝ)| := abs_add_le _ _
      _ = nn (x - y) + nn y := rfl
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩
  · linarith [key a b]
  · have h := key b a
    have e : b - a = -(a - b) := by ring
    rw [e, Work.TMC16Core.Core.nn_neg_aux] at h
    linarith

/-- The `k`-th factor of the shifted block, as `S` of the doubled argument. -/
private lemma blk_shift_term (α : ℝ) (c : ℕ → ℤ) (x : ℝ) (k : ℕ) :
    |Real.sin (2 * Real.pi * (x + ((k : ℝ) + (c k : ℝ)) * α / 2))| =
      S (2 * x + ((k : ℝ) + (c k : ℝ)) * α) := by
  rw [S]
  congr 1
  ring_nf

theorem shift_block_relaxed {α : ℝ} {q : ℕ} {Δ Δr : ℝ} {c : ℕ → ℤ} {A : ℕ} {p : ℤ}
    (hq : 0 < q) (hΔ : 0 < Δ) (hΔr : 0 < Δr)
    (hcop : Nat.Coprime p.natAbs q)
    (happ : |(q : ℝ) * α - (p : ℝ)| ≤ Δ)
    (hsh : ∀ k l : ℕ, 1 ≤ k → k ≤ q → 1 ≤ l → l ≤ q →
      Work.TMC16Core.fracDist (((c k - c l : ℤ) : ℝ) * α) ≤ (A : ℝ) * Δr)
    (hsmall : (q : ℝ) * (Δ + (A : ℝ) * Δr) ≤ 3 / 2)
    (hsep : ∀ k l : ℕ, 1 ≤ k → k ≤ q → 1 ≤ l → l ≤ q → k ≠ l →
      1 / (5 * (q : ℝ)) ≤
        Work.TMC16Core.fracDist ((((k : ℤ) + c k - ((l : ℤ) + c l) : ℤ) : ℝ) * α))
    (x : ℝ) {k₀ : ℕ} (hk₀ : k₀ ∈ Finset.Icc 1 q)
    (hmin : ∀ k ∈ Finset.Icc 1 q,
      |Real.sin (2 * Real.pi * (x + ((k : ℝ) + (c k : ℝ)) * α / 2))| ≥
      |Real.sin (2 * Real.pi * (x + ((k₀ : ℝ) + (c k₀ : ℝ)) * α / 2))|) :
    |Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀,
        |Real.sin (2 * Real.pi * (x + ((k : ℝ) + (c k : ℝ)) * α / 2))|) + ((q : ℝ) - 1) * Real.log 2|
      ≤ 70 * Real.log q := by
  classical
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1' : 1 ≤ q := by omega
  have hlogq_nonneg : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1')
  rcases eq_or_lt_of_le hq1' with hq1 | hq_gt
  · -- ## `q = 1`: the product is empty
    subst hq1
    have hk : k₀ = 1 := by
      have h := hk₀
      simp only [Finset.mem_Icc] at h
      omega
    subst hk
    simp
  · -- ## `q ≥ 2`
    have hq2pos : 2 ≤ q := hq_gt
    have hlog2_nonneg : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlog2_le_one : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hAΔr_nonneg : (0 : ℝ) ≤ (A : ℝ) * Δr := by positivity
    set η : ℝ := Δ + (A : ℝ) * Δr with hηdef
    have hqη : (q : ℝ) * η ≤ 3 / 2 := by rw [hηdef]; exact hsmall
    have hη : 0 < η := by rw [hηdef]; linarith
    have hη_nonneg : 0 ≤ η := le_of_lt hη
    set Sf : ℕ → ℝ :=
      fun k => |Real.sin (2 * Real.pi * (x + ((k : ℝ) + (c k : ℝ)) * α / 2))| with hSf
    have hS_eq : ∀ k : ℕ, Sf k = S (2 * x + ((k : ℝ) + (c k : ℝ)) * α) := by
      intro k
      rw [hSf]
      exact blk_shift_term α c x k
    -- minimality of `k₀` in terms of `nn`
    have hminA_nn : ∀ k ∈ Finset.Icc 1 q,
        nn (2 * x + ((k₀ : ℝ) + (c k₀ : ℝ)) * α) ≤
          nn (2 * x + ((k : ℝ) + (c k : ℝ)) * α) := by
      intro k hk
      have h1 : S (2 * x + ((k₀ : ℝ) + (c k₀ : ℝ)) * α) ≤
          S (2 * x + ((k : ℝ) + (c k : ℝ)) * α) := by
        rw [← hS_eq k₀, ← hS_eq k]
        exact hmin k hk
      exact (Work.TMC16Core.Core.S_le_iff_nn_le_aux _ _).mp h1
    -- the separation hypothesis in `nn` form
    have hsep_nn : ∀ k l : ℕ, 1 ≤ k → k ≤ q → 1 ≤ l → l ≤ q → k ≠ l →
        1 / (5 * (q : ℝ)) ≤ nn (2 * x + ((k : ℝ) + (c k : ℝ)) * α
            - (2 * x + ((l : ℝ) + (c l : ℝ)) * α)) := by
      intro k l hk1 hkq hl1 hlq hne
      have h1 := hsep k l hk1 hkq hl1 hlq hne
      have h2 : ((((k : ℤ) + c k - ((l : ℤ) + c l) : ℤ) : ℝ) * α) =
          2 * x + ((k : ℝ) + (c k : ℝ)) * α - (2 * x + ((l : ℝ) + (c l : ℝ)) * α) := by
        push_cast; ring
      rwa [h2, Work.TMC16Core.Core.fracDist_eq_nn_aux] at h1
    have hnn_w : ∀ k ∈ Finset.Icc 1 q, k ≠ k₀ →
        1 / (10 * (q : ℝ)) ≤ nn (2 * x + ((k : ℝ) + (c k : ℝ)) * α) := by
      intro k hk hkne
      have h1 := hsep_nn k k₀ (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2
        (Finset.mem_Icc.mp hk₀).1 (Finset.mem_Icc.mp hk₀).2 hkne
      have h2 := Work.TMC16Core.Core.nn_sub_le_aux
        (2 * x + ((k : ℝ) + (c k : ℝ)) * α) (2 * x + ((k₀ : ℝ) + (c k₀ : ℝ)) * α)
      have h3 := hminA_nn k hk
      have h4 : (1 : ℝ) / (10 * (q : ℝ)) = (1 / 2) * (1 / (5 * (q : ℝ))) := by
        rw [one_div_mul_one_div]; ring_nf
      have h5 : (1 / 2 : ℝ) * (1 / (5 * (q : ℝ))) ≤
          (1 / 2 : ℝ) * (nn (2 * x + ((k : ℝ) + (c k : ℝ)) * α)
            + nn (2 * x + ((k₀ : ℝ) + (c k₀ : ℝ)) * α)) :=
        mul_le_mul_of_nonneg_left (le_trans h1 h2) (by norm_num)
      have h6 : (1 / 2 : ℝ) * (nn (2 * x + ((k : ℝ) + (c k : ℝ)) * α)
            + nn (2 * x + ((k₀ : ℝ) + (c k₀ : ℝ)) * α))
          ≤ nn (2 * x + ((k : ℝ) + (c k : ℝ)) * α) := by linarith
      rw [h4]; linarith
    have hA_lb : ∀ k ∈ Finset.Icc 1 q, k ≠ k₀ → 1 / (5 * (q : ℝ)) ≤ Sf k := by
      intro k hk hkne
      have h1 := hnn_w k hk hkne
      have h2 := Work.TMC16Core.Core.two_mul_nn_le_S_aux (2 * x + ((k : ℝ) + (c k : ℝ)) * α)
      have h3 : 2 * (1 / (10 * (q : ℝ))) = 1 / (5 * (q : ℝ)) := by
        rw [mul_one_div]; ring_nf
      rw [hS_eq k]; linarith
    have hSf_pos : ∀ k ∈ (Finset.Icc 1 q).erase k₀, 0 < Sf k := by
      intro k hk
      have h1 := hA_lb k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)
      have h2 : (0 : ℝ) < 1 / (5 * (q : ℝ)) := by positivity
      linarith
    have hSf_le1 : ∀ k ∈ (Finset.Icc 1 q).erase k₀, Sf k ≤ 1 := by
      intro k hk
      rw [hS_eq k]
      rw [S]
      exact Real.abs_sin_le_one _
    have hcard₀ : ((Finset.Icc 1 q).erase k₀).card = q - 1 := by
      rw [Finset.card_erase_of_mem hk₀, Nat.card_Icc]
      omega
    by_cases hq10 : q ≤ 10
    · -- ## crude case: `q ≤ 10`
      have hlog_ub : Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀, Sf k) ≤ 0 := by
        refine Real.log_nonpos (le_of_lt (Finset.prod_pos hSf_pos)) ?_
        calc ∏ k ∈ (Finset.Icc 1 q).erase k₀, Sf k
            ≤ ∏ k ∈ (Finset.Icc 1 q).erase k₀, (1 : ℝ) :=
              Finset.prod_le_prod₀ (fun k hk => le_of_lt (hSf_pos k hk)) hSf_le1
          _ = 1 := by simp
      have hge : (1 / (5 * (q : ℝ))) ^ ((Finset.Icc 1 q).erase k₀).card ≤
          ∏ k ∈ (Finset.Icc 1 q).erase k₀, Sf k := by
        calc (1 / (5 * (q : ℝ))) ^ ((Finset.Icc 1 q).erase k₀).card
            = ∏ k ∈ (Finset.Icc 1 q).erase k₀, (1 / (5 * (q : ℝ))) := by
              rw [Finset.prod_const]
          _ ≤ ∏ k ∈ (Finset.Icc 1 q).erase k₀, Sf k := by
              refine Finset.prod_le_prod₀ (fun k hk => by positivity) ?_
              intro k hk
              exact hA_lb k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)
      have hlog_lb : -(((q : ℝ) - 1) * (Real.log 5 + Real.log q)) ≤
          Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀, Sf k) + ((q : ℝ) - 1) * Real.log 2 := by
        have h1 : Real.log ((1 / (5 * (q : ℝ))) ^ ((Finset.Icc 1 q).erase k₀).card) ≤
            Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀, Sf k) :=
          Real.log_le_log (by positivity) hge
        rw [Real.log_pow, hcard₀] at h1
        have h4 : Real.log (1 / (5 * (q : ℝ))) = -(Real.log 5 + Real.log q) := by
          rw [one_div, Real.log_inv, Real.log_mul (by norm_num) (ne_of_gt hqR)]
        have h5 : ((q - 1 : ℕ) : ℝ) * Real.log (1 / (5 * (q : ℝ))) =
            -(((q : ℝ) - 1) * (Real.log 5 + Real.log q)) := by
          rw [h4, Nat.cast_sub (by omega : 1 ≤ q)]
          push_cast
          ring
        rw [h5] at h1
        have hql : (0 : ℝ) ≤ (q : ℝ) - 1 := by
          have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2pos
          linarith
        have h7 : (0 : ℝ) ≤ ((q : ℝ) - 1) * Real.log 2 := mul_nonneg hql hlog2_nonneg
        linarith [h1, h7]
      have hcrude : |Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₀, Sf k)
            + ((q : ℝ) - 1) * Real.log 2|
          ≤ ((q : ℝ) - 1) * (Real.log 5 + Real.log q) := by
        rw [abs_le]
        refine ⟨by linarith [hlog_lb], ?_⟩
        have hlog2le : Real.log 2 ≤ Real.log 5 + Real.log q := by
          have h5 : Real.log 2 ≤ Real.log 5 := Real.log_le_log (by norm_num) (by norm_num)
          linarith [hlogq_nonneg]
        have hql : (0 : ℝ) ≤ (q : ℝ) - 1 := by
          have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2pos
          linarith
        have h8 : ((q : ℝ) - 1) * Real.log 2 ≤ ((q : ℝ) - 1) * (Real.log 5 + Real.log q) :=
          mul_le_mul_of_nonneg_left hlog2le hql
        linarith [hlog_ub, h8]
      have hnum : ((q : ℝ) - 1) * (Real.log 5 + Real.log q) ≤ 70 * Real.log q := by
        have hq10R : (q : ℝ) ≤ 10 := by exact_mod_cast hq10
        have h1 : (q : ℝ) - 1 ≤ 9 := by linarith
        have h2 : Real.log 5 + Real.log q ≤ 6 * Real.log 2 := by
          have h3 : Real.log q ≤ Real.log 10 := Real.log_le_log (by positivity) hq10R
          have h4 : Real.log 5 + Real.log 10 = Real.log 50 := by
            rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
          have h5 : Real.log 50 ≤ 6 * Real.log 2 := by
            have h6 : Real.log (50 : ℝ) ≤ Real.log ((2 : ℝ) ^ 6) :=
              Real.log_le_log (by norm_num) (by norm_num)
            rw [Real.log_pow] at h6
            norm_num at h6
            linarith
          linarith
        have h7 : (0 : ℝ) ≤ Real.log 5 + Real.log q := by
          have : (0 : ℝ) ≤ Real.log 5 := Real.log_nonneg (by norm_num)
          linarith [hlogq_nonneg]
        have h8 : ((q : ℝ) - 1) * (Real.log 5 + Real.log q) ≤ 9 * (6 * Real.log 2) :=
          mul_le_mul h1 h2 h7 (by norm_num)
        have h9 : 9 * (6 * Real.log 2) = 54 * Real.log 2 := by ring
        have h10 : 54 * Real.log 2 ≤ 70 * Real.log 2 := by linarith
        have h11 : 70 * Real.log 2 ≤ 70 * Real.log q := by
          have h12 : Real.log 2 ≤ Real.log q :=
            Real.log_le_log (by norm_num) (by exact_mod_cast hq2pos)
          linarith
        linarith [h8, h9, h10, h11]
      linarith [hcrude, hnum]
    · -- ## delicate case: `q ≥ 11`
      have hq11 : 11 ≤ q := by omega
      have hlogq_ge : (2.2 : ℝ) ≤ Real.log q := by
        have hq11R : (11 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq11
        have h1 : Real.log ((11 : ℝ) ^ 3) ≤ Real.log ((q : ℝ) ^ 3) :=
          Real.log_le_log (by positivity)
            (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 11) hq11R 3)
        rw [Real.log_pow, Real.log_pow] at h1
        norm_num at h1
        have h5 : (10 : ℝ) * Real.log 2 ≤ 3 * Real.log 11 := by
          have h6 : Real.log ((2 : ℝ) ^ 10) ≤ Real.log ((11 : ℝ) ^ 3) :=
            Real.log_le_log (by positivity) (by norm_num)
          rw [Real.log_pow, Real.log_pow] at h6
          norm_num at h6
          linarith
        have h7 : (0.69 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
        linarith
      -- ### the rational comparison block
      set x' : ℝ := x + ((c 1 : ℤ) : ℝ) * α / 2 with hx'
      set Bf : ℕ → ℝ :=
        fun k => |Real.sin (2 * Real.pi * (x' + (k : ℝ) * ((p : ℝ) / (2 * (q : ℝ)))))| with hBf
      obtain ⟨k₁, hk₁, hminB⟩ := Finset.exists_min_image (Finset.Icc 1 q) Bf ⟨k₀, hk₀⟩
      have hB_eq : ∀ k : ℕ, Bf k = S (2 * x' + (k : ℝ) * ((p : ℝ) / (q : ℝ))) := by
        intro k
        rw [hBf]
        exact Work.TMC16Core.Core.block_term_rat p q x' k
      have hminB_nn : ∀ k ∈ Finset.Icc 1 q,
          nn (2 * x' + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ))) ≤
            nn (2 * x' + (k : ℝ) * ((p : ℝ) / (q : ℝ))) := by
        intro k hk
        have h1 : S (2 * x' + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ))) ≤
            S (2 * x' + (k : ℝ) * ((p : ℝ) / (q : ℝ))) := by
          rw [← hB_eq k₁, ← hB_eq k]
          exact hminB k hk
        exact (Work.TMC16Core.Core.S_le_iff_nn_le_aux _ _).mp h1
      obtain ⟨hgrid_sep, hgrid_min⟩ := grid_sep hq hcop x' hk₁ hminB_nn
      set g : ℕ → ℝ := fun k => nn (2 * x' + (k : ℝ) * ((p : ℝ) / (q : ℝ))) with hg
      set f : ℕ → ℝ := fun k => nn (2 * x + ((k : ℝ) + (c k : ℝ)) * α) with hf
      have hB_lb : ∀ k ∈ Finset.Icc 1 q, k ≠ k₁ → 1 / (q : ℝ) ≤ Bf k := by
        intro k hk hkne
        have h1 := hgrid_sep k hk hkne
        have h2 := Work.TMC16Core.Core.two_mul_nn_le_S_aux (2 * x' + (k : ℝ) * ((p : ℝ) / (q : ℝ)))
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
        have h := rat_prod_erase_le hq hcop x' hk₁ (fun k hk => by
          have h1 := hminB k hk
          simpa only [hBf] using h1)
        simpa only [hBf] using h
      have hRatLB : (q : ℝ) * (2 / Real.pi) / 2 ^ (q - 1) ≤
          ∏ k ∈ (Finset.Icc 1 q).erase k₁, Bf k := by
        have h := rat_prod_min_removed_v2 hq hcop x' hk₁ (fun k hk => by
          have h1 := hminB k hk
          simpa only [hBf] using h1)
        simpa only [hBf] using h
      have hprod2B : ∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k)
          = 2 ^ (q - 1) * ∏ k ∈ (Finset.Icc 1 q).erase k₁, Bf k := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, hcard₁]
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
            _ ≤ 2 * Real.log q + 2 := by linarith [Work.TMC16Core.Core.log_four_le_two]
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
            linarith [hh, Work.TMC16Core.Core.log_four_le_two]
          calc -(2 * Real.log q + 2) ≤ Real.log 2 + Real.log q - Real.log Real.pi := by
                linarith [h4, hlogq_nonneg, hlog2_nonneg]
            _ = Real.log (2 * (q : ℝ) / Real.pi) := h3.symm
            _ ≤ Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k)) :=
                Real.log_le_log (by positivity) h2
        rw [abs_le]
        exact ⟨hlb, hub⟩
      -- ### the harmonic sum over the rational grid
      have hcard_g : ∀ γ : ℝ, 0 < γ →
          ((((Finset.Icc 1 q).erase k₁).filter (fun k => g k < γ)).card : ℝ)
            ≤ 2 * (q : ℝ) * γ + 2 := by
        intro γ hγ
        by_cases hγ2 : γ ≤ 1 / 2
        · have h := Work.TMC16Core.Core.grid_card_bad hq hcop x' γ (le_of_lt hγ) hγ2 hk₁
          have h' : ((((Finset.Icc 1 q).erase k₁).filter (fun k => g k < γ)).card : ℝ)
              ≤ 2 * γ * (q : ℝ) + 2 := by simpa only [hg] using h
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
      have hHarm_g := Work.TMC16Core.Core.inv_sum_card_filter ((Finset.Icc 1 q).erase k₁) g
        (A := 2 * (q : ℝ)) (B := 2) (c := 1 / (2 * (q : ℝ)))
        (by positivity) (by positivity)
        (fun k hk => hgrid_sep k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk))
        hcard_g
      have hHarm_g' : ∑ k ∈ (Finset.Icc 1 q).erase k₁, (g k)⁻¹
          ≤ 2 * (q : ℝ) * Real.log q + 8 * (q : ℝ) := by
        have h2 : ((2 : ℕ) : ℝ) + 1 = 3 := by norm_num
        rw [h2, hcard₁] at hHarm_g
        have h3 : (3 : ℝ) / (1 / (2 * (q : ℝ))) = 6 * (q : ℝ) := by
          field_simp
          ring
        rw [h3] at hHarm_g
        have h4 : Real.log (((q - 1 : ℕ)) : ℝ) ≤ Real.log (q : ℝ) := by
          have hpos : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by
            rw [Nat.cast_sub (by omega : 1 ≤ q)]; push_cast
            have h2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2pos
            linarith
          have hle : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
            rw [Nat.cast_sub (by omega : 1 ≤ q)]; push_cast; linarith
          exact Real.log_le_log hpos hle
        have h5 : 2 * (q : ℝ) * (1 + Real.log (((q - 1 : ℕ)) : ℝ))
            ≤ 2 * (q : ℝ) * (1 + Real.log (q : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith [h4]) (by positivity)
        linarith [hHarm_g, h5]
      -- ### pointwise comparison of the two grids
      have hf_unfold : ∀ k : ℕ,
          f k = nn (2 * x' + (k : ℝ) * α + (((c k - c 1 : ℤ)) : ℝ) * α) := by
        intro k
        rw [hf, hx']
        congr 1
        push_cast
        ring
      have hab : ∀ k ∈ Finset.Icc 1 q, |f k - g k| ≤ η := by
        intro k hk
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        have hkq : k ≤ q := (Finset.mem_Icc.mp hk).2
        have hfrac : nn ((((c k - c 1 : ℤ)) : ℝ) * α) ≤ (A : ℝ) * Δr := by
          have h := hsh k 1 hk1 hkq (le_refl 1) hq1'
          rwa [Work.TMC16Core.Core.fracDist_eq_nn_aux] at h
        have hdiff : nn ((2 * x' + (k : ℝ) * α + (((c k - c 1 : ℤ)) : ℝ) * α)
              - (2 * x' + (k : ℝ) * ((p : ℝ) / (q : ℝ)))) ≤ η := by
          have e : (2 * x' + (k : ℝ) * α + (((c k - c 1 : ℤ)) : ℝ) * α)
              - (2 * x' + (k : ℝ) * ((p : ℝ) / (q : ℝ)))
              = (k : ℝ) * (α - (p : ℝ) / (q : ℝ)) + (((c k - c 1 : ℤ)) : ℝ) * α := by ring
          rw [e]
          have h4 : |(k : ℝ) * (α - (p : ℝ) / (q : ℝ))| ≤ Δ := by
            rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
            have h4' : (k : ℝ) ≤ (q : ℝ) := by exact_mod_cast hkq
            have h5 : |α - (p : ℝ) / (q : ℝ)| * (q : ℝ) = |(q : ℝ) * α - (p : ℝ)| := by
              calc |α - (p : ℝ) / (q : ℝ)| * (q : ℝ)
                  = |α - (p : ℝ) / (q : ℝ)| * |(q : ℝ)| := by rw [abs_of_nonneg hqR.le]
                _ = |(α - (p : ℝ) / (q : ℝ)) * (q : ℝ)| := by rw [abs_mul]
                _ = |(q : ℝ) * α - (p : ℝ)| := by
                    congr 1
                    rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hqR)]
                    ring
            nlinarith [h4', h5, happ, abs_nonneg (α - (p : ℝ) / (q : ℝ))]
          calc nn ((k : ℝ) * (α - (p : ℝ) / (q : ℝ)) + (((c k - c 1 : ℤ)) : ℝ) * α)
              ≤ nn ((k : ℝ) * (α - (p : ℝ) / (q : ℝ))) + nn ((((c k - c 1 : ℤ)) : ℝ) * α) :=
                nn_add_le _ _
            _ ≤ |(k : ℝ) * (α - (p : ℝ) / (q : ℝ))| + (A : ℝ) * Δr :=
                add_le_add (nn_le_abs _) hfrac
            _ ≤ Δ + (A : ℝ) * Δr := add_le_add h4 le_rfl
            _ = η := by rw [hηdef]
        rw [hf_unfold k, hg]
        exact le_trans (nn_abs_sub_le _ _) hdiff
      -- ### the counting bound for the shifted grid
      have hcard_f : ∀ γ : ℝ, 0 < γ →
          ((((Finset.Icc 1 q).erase k₀).filter (fun k => f k < γ)).card : ℝ)
            ≤ 2 * (q : ℝ) * γ + 6 := by
        intro γ hγ
        have hsub : (((Finset.Icc 1 q).erase k₀).filter (fun k => f k < γ))
            ⊆ (Finset.Icc 1 q).filter (fun k => g k < γ + η) := by
          intro k hk
          obtain ⟨hkS, hfk⟩ := Finset.mem_filter.mp hk
          have hkI : k ∈ Finset.Icc 1 q := Finset.mem_of_mem_erase hkS
          rcases abs_le.mp (hab k hkI) with ⟨h1, h2⟩
          refine Finset.mem_filter.mpr ⟨hkI, ?_⟩
          linarith
        have hcardA : (((Finset.Icc 1 q).erase k₀).filter (fun k => f k < γ)).card
            ≤ ((Finset.Icc 1 q).filter (fun k => g k < γ + η)).card := Finset.card_le_card hsub
        have hcardA' : ((((Finset.Icc 1 q).erase k₀).filter (fun k => f k < γ)).card : ℝ)
            ≤ ((Finset.Icc 1 q).filter (fun k => g k < γ + η)).card := by exact_mod_cast hcardA
        by_cases hcase : γ + η ≤ 1 / 2
        · have hS : (Finset.Icc 1 q).filter (fun k => g k < γ + η)
              ⊆ insert k₁ (((Finset.Icc 1 q).erase k₁).filter (fun k => g k < γ + η)) := by
            intro k hk
            obtain ⟨hkI, hkg⟩ := Finset.mem_filter.mp hk
            by_cases hkk : k = k₁
            · subst hkk; exact Finset.mem_insert_self _ _
            · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
                ⟨Finset.mem_erase.mpr ⟨hkk, hkI⟩, hkg⟩))
          have hcardB : ((Finset.Icc 1 q).filter (fun k => g k < γ + η)).card
              ≤ (((Finset.Icc 1 q).erase k₁).filter (fun k => g k < γ + η)).card + 1 :=
            le_trans (Finset.card_le_card hS) (Finset.card_insert_le k₁ _)
          have hcardB' : (((Finset.Icc 1 q).filter (fun k => g k < γ + η)).card : ℝ)
              ≤ ((((Finset.Icc 1 q).erase k₁).filter (fun k => g k < γ + η)).card : ℝ) + 1 := by
            exact_mod_cast hcardB
          have hG := Work.TMC16Core.Core.grid_card_bad hq hcop x' (γ + η) (by positivity) hcase hk₁
          have hG' : ((((Finset.Icc 1 q).erase k₁).filter (fun k => g k < γ + η)).card : ℝ)
              ≤ 2 * (γ + η) * (q : ℝ) + 2 := by simpa only [hg] using hG
          nlinarith [hcardA', hcardB', hG', hqη, hqR]
        · push_neg at hcase
          have hcardB : ((Finset.Icc 1 q).filter (fun k => g k < γ + η)).card ≤ q := by
            calc _ ≤ (Finset.Icc 1 q).card := Finset.card_le_card (Finset.filter_subset _ _)
              _ = q := by simp
          have hcardB' : (((Finset.Icc 1 q).filter (fun k => g k < γ + η)).card : ℝ) ≤ (q : ℝ) := by
            exact_mod_cast hcardB
          nlinarith [hcardA', hcardB', hcase, hqη, hqR]
      have hHarm_f := Work.TMC16Core.Core.inv_sum_card_filter ((Finset.Icc 1 q).erase k₀) f
        (A := 2 * (q : ℝ)) (B := 6) (c := 1 / (10 * (q : ℝ)))
        (by positivity) (by positivity)
        (fun k hk => hnn_w k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk))
        hcard_f
      have hHarm_f' : ∑ k ∈ (Finset.Icc 1 q).erase k₀, (f k)⁻¹
          ≤ 72 * (q : ℝ) + 2 * (q : ℝ) * Real.log q := by
        have h2 : ((6 : ℕ) : ℝ) + 1 = 7 := by norm_num
        rw [h2, hcard₀] at hHarm_f
        have h3 : (7 : ℝ) / (1 / (10 * (q : ℝ))) = 70 * (q : ℝ) := by
          field_simp; ring
        rw [h3] at hHarm_f
        have h4 : Real.log (((q - 1 : ℕ)) : ℝ) ≤ Real.log (q : ℝ) := by
          have hpos : (0 : ℝ) < ((q - 1 : ℕ) : ℝ) := by
            rw [Nat.cast_sub (by omega : 1 ≤ q)]; push_cast
            have h2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2pos
            linarith
          have hle : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
            rw [Nat.cast_sub (by omega : 1 ≤ q)]; push_cast; linarith
          exact Real.log_le_log hpos hle
        have h5 : 2 * (q : ℝ) * (1 + Real.log (((q - 1 : ℕ)) : ℝ))
            ≤ 2 * (q : ℝ) * (1 + Real.log (q : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith [h4]) (by positivity)
        linarith [hHarm_f, h5]
      -- ### the two exceptional sites
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
      -- ### the pointwise logarithmic comparison
      have hterm : ∀ k ∈ T, |Real.log (Sf k) - Real.log (Bf k)| ≤ η * ((f k)⁻¹ + (g k)⁻¹) := by
        intro k hk
        obtain ⟨hkI, hkne₀, hkne₁⟩ := hTmem k hk
        have hf0 : 0 < f k :=
          lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (10 * (q : ℝ))) (hnn_w k hkI hkne₀)
        have hf2 : f k ≤ 1 / 2 := by rw [hf]; exact nn_le_half _
        have hg0 : 0 < g k :=
          lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (2 * (q : ℝ))) (hgrid_sep k hkI hkne₁)
        have hg2 : g k ≤ 1 / 2 := by rw [hg]; exact nn_le_half _
        have h := Work.TMC16Core.Core.abs_log_sin_sub_le hf0 hg0 hf2 hg2
        have e1 : Sf k = Real.sin (Real.pi * f k) := by rw [hS_eq k, S_eq_sin_nn]
        have e2 : Bf k = Real.sin (Real.pi * g k) := by rw [hB_eq k, S_eq_sin_nn]
        have hmininv : (min (f k) (g k))⁻¹ ≤ (f k)⁻¹ + (g k)⁻¹ := by
          rcases le_total (f k) (g k) with hle | hle
          · rw [min_eq_left hle]
            have hh : (0 : ℝ) ≤ (g k)⁻¹ := inv_nonneg.mpr (le_of_lt hg0)
            linarith
          · rw [min_eq_right hle]
            have hh : (0 : ℝ) ≤ (f k)⁻¹ := inv_nonneg.mpr (le_of_lt hf0)
            linarith
        have hmul : |f k - g k| / min (f k) (g k) ≤ η * ((f k)⁻¹ + (g k)⁻¹) := by
          rw [div_eq_mul_inv]
          exact mul_le_mul (hab k hkI) hmininv (by positivity) hη_nonneg
        rw [e1, e2]
        exact le_trans h hmul
      have hcmp : |∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k))| ≤ 120 + 6 * Real.log q := by
        have h1 : |∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k))|
            ≤ ∑ k ∈ T, |Real.log (Sf k) - Real.log (Bf k)| := Finset.abs_sum_le_sum_abs _ _
        have h2 : ∑ k ∈ T, |Real.log (Sf k) - Real.log (Bf k)|
            ≤ ∑ k ∈ T, η * ((f k)⁻¹ + (g k)⁻¹) := Finset.sum_le_sum hterm
        have h3 : ∑ k ∈ T, η * ((f k)⁻¹ + (g k)⁻¹)
            = η * ∑ k ∈ T, ((f k)⁻¹ + (g k)⁻¹) := by rw [Finset.mul_sum]
        have h4 : ∑ k ∈ T, ((f k)⁻¹ + (g k)⁻¹) ≤ 80 * (q : ℝ) + 4 * (q : ℝ) * Real.log q := by
          rw [Finset.sum_add_distrib]
          have hf' : ∑ k ∈ T, (f k)⁻¹ ≤ ∑ k ∈ (Finset.Icc 1 q).erase k₀, (f k)⁻¹ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro k hk
              obtain ⟨hkI, hkne₀, _⟩ := hTmem k hk
              exact Finset.mem_erase.mpr ⟨hkne₀, hkI⟩
            · intro k hk _
              rw [hf]
              exact inv_nonneg.mpr (nn_nonneg _)
          have hg' : ∑ k ∈ T, (g k)⁻¹ ≤ ∑ k ∈ (Finset.Icc 1 q).erase k₁, (g k)⁻¹ := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hTsub ?_
            intro k hk _
            rw [hg]
            exact inv_nonneg.mpr (nn_nonneg _)
          linarith [hHarm_f', hHarm_g', hf', hg']
        calc |∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k))|
            ≤ ∑ k ∈ T, |Real.log (Sf k) - Real.log (Bf k)| := h1
          _ ≤ ∑ k ∈ T, η * ((f k)⁻¹ + (g k)⁻¹) := h2
          _ = η * ∑ k ∈ T, ((f k)⁻¹ + (g k)⁻¹) := h3
          _ ≤ η * (80 * (q : ℝ) + 4 * (q : ℝ) * Real.log q) :=
              mul_le_mul_of_nonneg_left h4 hη_nonneg
          _ = 80 * ((q : ℝ) * η) + 4 * ((q : ℝ) * η) * Real.log q := by ring
          _ ≤ 120 + 6 * Real.log q := by
              have h5 : 80 * ((q : ℝ) * η) ≤ 80 * (3 / 2) :=
                mul_le_mul_of_nonneg_left hqη (by norm_num)
              have h7 : 4 * ((q : ℝ) * η) * Real.log q ≤ 4 * (3 / 2) * Real.log q :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hqη (by norm_num)) hlogq_nonneg
              nlinarith [h5, h7]
      -- ### the log of the product of the doubled shifted factors
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
      -- ### case split on whether the two minimisers agree
      by_cases hkk : k₁ = k₀
      · -- ## case A: `k₁ = k₀`
        have h1 : (Finset.Icc 1 q).erase k₁ = (Finset.Icc 1 q).erase k₀ := by rw [hkk]
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
            ≤ 120 + 6 * Real.log q + (2 * Real.log q + 2) := by
          have hh : |(∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k)))
                + Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))|
              ≤ |∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k))|
                + |Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))| :=
            abs_add_le _ _
          linarith [hh, hcmp, hlog2B_abs]
        have h4 : 120 + 6 * Real.log q + (2 * Real.log q + 2) ≤ 70 * Real.log q := by
          linarith [hlogq_ge]
        rw [← hlogSf2, hid]
        linarith [h3, h4]
      · -- ## case B: `k₁ ≠ k₀`
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
        have hposS1 : 0 < 2 * Sf k₁ := by
          have h1 := hA_lb k₁ hk₁ hkkne
          have h2 : (0 : ℝ) < 1 / (5 * (q : ℝ)) := by positivity
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
              have h2 : (0 : ℝ) < 1 / (5 * (q : ℝ)) := by positivity
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
              have h2 : (0 : ℝ) < 1 / (5 * (q : ℝ)) := by positivity
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
                  have h2 : (0 : ℝ) < 1 / (5 * (q : ℝ)) := by positivity
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
        have hA1 : |Real.log (2 * Sf k₁)| ≤ Real.log q + 2 := by
          have hpos : 0 < 2 * Sf k₁ := hposS1
          have hlo : 2 / (5 * (q : ℝ)) ≤ 2 * Sf k₁ := by
            have h1 := hA_lb k₁ hk₁ hkkne
            have h2 : 2 * (1 / (5 * (q : ℝ))) = 2 / (5 * (q : ℝ)) := by
              rw [mul_one_div]
            linarith
          have hhi : 2 * Sf k₁ ≤ 2 := by
            have h1 : Sf k₁ ≤ 1 := hSf_le1 k₁ (Finset.mem_erase.mpr ⟨hkkne, hk₁⟩)
            linarith
          rw [abs_le]
          constructor
          · have hh := Real.log_le_log (by positivity : (0 : ℝ) < 2 / (5 * (q : ℝ))) hlo
            have h3 : Real.log (2 / (5 * (q : ℝ))) = Real.log 2 - Real.log 5 - Real.log q := by
              rw [Real.log_div (by norm_num) (by positivity),
                Real.log_mul (by norm_num) (ne_of_gt hqR)]
              ring
            rw [h3] at hh
            have h4 : Real.log 5 ≤ 2 + Real.log 2 := by
              have h5 : Real.log 5 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
              have h6 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
                rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
                push_cast; ring
              rw [h6] at h5
              linarith [hlog2_le_one]
            linarith [hh, h4]
          · have hh := Real.log_le_log hpos hhi
            linarith [hh, hlog2_le_one, hlogq_nonneg]
        have hB0 : |Real.log (2 * Bf k₀)| ≤ Real.log q + 2 := by
          have hpos : 0 < 2 * Bf k₀ := hposB0
          have hlo : 2 / (q : ℝ) ≤ 2 * Bf k₀ := by
            have h1 := hB_lb k₀ hk₀ hk₀ne
            have h3 : 2 * (1 / (q : ℝ)) = 2 / (q : ℝ) := by rw [mul_one_div]
            linarith
          have hhi : 2 * Bf k₀ ≤ 2 := by
            have h1 : Bf k₀ ≤ 1 := by
              rw [hB_eq k₀, S]
              exact Real.abs_sin_le_one _
            linarith
          rw [abs_le]
          constructor
          · have hh := Real.log_le_log (by positivity : (0 : ℝ) < 2 / (q : ℝ)) hlo
            have h3 : Real.log (2 / (q : ℝ)) = Real.log 2 - Real.log q :=
              Real.log_div (by norm_num) (ne_of_gt hqR)
            rw [h3] at hh
            linarith [hh, hlog2_nonneg]
          · have hh := Real.log_le_log hpos hhi
            linarith [hh, hlog2_le_one, hlogq_nonneg]
        have h3 : |(∑ k ∈ T, (Real.log (Sf k) - Real.log (Bf k))) + Real.log (2 * Sf k₁)
              - Real.log (2 * Bf k₀) + Real.log (∏ k ∈ (Finset.Icc 1 q).erase k₁, (2 * Bf k))|
            ≤ 120 + 6 * Real.log q + (Real.log q + 2) + (Real.log q + 2)
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
        have h4 : 120 + 6 * Real.log q + (Real.log q + 2) + (Real.log q + 2)
              + (2 * Real.log q + 2) ≤ 70 * Real.log q := by
          linarith [hlogq_ge]
        rw [← hlogSf2, hidB]
        linarith [h3, h4]

end Work.TMC16Core.Trig

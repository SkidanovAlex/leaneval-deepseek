import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.nnDist
import Submission.Work.TMC16Core.Basic.rational_block_prod
import Submission.Work.TMC16Core.Trig.gridW
import Submission.Work.TMC16Core.Trig.grid_sep
import Submission.Work.TMC16Core.Trig.nn_mul_div_emod
import Submission.Work.TMC16Core.Trig.nn_grid_min_transfer
import Submission.Work.TMC16Core.Trig.q_mul_nn_eq_gridW
import Submission.Work.TMC16Core.Trig.gridW_inv_sum_le
import Submission.Work.TMC16Core.Trig.sum_emod_coprime
import Submission.Work.TMC16Core.Trig.rat_prod_erase_le
import Submission.Work.TMC16Core.Trig.rat_prod_min_removed_v2
import Submission.Work.TMC16Core.Core.comp_sum_sharp
import Submission.Work.TMC16Core.Core.card_nn_lt_le
import Submission.Work.TMC16Core.Core.bad_card_bound
import Submission.Work.TMC16Core.Core.final_arith
import Submission.Work.TMC16Core.Trig.rat_log_prod_bounds
import Submission.Work.TMC16Core.Core.blk_sep_base

set_option maxHeartbeats 1600000

/-!
# AJ §9, the shifted block estimate (`shift1`)

This file proves `irrat_blk_shift`, the shifted form of the Avila–Jitomirskaya block estimate:
the block of `q n` consecutive sites `k`, each shifted by `Lsh k * q r` (`|Lsh k| ≤ ℓ - 1`),
has its minimal-`|sin|` factor removed and is then `2^{-(q n - 1)}` up to a factor
`q n · exp (32 (Δ n + ℓ Δ r) q n log (q n))`.

The proof follows the paper: compare the *shifted irrational* block with the *rational* block
`k ↦ round (q n · α)/(q n)`, using

* the pairwise separation of the shifted sites (by `Δ`-minimality and the best-approximation
  hypotheses),
* the grid sum bound `∑ 1/nn ≤ 4 q (1 + log q)` (`Trig/grid_nn_sum`),
* the exact rational block product with one factor removed
  (`Trig/rat_prod_erase_le`, `Trig/rat_prod_min_removed_v2`),
* the mean-value bound `|log a - log b| ≤ 2|a-b|/b` for the logarithmic comparison.
-/

namespace Work.TMC16Core.Core

open Work.TMC16Core
open Work.TMC16Core.Basic
open Work.TMC16Core.Trig
open scoped BigOperators

/-! ## Glue lemmas for the grid sum -/

lemma cast_toNat_of_nonneg' {z : ℤ} (hz : 0 ≤ z) : (((z.toNat : ℕ)) : ℝ) = ((z : ℤ) : ℝ) := by
  exact_mod_cast (Int.toNat_of_nonneg hz : ((z.toNat : ℕ) : ℤ) = z)

lemma nn_two_mul_add_frac' (x w : ℝ) : nn (2 * x + w) = nn (Int.fract (2 * x) + w) := by
  have h : 2 * x + w = (Int.fract (2 * x) + w) + ((⌊2 * x⌋ : ℤ) : ℝ) := by
    have hfloor := Int.floor_add_fract (2 * x)
    linarith
  rw [h, nn_add_intCast]

theorem sum_erase_emod_coprime' {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q)
    {k₁ : ℕ} (hk₁ : k₁ ∈ Finset.Icc 1 q) (F : ℕ → ℝ) :
    ∑ k ∈ (Finset.Icc 1 q).erase k₁, F ((((k : ℤ) * p) % q).toNat)
      = ∑ j ∈ (Finset.range q).erase ((((k₁ : ℤ) * p) % q).toNat), F j := by
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hjlt : ((((k₁ : ℤ) * p) % q).toNat) < q := by
    have h1 : 0 ≤ ((k₁ : ℤ) * p) % q := Int.emod_nonneg _ hqZ
    have h2 : ((k₁ : ℤ) * p) % q < (q : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hq)
    have h3 : ((((k₁ : ℤ) * p) % q).toNat : ℤ) < (q : ℤ) := by
      rw [Int.toNat_of_nonneg h1]; exact h2
    exact_mod_cast h3
  have hmain := sum_emod_coprime hq hcop (F := fun z : ℤ => F z.toNat)
  simp only [Int.toNat_natCast] at hmain
  rw [Finset.sum_erase_eq_sub hk₁, Finset.sum_erase_eq_sub (Finset.mem_range.mpr hjlt),
    hmain]

/-- **The grid sum bound** (AJ §9, the harmonic estimate for the rational block).
For `q > 0`, `p` coprime to `q` and real `x`, if `k₁` minimises `nn (2x + k p/q)` over
`k ∈ {1,…,q}` then `∑_{k ≠ k₁} 1/nn (2x + k p/q) ≤ 4 q (1 + log q)`. -/
theorem grid_sum_bound {q : ℕ} (hq : 0 < q) {p : ℤ} (hcop : Nat.Coprime p.natAbs q) (x : ℝ)
    {k₁ : ℕ} (hk₁ : k₁ ∈ Finset.Icc 1 q)
    (hmin : ∀ k ∈ Finset.Icc 1 q,
      nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))) ≥
        nn (2 * x + (k₁ : ℝ) * ((p : ℝ) / (q : ℝ)))) :
    ∑ k ∈ (Finset.Icc 1 q).erase k₁,
        (nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))))⁻¹
      ≤ 4 * (q : ℝ) * (1 + Real.log q) := by
  have hqZ : (q : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  let j₁ : ℕ := ((((k₁ : ℤ) * p) % q).toNat)
  have hj₁lt : j₁ < q := by
    have h1 : 0 ≤ ((k₁ : ℤ) * p) % q := Int.emod_nonneg _ hqZ
    have h2 : ((k₁ : ℤ) * p) % q < (q : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hq)
    have h3 : ((j₁ : ℕ) : ℤ) < (q : ℤ) := by
      dsimp only [j₁]
      rw [Int.toNat_of_nonneg h1]; exact h2
    exact_mod_cast h3
  have hminj : ∀ j < q, nn (2 * x + (j : ℝ) / (q : ℝ)) ≥
      nn (2 * x + (j₁ : ℝ) / (q : ℝ)) := by
    intro j hj
    have h := nn_grid_min_transfer hq hcop x hk₁ hmin j hj
    simpa only [j₁] using h
  set s : ℝ := Int.fract (2 * x) with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; exact Int.fract_nonneg (2 * x)
  have hs1 : s < 1 := by rw [hsdef]; exact Int.fract_lt_one (2 * x)
  have hminj_s : ∀ j < q, nn (s + (j : ℝ) / (q : ℝ)) ≥ nn (s + (j₁ : ℝ) / (q : ℝ)) := by
    intro j hj
    have h := hminj j hj
    have e1 : nn (2 * x + (j : ℝ) / (q : ℝ)) = nn (s + (j : ℝ) / (q : ℝ)) := by
      simpa [hsdef] using nn_two_mul_add_frac' x ((j : ℝ) / (q : ℝ))
    have e2 : nn (2 * x + (j₁ : ℝ) / (q : ℝ)) = nn (s + (j₁ : ℝ) / (q : ℝ)) := by
      simpa [hsdef] using nn_two_mul_add_frac' x ((j₁ : ℝ) / (q : ℝ))
    rwa [e1, e2] at h
  have hreindex : ∑ k ∈ (Finset.Icc 1 q).erase k₁,
        (nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))))⁻¹
      = ∑ j ∈ (Finset.range q).erase j₁, (nn (2 * x + (j : ℝ) / (q : ℝ)))⁻¹ := by
    have hA : ∑ k ∈ (Finset.Icc 1 q).erase k₁,
          (nn (2 * x + (k : ℝ) * ((p : ℝ) / (q : ℝ))))⁻¹
        = ∑ k ∈ (Finset.Icc 1 q).erase k₁,
          (nn (2 * x + ((((k : ℤ) * p) % q).toNat : ℝ) / (q : ℝ)))⁻¹ := by
      refine Finset.sum_congr rfl ?_
      intro k _
      have hz : 0 ≤ ((k : ℤ) * p) % q := Int.emod_nonneg _ hqZ
      congr 1
      rw [cast_toNat_of_nonneg' hz, ← nn_mul_div_emod hq p x k]
    have h1 := sum_erase_emod_coprime' hq hcop hk₁
      (F := fun j : ℕ => (nn (2 * x + (j : ℝ) / (q : ℝ)))⁻¹)
    rw [hA]
    simpa only [j₁] using h1
  have hminW : ∀ j < q, gridW q ((q : ℝ) * s) j₁ ≤ gridW q ((q : ℝ) * s) j := by
    intro j hj
    have h1 : (q : ℝ) * nn (s + (j₁ : ℝ) / (q : ℝ)) = gridW q ((q : ℝ) * s) j₁ :=
      q_mul_nn_eq_gridW hq hs0 hs1 hj₁lt
    have h2 : (q : ℝ) * nn (s + (j : ℝ) / (q : ℝ)) = gridW q ((q : ℝ) * s) j :=
      q_mul_nn_eq_gridW hq hs0 hs1 hj
    rw [← h1, ← h2]
    exact mul_le_mul_of_nonneg_left (hminj_s j hj) (le_of_lt hpos)
  have hA0 : 0 ≤ (q : ℝ) * s := mul_nonneg (le_of_lt hpos) hs0
  have hAq : (q : ℝ) * s < (q : ℝ) := by nlinarith [hpos, hs0, hs1]
  have hcore := gridW_inv_sum_le hq hA0 hAq hj₁lt hminW
  have hnorm : ∑ j ∈ (Finset.range q).erase j₁, (gridW q ((q : ℝ) * s) j)⁻¹
      = (q : ℝ)⁻¹ * ∑ j ∈ (Finset.range q).erase j₁, (nn (s + (j : ℝ) / (q : ℝ)))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hjq : j < q := Finset.mem_range.mp (Finset.mem_of_mem_erase hj)
    rw [← q_mul_nn_eq_gridW hq hs0 hs1 hjq, mul_inv]
  have hfinal : ∑ j ∈ (Finset.range q).erase j₁, (nn (s + (j : ℝ) / (q : ℝ)))⁻¹
      ≤ 4 * (q : ℝ) * (1 + Real.log q) := by
    rw [hnorm] at hcore
    have hmul := mul_le_mul_of_nonneg_left hcore (le_of_lt hpos)
    have hleft : (q : ℝ) * ((q : ℝ)⁻¹ *
        ∑ j ∈ (Finset.range q).erase j₁, (nn (s + (j : ℝ) / (q : ℝ)))⁻¹)
        = ∑ j ∈ (Finset.range q).erase j₁, (nn (s + (j : ℝ) / (q : ℝ)))⁻¹ := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
    rw [hleft] at hmul
    calc ∑ j ∈ (Finset.range q).erase j₁, (nn (s + (j : ℝ) / (q : ℝ)))⁻¹
        ≤ (q : ℝ) * (4 * (1 + Real.log (q : ℝ))) := hmul
      _ = 4 * (q : ℝ) * (1 + Real.log q) := by ring
  have hsum_s : ∑ j ∈ (Finset.range q).erase j₁, (nn (2 * x + (j : ℝ) / (q : ℝ)))⁻¹
      = ∑ j ∈ (Finset.range q).erase j₁, (nn (s + (j : ℝ) / (q : ℝ)))⁻¹ := by
    refine Finset.sum_congr rfl ?_
    intro j _
    congr 1
    simpa [hsdef] using nn_two_mul_add_frac' x ((j : ℝ) / (q : ℝ))
  rw [hreindex, hsum_s]
  exact hfinal


/-! ## Elementary `nn`/`S` facts -/

/-- `fracDist` is `nn`. -/
lemma fracDist_eq_nn (t : ℝ) : fracDist t = nn t := rfl

/-- `nn` is even. -/
lemma nn_neg' (w : ℝ) : nn (-w) = nn w := by
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

/-- `nn (a - b) ≤ nn a + nn b`. -/
lemma nn_sub_le' (a b : ℝ) : nn (a - b) ≤ nn a + nn b := by
  have h : a - b = a + (-b) := by ring
  rw [h]
  calc nn (a + -b) ≤ nn a + nn (-b) := nn_add_le a (-b)
    _ = nn a + nn b := by rw [nn_neg']

/-- `|nn a - nn b| ≤ nn (a - b)`. -/
lemma abs_nn_sub_nn_le (a b : ℝ) : |nn a - nn b| ≤ nn (a - b) := by
  rw [abs_sub_le_iff]
  constructor
  · have h := nn_add_le (a - b) b
    rw [sub_add_cancel] at h
    linarith
  · have h := nn_add_le (b - a) a
    rw [sub_add_cancel] at h
    have h2 : nn (b - a) = nn (a - b) := by
      rw [show b - a = -(a - b) by ring, nn_neg']
    linarith [h, h2.le, h2.ge]

/-- `S` is `π`-Lipschitz in the `nn`-metric: `|S a - S b| ≤ π * nn (a - b)`. -/
lemma abs_S_sub_S_le_nn (a b : ℝ) : |S a - S b| ≤ Real.pi * nn (a - b) := by
  have h1 : S a = Real.sin (Real.pi * nn a) := S_eq_sin_nn a
  have h2 : S b = Real.sin (Real.pi * nn b) := S_eq_sin_nn b
  have h3 : |Real.sin (Real.pi * nn a) - Real.sin (Real.pi * nn b)|
      ≤ |Real.pi * nn a - Real.pi * nn b| := Real.abs_sin_sub_sin_le _ _
  have h4 : |Real.pi * nn a - Real.pi * nn b| = Real.pi * |nn a - nn b| := by
    rw [show Real.pi * nn a - Real.pi * nn b = Real.pi * (nn a - nn b) by ring, abs_mul,
      abs_of_pos Real.pi_pos]
  calc |S a - S b| = |Real.sin (Real.pi * nn a) - Real.sin (Real.pi * nn b)| := by rw [h1, h2]
    _ ≤ |Real.pi * nn a - Real.pi * nn b| := h3
    _ = Real.pi * |nn a - nn b| := h4
    _ ≤ Real.pi * nn (a - b) := by
        exact mul_le_mul_of_nonneg_left (abs_nn_sub_nn_le a b) (le_of_lt Real.pi_pos)

/-- `S a = sin (π * nn a)`. -/
lemma S_eq_sin_nn' (a : ℝ) : S a = Real.sin (Real.pi * nn a) := S_eq_sin_nn a

/-- `2 * nn a ≤ S a` (Jordan's inequality, for `nn ≤ 1/2`). -/
lemma two_mul_nn_le_S' (a : ℝ) : 2 * nn a ≤ S a := by
  have h := two_div_pi_mul_le_S a
  have : (2 : ℝ) / Real.pi * (Real.pi * nn a) = 2 * nn a := by field_simp
  linarith [h, this.le, this.ge]

/-- `log (sin (π n)) ≥ log (2 n)` for `n ∈ (0, 1/2]`. -/
lemma log_two_mul_le_log_S {a : ℝ} (h0 : 0 < nn a) : Real.log (2 * nn a) ≤ Real.log (S a) := by
  refine Real.log_le_log (by linarith) ?_
  simpa [S_eq_sin_nn'] using two_mul_nn_le_S' a

/-- `S a ≤ π * nn a`. -/
lemma S_le_pi_mul_nn' (a : ℝ) : S a ≤ Real.pi * nn a := S_le_pi_mul_nn a

/-! ## Separation from the best-approximation hypotheses -/

/-- **Refined separation.**  If `q j ≤ d < q (j+1)` and `1 ≤ d < q n`, then
`1/(2 q (j+1)) ≤ fracDist (d α)`; with `j + 1 ≤ n` this is at least `1/(2 q n)`. -/
lemma sep_refined {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m)
    (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    {n d j : ℕ} (hd1 : 1 ≤ d) (hdn : d < q n) (hjd : q j ≤ d) (hdj : d < q (j + 1)) :
    1 / (2 * (q (j + 1) : ℝ)) ≤ fracDist ((d : ℝ) * α) := by
  have h1 : Δ j ≤ fracDist ((d : ℝ) * α) := hbest j d hjd hdj
  have h2 : 1 / ((q (j + 1) : ℝ) + (q j : ℝ)) < Δ j := hΔlo j
  have hsum : (q (j + 1) : ℝ) + (q j : ℝ) ≤ 2 * (q (j + 1) : ℝ) := by
    have : (q j : ℝ) ≤ (q (j + 1) : ℝ) := by
      exact_mod_cast (le_trans hjd (Nat.le_of_lt hdj))
    linarith
  have hqjpos : (0 : ℝ) < (q (j + 1) : ℝ) := by exact_mod_cast (hqpos (j + 1))
  have hsumpos : 0 < (q (j + 1) : ℝ) + (q j : ℝ) := by
    have : (0 : ℝ) < (q j : ℝ) := by exact_mod_cast (hqpos j)
    linarith
  have h3 : 1 / (2 * (q (j + 1) : ℝ)) ≤ 1 / ((q (j + 1) : ℝ) + (q j : ℝ)) :=
    one_div_le_one_div_of_le hsumpos hsum
  linarith

/-- **Locating a multiplicative scale.**  For `q 0 ≤ d < q n` there is `j` with
`q j ≤ d < q (j+1)` and `j + 1 ≤ n`. -/
lemma exists_scale {q : ℕ → ℕ} :
    ∀ n d : ℕ, q 0 ≤ d → d < q n → ∃ j : ℕ, q j ≤ d ∧ d < q (j + 1) ∧ j + 1 ≤ n := by
  intro n
  induction n with
  | zero => intro d h0 h1; exact absurd h1 (not_lt.mpr h0)
  | succ m ih =>
    intro d h0 h1
    rcases lt_or_ge d (q m) with hlt | hge
    · obtain ⟨j, hj1, hj2, hj3⟩ := ih d h0 hlt
      exact ⟨j, hj1, hj2, Nat.le_succ_of_le hj3⟩
    · exact ⟨m, hge, h1, le_rfl⟩

/-- **Uniform separation at scale `n`**: every `1 ≤ d < q n` satisfies
`1/(2 * q n) ≤ fracDist (d α)`. -/
lemma sep_scale {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hbase : ∀ d : ℕ, 1 ≤ d → d < q 0 →
      1 / (2 * (q 0 : ℝ)) ≤ fracDist ((d : ℝ) * α))
    {n d : ℕ} (hd1 : 1 ≤ d) (hdn : d < q n) :
    1 / (2 * (q n : ℝ)) ≤ fracDist ((d : ℝ) * α) := by
  have hLpos : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast (hqpos n)
  rcases lt_or_ge d (q 0) with hlt | hge
  · have hb := hbase d hd1 hlt
    have hq0L : (q 0 : ℝ) ≤ (q n : ℝ) := by
      have := hmono.monotone (Nat.zero_le n)
      exact_mod_cast this
    have hq0pos : (0 : ℝ) < (q 0 : ℝ) := by exact_mod_cast (hqpos 0)
    have h2 : 2 * (q 0 : ℝ) ≤ 2 * (q n : ℝ) := by linarith
    have h4 : 1 / (2 * (q n : ℝ)) ≤ 1 / (2 * (q 0 : ℝ)) :=
      one_div_le_one_div_of_le (by linarith) h2
    linarith
  · obtain ⟨j, hj1, hj2, hj3⟩ := exists_scale n d hge hdn
    have hsep := sep_refined hqpos hΔpos hΔeq hΔlo hbest hd1 hdn hj1 hj2
    have hLj : (q (j + 1) : ℝ) ≤ (q n : ℝ) := by
      exact_mod_cast (hmono.monotone hj3)
    have hqjpos : (0 : ℝ) < (q (j + 1) : ℝ) := by exact_mod_cast (hqpos (j + 1))
    have h6 : 1 / (2 * (q n : ℝ)) ≤ 1 / (2 * (q (j + 1) : ℝ)) := by
      apply one_div_le_one_div_of_le (by linarith)
      linarith
    linarith

/-- **The `q n = 2` case.**  If the scale `n` has `q n = 2` then `fracDist α ≥ 1/3`. -/
lemma sep_two {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hbase : ∀ d : ℕ, 1 ≤ d → d < q 0 →
      max (1 / (2 * (q 0 : ℝ) - 1)) (1 / (q 0 : ℝ) - Δ 0) ≤ fracDist ((d : ℝ) * α))
    {n : ℕ} (hn : q n = 2) :
    (1 : ℝ) / 3 ≤ fracDist α := by
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    have hb := hbase 1 le_rfl (by rw [hn]; norm_num)
    have h1 : (1 : ℝ) / (2 * (q 0 : ℝ) - 1) ≤ fracDist (((1 : ℕ) : ℝ) * α) :=
      le_trans (le_max_left _ _) hb
    rw [hn] at h1
    norm_num at h1
    simpa using h1
  · have h1 : q 1 ≤ q n := hmono.monotone hnpos
    rw [hn] at h1
    have hq0pos : 0 < q 0 := hqpos 0
    have hlt01 : q 0 < q 1 := hmono (Nat.zero_lt_one)
    have hq1 : q 1 = 2 := by omega
    have hq0 : q 0 = 1 := by omega
    have hbest0 := hbest 0 1 (by rw [hq0]) (by rw [hq1]; norm_num)
    have hlo0 := hΔlo 0
    rw [hq0, hq1] at hlo0
    have hbest0' : Δ 0 ≤ fracDist α := by
      simpa using hbest0
    norm_num at hlo0
    linarith

/-- `nn x ≤ |x - m|` for every integer `m`. -/
lemma nn_le_abs_sub_intCast (x : ℝ) (m : ℤ) : nn x ≤ |x - (m : ℝ)| := by
  simpa [nn] using round_le x m

/-- **Coprimality of the convergent numerator with the scale.**  With `L = q n`,
`pn = round (L α)` and `Δ n = fracDist (L α)`, the integers `pn` and `L` are coprime. -/
lemma coprime_round {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hbase : ∀ d : ℕ, 1 ≤ d → d < q 0 →
      1 / (2 * (q 0 : ℝ)) ≤ fracDist ((d : ℝ) * α))
    {n : ℕ} :
    Nat.Coprime (Int.natAbs (round ((q n : ℝ) * α))) (q n) := by
  set L : ℕ := q n with hLdef
  set pn : ℤ := round ((L : ℝ) * α) with hpndef
  have hLpos : 0 < L := hqpos n
  have hLposR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hΔn : Δ n = |(L : ℝ) * α - (pn : ℝ)| := by
    rw [hΔeq n, fracDist, hpndef, hLdef]
  have hLt : Δ n < 1 / (L : ℝ) := by
    have h1 : Δ n < 1 / ((q (n + 1) : ℝ)) := hΔup n
    have h2 : (L : ℝ) < (q (n + 1) : ℝ) := by
      have := hmono (Nat.lt_succ_self n); exact_mod_cast this
    have h4 : (0 : ℝ) < (q (n + 1) : ℝ) := by
      have := hqpos (n + 1); exact_mod_cast this
    have h5 : 1 / ((q (n + 1) : ℝ)) ≤ 1 / (L : ℝ) := one_div_le_one_div_of_le hLposR (le_of_lt h2)
    linarith
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  set g : ℕ := Nat.gcd (Int.natAbs pn) L with hgdef
  have hgL : g ∣ L := Nat.gcd_dvd_right _ _
  have hgp : g ∣ Int.natAbs pn := Nat.gcd_dvd_left _ _
  have hgne1 : g ≠ 1 := by rw [hgdef]; exact hne
  have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgL hLpos
  have hg2 : 2 ≤ g := by omega
  have hgle : g ≤ L := Nat.le_of_dvd hLpos hgL
  set d : ℕ := L / g with hddef
  have hdmul : g * d = L := Nat.mul_div_cancel' hgL
  have hdpos : 0 < d := by
    rw [hddef]; exact Nat.div_pos hgle hgpos
  have hdlt : d < L := by
    have h1 : 1 * d < g * d := Nat.mul_lt_mul_of_pos_right (by omega : 1 < g) hdpos
    rw [hdmul] at h1; simpa using h1
  have hgZp : (g : ℤ) ∣ pn := by
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
    exact hgp
  obtain ⟨p', hp'⟩ := hgZp
  have hcast_d : (d : ℝ) = (L : ℝ) / (g : ℝ) := by
    have hgR : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hgpos
    have : (L : ℝ) = (g : ℝ) * (d : ℝ) := by
      rw [← hdmul]; push_cast; ring
    rw [this]; field_simp
  have hcast_p : (pn : ℝ) = (g : ℝ) * (p' : ℝ) := by
    rw [hp']; push_cast; ring
  have hdiff : (d : ℝ) * α - (p' : ℝ) = ((L : ℝ) * α - (pn : ℝ)) / (g : ℝ) := by
    rw [hcast_d, hcast_p]
    have hgR : (g : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (g : ℝ) := by exact_mod_cast hgpos
      linarith
    field_simp
  have hle : fracDist ((d : ℝ) * α) ≤ Δ n / (g : ℝ) := by
    calc fracDist ((d : ℝ) * α) ≤ |(d : ℝ) * α - (p' : ℝ)| := nn_le_abs_sub_intCast _ _
      _ = |((L : ℝ) * α - (pn : ℝ)) / (g : ℝ)| := by rw [hdiff]
      _ = |(L : ℝ) * α - (pn : ℝ)| / (g : ℝ) := by
            rw [abs_div, abs_of_pos (by exact_mod_cast hgpos : (0:ℝ) < (g:ℝ))]
      _ = Δ n / (g : ℝ) := by rw [← hΔn]
  have hdiv2 : Δ n / (g : ℝ) ≤ Δ n / 2 := by
    apply div_le_div_of_nonneg_left (le_of_lt (hΔpos n)) (by norm_num)
    exact_mod_cast hg2
  have hsep := sep_scale hqpos hmono hΔpos hΔeq hΔlo hbest hbase (n := n) (d := d)
    (by omega) hdlt
  rw [← hLdef] at hsep
  have h2L : (0 : ℝ) < 2 * (L : ℝ) := by linarith
  have h1 : (1 : ℝ) / (2 * (L : ℝ)) ≤ Δ n / 2 := le_trans hsep (le_trans hle hdiv2)
  have h2 : (1 : ℝ) ≤ (Δ n / 2) * (2 * (L : ℝ)) := (div_le_iff₀ h2L).mp h1
  have h3 : (Δ n / 2) * (2 * (L : ℝ)) = Δ n * (L : ℝ) := by ring
  rw [h3] at h2
  have h4 : (1 : ℝ) / (L : ℝ) ≤ Δ n := (div_le_iff₀ hLposR).mpr h2
  linarith

/-- **Reindexing the shifted block.**  For the phase `2x = ξ + (p-1)α` the integer block
`Icc p (p+L-1)` with the minimum removed becomes the index block `Icc 1 L` with the
corresponding index removed, the site `k = p + j - 1` carrying the shift
`Lsh (p + j - 1) * qr`. -/
lemma sum_block_shift_reindex (L : ℕ) (p k₀ : ℤ) (ξ α : ℝ) (qr : ℤ) (Lsh : ℤ → ℤ)
    (hk₀ : k₀ ∈ Finset.Icc p (p + (L : ℤ) - 1)) :
    (∑ k ∈ (Finset.Icc p (p + (L : ℤ) - 1)).erase k₀,
        Real.log |Real.sin (Real.pi * (ξ + ((k + Lsh k * qr : ℤ) : ℝ) * α))|)
      = ∑ j ∈ (Finset.Icc 1 L).erase ((k₀ - p + 1).toNat),
          Real.log |Real.sin (Real.pi * (ξ + (((p + (j : ℤ) - 1)
            + Lsh (p + (j : ℤ) - 1) * qr : ℤ) : ℝ) * α))| := by
  set x : ℝ := (ξ + ((p : ℝ) - 1) * α) / 2 with hx
  set j₀ : ℕ := (k₀ - p + 1).toNat with hj₀
  have hmem₀ : k₀ - p + 1 ∈ Finset.Icc 1 (L : ℤ) := by
    rw [Finset.mem_Icc] at hk₀ ⊢
    constructor <;> omega
  have hj₀spec : ((j₀ : ℕ) : ℤ) = k₀ - p + 1 := by
    rw [hj₀]
    exact Int.toNat_of_nonneg (by rw [Finset.mem_Icc] at hmem₀; omega)
  refine Finset.sum_bij (fun k _ => (k - p + 1).toNat) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_erase] at hk
    obtain ⟨hkne, hkmem⟩ := hk
    rw [Finset.mem_erase]
    constructor
    · intro hcon
      apply hkne
      have h1 : 0 ≤ k - p + 1 := by rw [Finset.mem_Icc] at hkmem; omega
      have h2 : 0 ≤ k₀ - p + 1 := by rw [Finset.mem_Icc] at hk₀; omega
      have hcon' : (k - p + 1).toNat = (k₀ - p + 1).toNat := by rw [hj₀] at hcon; exact hcon
      have hconZ : ((k - p + 1).toNat : ℤ) = ((k₀ - p + 1).toNat : ℤ) := by exact_mod_cast hcon'
      rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at hconZ
      omega
    · rw [Finset.mem_Icc] at hkmem ⊢
      have h1 : 0 ≤ k - p + 1 := by omega
      have h2 : k - p + 1 ≤ (L : ℤ) := by omega
      constructor
      · have : (1 : ℤ) ≤ ((k - p + 1).toNat : ℤ) := by rw [Int.toNat_of_nonneg h1]; omega
        omega
      · have : ((k - p + 1).toNat : ℤ) ≤ (L : ℤ) := by rw [Int.toNat_of_nonneg h1]; omega
        omega
  · intro k₁ hk₁ k₂ hk₂ heq
    rw [Finset.mem_erase] at hk₁ hk₂
    have h1 : 0 ≤ k₁ - p + 1 := by rw [Finset.mem_Icc] at hk₁; omega
    have h2 : 0 ≤ k₂ - p + 1 := by rw [Finset.mem_Icc] at hk₂; omega
    have heq' : ((k₁ - p + 1).toNat : ℤ) = ((k₂ - p + 1).toNat : ℤ) := by exact_mod_cast heq
    rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at heq'
    omega
  · intro b hb
    rw [Finset.mem_erase] at hb
    obtain ⟨hbne, hbmem⟩ := hb
    refine ⟨(b : ℤ) + p - 1, ?_, ?_⟩
    · rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · intro hcon
        apply hbne
        rw [hj₀]
        rw [← hcon]
        have : (b : ℤ) + p - 1 - p + 1 = (b : ℤ) := by ring
        rw [this, Int.toNat_natCast]
      · rw [Finset.mem_Icc] at hbmem ⊢
        constructor <;> omega
    · have : (b : ℤ) + p - 1 - p + 1 = (b : ℤ) := by ring
      rw [this, Int.toNat_natCast]
  · intro k hk
    rw [Finset.mem_erase] at hk
    obtain ⟨hkne, hkmem⟩ := hk
    have h1 : 0 ≤ k - p + 1 := by rw [Finset.mem_Icc] at hkmem; omega
    have hcast : ((((k - p + 1).toNat : ℕ)) : ℝ) = (k : ℝ) - (p : ℝ) + 1 := by
      have hzi : (((k - p + 1).toNat : ℕ) : ℤ) = k - p + 1 := Int.toNat_of_nonneg h1
      have hreal : (((k - p + 1).toNat : ℕ) : ℝ) = ((k - p + 1 : ℤ) : ℝ) := by exact_mod_cast hzi
      rw [hreal]; push_cast; ring
    have hcastZ : ((k - p + 1).toNat : ℤ) = k - p + 1 := Int.toNat_of_nonneg h1
    have hsite : (p + (((k - p + 1).toNat : ℕ) : ℤ) - 1) = k := by
      rw [hcastZ]; ring
    have harg : ξ + ((k + Lsh k * qr : ℤ) : ℝ) * α
        = 2 * x + (((k - p + 1).toNat : ℝ) + (Lsh (p + (((k - p + 1).toNat : ℕ) : ℤ) - 1) : ℝ) * (qr : ℝ)) * α := by
      rw [hsite, hx, hcast]
      push_cast
      ring
    rw [harg]
    congr 3
    push_cast
    ring

/-- `ℓ * Δ r < 1/(10 * q n)`: the shift scale is tiny compared with the block length. -/
lemma ell_mul_Dr_lt {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    {n r : ℕ} (hnr : n ≤ r) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hℓb : 10 * (ℓ : ℝ) * (q r : ℝ) < (q (r + 1) : ℝ)) :
    (ℓ : ℝ) * Δ r < 1 / (10 * (q n : ℝ)) := by
  have hℓR : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ
  have hqrR : (q n : ℝ) ≤ (q r : ℝ) := by exact_mod_cast (hmono.monotone hnr)
  have h1 : Δ r < 1 / (q (r + 1) : ℝ) := hΔup r
  have hqrpos : (0 : ℝ) < (q r : ℝ) := by
    have := hqpos r; exact_mod_cast this
  have hnpos : (0 : ℝ) < (q n : ℝ) := by
    have := hqpos n; exact_mod_cast this
  have h3 : (ℓ : ℝ) / (q (r + 1) : ℝ) < (ℓ : ℝ) / (10 * (ℓ : ℝ) * (q r : ℝ)) := by
    apply div_lt_div_of_pos_left hℓR (by positivity) hℓb
  have h4 : (ℓ : ℝ) / (10 * (ℓ : ℝ) * (q r : ℝ)) = 1 / (10 * (q r : ℝ)) := by
    field_simp
  have h5 : 1 / (10 * (q r : ℝ)) ≤ 1 / (10 * (q n : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity); linarith
  calc (ℓ : ℝ) * Δ r < (ℓ : ℝ) * (1 / (q (r + 1) : ℝ)) := mul_lt_mul_of_pos_left h1 hℓR
    _ = (ℓ : ℝ) / (q (r + 1) : ℝ) := by ring
    _ < (ℓ : ℝ) / (10 * (ℓ : ℝ) * (q r : ℝ)) := h3
    _ = 1 / (10 * (q r : ℝ)) := h4
    _ ≤ 1 / (10 * (q n : ℝ)) := h5

/-- The shift part of the phase difference is at most `2 ℓ Δ r` away from an integer. -/
lemma nn_shift_le {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔpos : ∀ m, 0 < Δ m) {r : ℕ} {ℓ : ℕ}
    {c : ℕ → ℤ} (hc : ∀ j, |c j| ≤ (ℓ : ℤ) - 1) (j j₀ : ℕ) :
    nn ((((c j - c j₀) * (q r : ℤ) : ℤ) : ℝ) * α) ≤ 2 * (ℓ : ℝ) * Δ r := by
  have hcast : ∀ z : ℤ, ((|z| : ℤ) : ℝ) = |((z : ℤ) : ℝ)| := fun z => Int.cast_abs
  have hcc : |((c j - c j₀ : ℤ) : ℝ)| ≤ 2 * (ℓ : ℝ) := by
    have h6 : ((c j - c j₀ : ℤ) : ℝ) = (c j : ℝ) - (c j₀ : ℝ) := by push_cast; ring
    rw [h6]
    have h7 : |((c j : ℤ) : ℝ)| ≤ (ℓ : ℝ) - 1 := by
      have h := hc j
      have h2 : ((|c j| : ℤ) : ℝ) ≤ (ℓ : ℝ) - 1 := by
        have h' : ((|c j| : ℤ) : ℝ) ≤ ((ℓ : ℤ) : ℝ) - 1 := by exact_mod_cast h
        simpa using h'
      rwa [hcast] at h2
    have h8 : |((c j₀ : ℤ) : ℝ)| ≤ (ℓ : ℝ) - 1 := by
      have h := hc j₀
      have h2 : ((|c j₀| : ℤ) : ℝ) ≤ (ℓ : ℝ) - 1 := by
        have h' : ((|c j₀| : ℤ) : ℝ) ≤ ((ℓ : ℤ) : ℝ) - 1 := by exact_mod_cast h
        simpa using h'
      rwa [hcast] at h2
    calc |((c j : ℤ) : ℝ) - ((c j₀ : ℤ) : ℝ)|
        ≤ |((c j : ℤ) : ℝ)| + |((c j₀ : ℤ) : ℝ)| := abs_sub _ _
      _ ≤ ((ℓ:ℝ) - 1) + ((ℓ:ℝ) - 1) := by linarith
      _ ≤ 2 * (ℓ : ℝ) := by linarith
  have h1 : ((((c j - c j₀) * (q r : ℤ) : ℤ) : ℝ) * α)
      = ((c j - c j₀ : ℤ) : ℝ) * ((q r : ℝ) * α) := by push_cast; ring
  rw [h1]
  calc nn (((c j - c j₀ : ℤ) : ℝ) * ((q r : ℝ) * α))
      ≤ |((c j - c j₀ : ℤ) : ℝ) * ((q r : ℝ) * α)
          - (((c j - c j₀ : ℤ) * (round ((q r : ℝ) * α)) : ℤ) : ℝ)| :=
        nn_le_abs_sub_intCast _ _
    _ = |((c j - c j₀ : ℤ) : ℝ)| * |(q r : ℝ) * α - (round ((q r : ℝ) * α) : ℝ)| := by
        have hfac : ((c j - c j₀ : ℤ) : ℝ) * ((q r : ℝ) * α)
            - (((c j - c j₀ : ℤ) * (round ((q r : ℝ) * α)) : ℤ) : ℝ)
            = ((c j - c j₀ : ℤ) : ℝ)
              * ((q r : ℝ) * α - (round ((q r : ℝ) * α) : ℝ)) := by
          push_cast; ring
        rw [hfac, abs_mul]
    _ = |((c j - c j₀ : ℤ) : ℝ)| * Δ r := by
        congr 1
        rw [hΔeq r, fracDist]
    _ ≤ (2 * (ℓ : ℝ)) * Δ r := mul_le_mul_of_nonneg_right hcc (le_of_lt (hΔpos r))

lemma site_sep {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q) (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hbase : ∀ d : ℕ, 1 ≤ d → d < q 0 →
      1 / (2 * (q 0 : ℝ)) ≤ fracDist ((d : ℝ) * α))
    {n r : ℕ} (hnr : n ≤ r) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hℓb : 10 * (ℓ : ℝ) * (q r : ℝ) < (q (r + 1) : ℝ))
    {x : ℝ} {c : ℕ → ℤ} (hc : ∀ j, |c j| ≤ (ℓ : ℤ) - 1)
    {j j₀ : ℕ} (hj : j ∈ Finset.Icc 1 (q n)) (hj₀ : j₀ ∈ Finset.Icc 1 (q n)) (hjne : j ≠ j₀) :
    (3 : ℝ) / (10 * (q n : ℝ)) ≤ nn (x + ((j : ℝ) + (c j : ℝ) * ((q r : ℤ) : ℝ)) * α
        - (x + ((j₀ : ℝ) + (c j₀ : ℝ) * ((q r : ℤ) : ℝ)) * α)) := by
  have hdiff : (x + ((j : ℝ) + (c j : ℝ) * ((q r : ℤ) : ℝ)) * α)
      - (x + ((j₀ : ℝ) + (c j₀ : ℝ) * ((q r : ℤ) : ℝ)) * α)
      = (((j : ℝ) - (j₀ : ℝ)) * α) + ((((c j - c j₀) * (q r : ℤ) : ℤ) : ℝ) * α) := by
    push_cast; ring
  rw [hdiff]
  have hgen : ∀ d : ℕ, 1 ≤ d → d < q n → (1:ℝ) / (2 * (q n : ℝ)) ≤ nn ((d:ℝ) * α) :=
    fun d h1 h2 => sep_scale hqpos hmono hΔpos hΔeq hΔlo hbest hbase h1 h2
  have hsepA : (1:ℝ) / (2 * (q n : ℝ)) ≤ nn (((j : ℝ) - (j₀ : ℝ)) * α) := by
    rw [Finset.mem_Icc] at hj hj₀
    rcases lt_or_ge j j₀ with hlt | hle
    · have hcast : ((j : ℝ) - (j₀ : ℝ)) * α = -(((j₀ - j : ℕ) : ℝ) * α) := by
        push_cast [Nat.cast_sub hlt.le]; ring
      rw [hcast, nn_neg']
      exact hgen (j₀ - j) (by omega) (by omega)
    · have hlt' : j₀ < j := lt_of_le_of_ne hle (Ne.symm hjne)
      have hcast : ((j : ℝ) - (j₀ : ℝ)) * α = ((j - j₀ : ℕ) : ℝ) * α := by
        push_cast [Nat.cast_sub hle]; ring
      rw [hcast]
      exact hgen (j - j₀) (by omega) (by omega)
  have hshift := nn_shift_le hΔeq hΔpos hc j j₀ (r := r) (ℓ := ℓ)
  have hmain : (1:ℝ) / (2 * (q n : ℝ)) - 2 * (ℓ : ℝ) * Δ r
      ≤ nn (((j : ℝ) - (j₀ : ℝ)) * α + (((c j - c j₀) * (q r : ℤ) : ℤ) : ℝ) * α) := by
    have h := nn_add_le (((j : ℝ) - (j₀ : ℝ)) * α) ((((c j - c j₀) * (q r : ℤ) : ℤ) : ℝ) * α)
    have hneg : nn (-((((c j - c j₀) * (q r : ℤ) : ℤ) : ℝ) * α)) ≤ 2 * (ℓ : ℝ) * Δ r := by
      rw [nn_neg']; exact hshift
    have hsub : nn (((j : ℝ) - (j₀ : ℝ)) * α)
        = nn (((j : ℝ) - (j₀ : ℝ)) * α + (((c j - c j₀) * (q r : ℤ) : ℤ) : ℝ) * α
            + (-((((c j - c j₀) * (q r : ℤ) : ℤ) : ℝ) * α))) := by ring_nf
    rw [hsub] at hsepA
    have h2 := nn_add_le (((j : ℝ) - (j₀ : ℝ)) * α + (((c j - c j₀) * (q r : ℤ) : ℤ) : ℝ) * α)
      (-((((c j - c j₀) * (q r : ℤ) : ℤ) : ℝ) * α))
    linarith
  have hkey : 2 * (ℓ : ℝ) * Δ r ≤ 1 / (5 * (q n : ℝ)) := by
    have h1 := ell_mul_Dr_lt hqpos hmono hΔup hnr hℓ hℓb
    have h2 : 2 * (ℓ : ℝ) * Δ r = 2 * ((ℓ : ℝ) * Δ r) := by ring
    rw [h2]
    have h3 : 2 * (1 / (10 * (q n : ℝ))) = 1 / (5 * (q n : ℝ)) := by ring
    linarith
  have h3 : (3:ℝ) / (10 * (q n : ℝ)) = 1 / (2 * (q n : ℝ)) - 1 / (5 * (q n : ℝ)) := by
    field_simp; ring
  rw [h3]
  linarith

lemma nn_natCast_mul_le (n : ℕ) (w : ℝ) : nn ((n : ℝ) * w) ≤ (n : ℝ) * nn w := by
  induction n with
  | zero => simp [nn]
  | succ k ih =>
    have h : ((k + 1 : ℕ) : ℝ) * w = (k : ℝ) * w + w := by push_cast; ring
    rw [h]
    calc nn ((k : ℝ) * w + w) ≤ nn ((k : ℝ) * w) + nn w := nn_add_le _ _
      _ ≤ (k : ℝ) * nn w + nn w := by linarith [nn_nonneg w]
      _ = ((k + 1 : ℕ) : ℝ) * nn w := by push_cast; ring

lemma nn_intCast_mul_le (m : ℤ) (w : ℝ) : nn ((m : ℝ) * w) ≤ ((m.natAbs : ℕ) : ℝ) * nn w := by
  have key : ∀ (n : ℕ), nn (((n : ℤ) : ℝ) * w) ≤ ((n : ℝ) * nn w) := by
    intro n
    have h1 : (((n : ℤ) : ℝ) * w) = (n : ℝ) * w := by push_cast; ring
    rw [h1]; exact nn_natCast_mul_le n w
  rcases Int.natAbs_eq m with h | h
  · conv_lhs => rw [h]
    exact key _
  · conv_lhs => rw [h]
    have h2 : ((-((m.natAbs : ℤ)) : ℤ) : ℝ) * w = -(((((m.natAbs : ℤ)) : ℝ)) * w) := by
      push_cast; ring
    rw [h2, nn_neg']
    exact key _

lemma nn_int_mul_qr_le {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {r : ℕ} (hΔr : 0 < Δ r) {m : ℤ} (hm : |m| ≤ (ℓ : ℤ) - 1) :
    nn ((m : ℝ) * (((q r : ℤ) : ℝ) * α)) ≤ ((ℓ : ℝ) - 1) * Δ r := by
  have h1 : nn ((m : ℝ) * (((q r : ℤ) : ℝ) * α))
      ≤ ((m.natAbs : ℕ) : ℝ) * nn (((q r : ℤ) : ℝ) * α) := nn_intCast_mul_le m _
  have h2 : ((m.natAbs : ℕ) : ℝ) ≤ (ℓ : ℝ) - 1 := by
    have h5 : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by
      simp
    rw [h5]
    have h3 : ((|m| : ℤ) : ℝ) ≤ (ℓ : ℝ) - 1 := by exact_mod_cast hm
    rwa [Int.cast_abs] at h3
  have h4 : nn (((q r : ℤ) : ℝ) * α) = Δ r := by
    rw [hΔeq r, fracDist_eq_nn]
    congr 1
  calc nn ((m : ℝ) * (((q r : ℤ) : ℝ) * α))
        ≤ ((m.natAbs : ℕ) : ℝ) * nn (((q r : ℤ) : ℝ) * α) := h1
    _ = ((m.natAbs : ℕ) : ℝ) * Δ r := by rw [h4]
    _ ≤ ((ℓ : ℝ) - 1) * Δ r := mul_le_mul_of_nonneg_right h2 (le_of_lt hΔr)

lemma S_le_iff_nn_le' (a b : ℝ) : S a ≤ S b ↔ nn a ≤ nn b := by
  have m1 : Real.pi * nn a ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [Set.mem_Icc]
    exact ⟨by nlinarith [Real.pi_pos, nn_nonneg a], by nlinarith [Real.pi_pos, nn_le_half a]⟩
  have m2 : Real.pi * nn b ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [Set.mem_Icc]
    exact ⟨by nlinarith [Real.pi_pos, nn_nonneg b], by nlinarith [Real.pi_pos, nn_le_half b]⟩
  rw [S_eq_sin_nn', S_eq_sin_nn', Real.strictMonoOn_sin.le_iff_le m1 m2]
  constructor
  · intro h; nlinarith [Real.pi_pos, h]
  · intro h; nlinarith [Real.pi_pos, h]

theorem irrat_blk_shift_master {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q) (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) → Δ m ≤ fracDist ((k : ℝ) * α))
    (hbase : ∀ d : ℕ, 1 ≤ d → d < q 0 →
      1 / (2 * (q 0 : ℝ)) ≤ fracDist ((d : ℝ) * α))
    {n r : ℕ} (hnr : n ≤ r) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hℓb : 10 * (ℓ : ℝ) * (q r : ℝ) < (q (r + 1) : ℝ))
    {p : ℤ} {ξ : ℝ} {k₀ : ℤ} {Lsh : ℤ → ℤ}
    (hLsh : ∀ k : ℤ, |Lsh k| ≤ (ℓ : ℤ) - 1)
    (hk₀ : k₀ ∈ Finset.Icc p (p + (q n : ℤ) - 1))
    (hmin : ∀ k ∈ Finset.Icc p (p + (q n : ℤ) - 1),
      |Real.sin (Real.pi * (ξ + ((k + Lsh k * (q r : ℤ) : ℤ) : ℝ) * α))| ≥
        |Real.sin (Real.pi * (ξ + ((k₀ + Lsh k₀ * (q r : ℤ) : ℤ) : ℝ) * α))|) :
    |∑ k ∈ (Finset.Icc p (p + (q n : ℤ) - 1)).erase k₀,
        Real.log |Real.sin (Real.pi * (ξ + ((k + Lsh k * (q r : ℤ) : ℤ) : ℝ) * α))|
      + ((q n : ℝ) - 1) * Real.log 2|
      ≤ Real.log (q n : ℝ)
        + 32 * ((Δ n + (ℓ : ℝ) * Δ r) * (q n : ℝ) * Real.log (q n : ℝ)) := by
  classical
  have hLpos : 0 < q n := hqpos n
  have hLposR : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hLpos
  have hL1 : 1 ≤ q n := by
    have h0 : 1 ≤ q 0 := hqpos 0
    have h := hmono.monotone (Nat.zero_le n)
    omega
  let L : ℕ := q n
  let pn : ℤ := round ((L : ℝ) * α)
  let xx : ℝ := (ξ + ((p : ℝ) - 1) * α) / 2
  let cc : ℕ → ℤ := fun j => Lsh (p + (j : ℤ) - 1)
  let ph : ℕ → ℝ := fun j => 2 * xx + ((j : ℝ) + (cc j : ℝ) * ((q r : ℤ) : ℝ)) * α
  let j₀ : ℕ := (k₀ - p + 1).toNat
  have hcop : Nat.Coprime pn.natAbs L :=
    coprime_round hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hbase (n := n)
  have hLR : (0 : ℝ) < (L : ℝ) := hLposR
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLR
  have hΔnval : Δ n = |(L : ℝ) * α - (pn : ℝ)| := by
    rw [hΔeq n, fracDist]
  have hk₀I : p ≤ k₀ ∧ k₀ ≤ p + (q n : ℤ) - 1 := by
    have h := hk₀
    rw [Finset.mem_Icc] at h
    exact h
  have hj₀Z : ((j₀ : ℕ) : ℤ) = k₀ - p + 1 := by
    simp only [j₀]
    exact Int.toNat_of_nonneg (by omega)
  have hj₀mem : j₀ ∈ Finset.Icc 1 L := by
    rw [Finset.mem_Icc]
    exact ⟨by omega, by omega⟩
  have hSeq : ∀ j : ℕ,
      |Real.sin (Real.pi * (ξ + (((p + (j : ℤ) - 1)
        + Lsh (p + (j : ℤ) - 1) * (q r : ℤ) : ℤ) : ℝ) * α))| = S (ph j) := by
    intro j
    have h1 : ξ + (((p + (j : ℤ) - 1) + Lsh (p + (j : ℤ) - 1) * (q r : ℤ) : ℤ) : ℝ) * α
        = ph j := by
      dsimp only [ph, xx, cc]
      push_cast
      ring
    rw [h1]
    rfl
  rw [sum_block_shift_reindex (q n) p k₀ ξ α (q r : ℤ) Lsh hk₀]
  simp only [hSeq]
  have hminS : ∀ j ∈ Finset.Icc 1 L, S (ph j₀) ≤ S (ph j) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hsite : p + (j : ℤ) - 1 ∈ Finset.Icc p (p + (L : ℤ) - 1) := by
      rw [Finset.mem_Icc]; constructor <;> omega
    have h := hmin (p + (j : ℤ) - 1) hsite
    have hsite₀ : p + (j₀ : ℤ) - 1 = k₀ := by
      have h1 := hj₀Z
      omega
    have e2 : |Real.sin (Real.pi * (ξ + (((k₀ + Lsh k₀ * (q r : ℤ) : ℤ) : ℝ) * α)))|
        = S (ph j₀) := by
      rw [← hsite₀]
      exact hSeq j₀
    rw [hSeq j, e2] at h
    exact h
  have hnnmin : ∀ j ∈ Finset.Icc 1 L, nn (ph j₀) ≤ nn (ph j) :=
    fun j hj => (S_le_iff_nn_le' (ph j₀) (ph j)).mp (hminS j hj)
  have hsite_sep : ∀ j ∈ Finset.Icc 1 L, j ≠ j₀ →
      (3 : ℝ) / (10 * (L : ℝ)) ≤ nn (ph j - ph j₀) := by
    intro j hj hjne
    exact site_sep hqpos hmono hΔpos hΔeq hΔup hΔlo hbest hbase hnr hℓ hℓb
      (x := 2 * xx) (c := cc) (fun j => hLsh _) hj hj₀mem hjne
  have hnnφ : ∀ j ∈ Finset.Icc 1 L, j ≠ j₀ → (3 : ℝ) / (20 * (L : ℝ)) ≤ nn (ph j) := by
    intro j hj hjne
    have hsep := hsite_sep j hj hjne
    have h2 : nn (ph j - ph j₀) ≤ nn (ph j) + nn (ph j₀) := nn_sub_le' _ _
    have h3 : nn (ph j₀) ≤ nn (ph j) := hnnmin j hj
    have h4 : (3 : ℝ) / (10 * (L : ℝ)) ≤ 2 * nn (ph j) := by linarith
    have h5 : (3 : ℝ) / (10 * (L : ℝ)) = 2 * (3 / (20 * (L : ℝ))) := by
      field_simp
      ring
    linarith
  have hSpos : ∀ j ∈ Finset.Icc 1 L, j ≠ j₀ → 0 < S (ph j) := by
    intro j hj hjne
    have h := hnnφ j hj hjne
    have h2 := two_mul_nn_le_S' (ph j)
    have h3 : (0 : ℝ) < 3 / (20 * (L : ℝ)) := by
      apply div_pos (by norm_num)
      linarith
    linarith
  rcases eq_or_lt_of_le hL1 with hL1eq | hL2
  · have hq1 : q n = 1 := hL1eq.symm
    rw [hq1] at hk₀ ⊢
    have hk : k₀ = p := by rw [Finset.mem_Icc] at hk₀; omega
    rw [hk]
    have htoNat : (p - p + 1).toNat = 1 := by
      have h : p - p + 1 = (1 : ℤ) := by ring
      rw [h]; rfl
    rw [htoNat]
    simp
  · show |∑ j ∈ (Finset.Icc 1 L).erase j₀, Real.log (S (ph j)) + ((L : ℝ) - 1) * Real.log 2|
        ≤ Real.log (L : ℝ)
          + 32 * ((Δ n + (ℓ : ℝ) * Δ r) * (L : ℝ) * Real.log (L : ℝ))
    let νa : ℕ → ℝ := fun j => 2 * xx + (j : ℝ) * ((pn : ℝ) / (L : ℝ))
    let Bb : ℕ → ℝ := fun j => S (νa j)
    let ν : ℕ → ℝ := fun j => nn (νa j)
    let η : ℝ := Δ n + (ℓ : ℝ) * Δ r
    have hηpos : 0 < η := by
      show 0 < Δ n + (ℓ : ℝ) * Δ r
      have h1 := hΔpos n
      have h2 : (0 : ℝ) ≤ (ℓ : ℝ) * Δ r :=
        mul_nonneg (Nat.cast_nonneg ℓ) (le_of_lt (hΔpos r))
      linarith
    have hηL : η * (L : ℝ) ≤ 11 / 10 := by
      have h1 : Δ n * (L : ℝ) < 1 := by
        have h2 : Δ n < 1 / (q (n + 1) : ℝ) := hΔup n
        have h3 : (L : ℝ) < (q (n + 1) : ℝ) := by
          have := hmono (Nat.lt_succ_self n)
          exact_mod_cast this
        calc Δ n * (L : ℝ) < (1 / (q (n + 1) : ℝ)) * L := mul_lt_mul_of_pos_right h2 hLposR
          _ = (L : ℝ) / (q (n + 1) : ℝ) := by ring
          _ < 1 := by
              rw [div_lt_one (by exact_mod_cast (hqpos (n + 1)))]
              exact h3
      have h2 : (ℓ : ℝ) * Δ r * (L : ℝ) < 1 / 10 := by
        have h3 := ell_mul_Dr_lt hqpos hmono hΔup hnr hℓ hℓb
        calc (ℓ : ℝ) * Δ r * (L : ℝ) < (1 / (10 * (L : ℝ))) * L :=
              mul_lt_mul_of_pos_right h3 hLposR
          _ = 1 / 10 := by field_simp
      have h5 : η * (L : ℝ) = Δ n * L + (ℓ : ℝ) * Δ r * L := by
        show (Δ n + (ℓ : ℝ) * Δ r) * (L : ℝ) = Δ n * L + (ℓ : ℝ) * Δ r * L
        ring
      rw [h5]; linarith
    have hBsin : ∀ j, Bb j = Real.sin (Real.pi * ν j) := by
      intro j; dsimp only [Bb, ν]; exact S_eq_sin_nn' _
    obtain ⟨j₁, hj₁mem, hj₁min⟩ :=
      Finset.exists_min_image (Finset.Icc 1 L) Bb ⟨1, by rw [Finset.mem_Icc]; omega⟩
    have hminν : ∀ j ∈ Finset.Icc 1 L, ν j₁ ≤ ν j :=
      fun j hj => (S_le_iff_nn_le' (νa j₁) (νa j)).mp (hj₁min j hj)
    have hgrid := grid_sep (q := L) hLpos hcop (x := xx) (k₁ := j₁) hj₁mem hminν
    have hgrid1 : ∀ j ∈ Finset.Icc 1 L, j ≠ j₁ → 1 / (2 * (L : ℝ)) ≤ ν j :=
      fun j hj hjne => hgrid.1 j hj hjne
    have hgrid2 : ν j₁ ≤ 1 / (2 * (L : ℝ)) := hgrid.2
    have hνpos : ∀ j ∈ Finset.Icc 1 L, j ≠ j₁ → 0 < ν j := by
      intro j hj hjne
      have h := hgrid1 j hj hjne
      have h2 : (0 : ℝ) < 1 / (2 * (L : ℝ)) := one_div_pos.mpr (by linarith)
      linarith
    have hBbpos : ∀ j ∈ Finset.Icc 1 L, j ≠ j₁ → 0 < Bb j := by
      intro j hj hjne
      have h := hgrid1 j hj hjne
      have h2 : 2 * ν j ≤ Bb j := two_mul_nn_le_S' (νa j)
      have h3 : (1 : ℝ) / (L : ℝ) ≤ 2 * ν j := by
        have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLR
        have h4 : (2 : ℝ) * (1 / (2 * (L : ℝ))) = 1 / (L : ℝ) := by field_simp
        linarith
      have h4 : (0 : ℝ) < 1 / (L : ℝ) := one_div_pos.mpr hLR
      linarith
    have hbprod : ∀ k : ℕ,
        |Real.sin (2 * Real.pi * (xx + (k : ℝ) * ((pn : ℝ) / (2 * (L : ℝ)))))| = Bb k := by
      intro k
      have harg : 2 * Real.pi * (xx + (k : ℝ) * ((pn : ℝ) / (2 * (L : ℝ)))) = Real.pi * νa k := by
        show 2 * Real.pi * (xx + (k : ℝ) * ((pn : ℝ) / (2 * (L : ℝ))))
          = Real.pi * (2 * xx + (k : ℝ) * ((pn : ℝ) / (L : ℝ)))
        have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLR
        field_simp
      rw [harg]
      rfl
    have hprod2 : ∏ j ∈ Finset.Icc 1 L, (2 * Bb j)
        = 2 * |Real.sin (2 * Real.pi * ((L : ℝ) * xx))| := by
      have hprod := rational_block_prod pn L hLpos hcop xx
      rw [Finset.prod_congr rfl (fun k _ => (hbprod k))] at hprod
      rw [Finset.prod_mul_distrib, hprod, Finset.prod_const, Nat.card_Icc]
      have hcard : (L + 1 - 1 : ℕ) = L := by omega
      rw [hcard]
      have key : (2 : ℝ) ^ L * (|Real.sin (2 * Real.pi * ((L : ℝ) * xx))| * (2 / (2 : ℝ) ^ L))
          = 2 * |Real.sin (2 * Real.pi * ((L : ℝ) * xx))| := by
        have hne : (2 : ℝ) ^ L ≠ 0 := by positivity
        field_simp
      exact key
    let R : ℝ := ∑ j ∈ (Finset.Icc 1 L).erase j₁, Real.log (2 * Bb j)
    have hRlog : R = Real.log (∏ j ∈ (Finset.Icc 1 L).erase j₁, (2 * Bb j)) := by
      refine (Real.log_prod (f := fun j => 2 * Bb j) (s := (Finset.Icc 1 L).erase j₁) ?_).symm
      intro j hj
      have h1 : j ∈ Finset.Icc 1 L := Finset.mem_of_mem_erase hj
      have h2 : j ≠ j₁ := Finset.ne_of_mem_erase hj
      have h3 : 0 < Bb j := hBbpos j h1 h2
      positivity
    have hprod_eq : ∏ j ∈ (Finset.Icc 1 L).erase j₁,
        (2 * S (2 * xx + (j : ℝ) * ((pn : ℝ) / (L : ℝ))))
        = ∏ j ∈ (Finset.Icc 1 L).erase j₁, (2 * Bb j) := rfl
    have hRle : R ≤ Real.log (L : ℝ) := by
      rw [hRlog]
      have h := (Work.TMC16Core.Trig.rat_log_prod_bounds (L := L) hLpos hcop xx hj₁mem hminν).2
      rwa [hprod_eq] at h
    have hRge : Real.log (2 * (L : ℝ) / Real.pi) ≤ R := by
      rw [hRlog]
      have h := (Work.TMC16Core.Trig.rat_log_prod_bounds (L := L) hLpos hcop xx hj₁mem hminν).1
      rwa [hprod_eq] at h
    have hphdiff : ∀ j ∈ Finset.Icc 1 L, nn (ph j - νa j) ≤ η := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      have hsplit : ph j - νa j = ((j : ℝ) * (α - (pn : ℝ) / (L : ℝ)))
          + ((cc j : ℝ) * (((q r : ℤ) : ℝ) * α)) := by
        dsimp only [ph, νa]; ring
      rw [hsplit]
      have h1 : nn (((j : ℝ) * (α - (pn : ℝ) / (L : ℝ)))
          + ((cc j : ℝ) * (((q r : ℤ) : ℝ) * α)))
          ≤ nn ((j : ℝ) * (α - (pn : ℝ) / (L : ℝ)))
            + nn ((cc j : ℝ) * (((q r : ℤ) : ℝ) * α)) := nn_add_le _ _
      have h2 : nn ((j : ℝ) * (α - (pn : ℝ) / (L : ℝ))) ≤ Δ n := by
        have h3 : nn ((j : ℝ) * (α - (pn : ℝ) / (L : ℝ)))
            ≤ |(j : ℝ) * (α - (pn : ℝ) / (L : ℝ))| := nn_le_abs _
        have h4 : |(j : ℝ) * (α - (pn : ℝ) / (L : ℝ))|
            = (j : ℝ) * |α - (pn : ℝ) / (L : ℝ)| := by
          rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg j)]
        have h5 : |α - (pn : ℝ) / (L : ℝ)| = Δ n / (L : ℝ) := by
          have h6 : α - (pn : ℝ) / (L : ℝ) = ((L : ℝ) * α - (pn : ℝ)) / (L : ℝ) := by
            have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLR
            field_simp
          rw [h6, abs_div, abs_of_pos hLposR, ← hΔnval]
        have h7 : (j : ℝ) * (Δ n / (L : ℝ)) ≤ Δ n := by
          have h8 : (j : ℝ) ≤ (L : ℝ) := by exact_mod_cast hj.2
          have h9 : 0 ≤ Δ n := le_of_lt (hΔpos n)
          rw [mul_div_assoc', div_le_iff₀ hLposR]
          nlinarith
        rw [h4, h5] at h3
        exact le_trans h3 h7
      have h3 : nn ((cc j : ℝ) * (((q r : ℤ) : ℝ) * α)) ≤ ((ℓ : ℝ) - 1) * Δ r :=
        nn_int_mul_qr_le hΔeq hℓ (hΔpos r) (hLsh _)
      have h4 : Δ n + ((ℓ : ℝ) - 1) * Δ r ≤ η := by
        dsimp only [η]
        have h5 : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
        nlinarith [le_of_lt (hΔpos r)]
      linarith
    let F : Finset ℕ := (Finset.Icc 1 L).erase j₀
    let G : Finset ℕ := F.erase j₁
    let bad : Finset ℕ := G.filter (fun j => Real.sin (Real.pi * ν j) < 2 * Real.pi * η)
    let β : ℝ := ∑ j ∈ G, (Real.sin (Real.pi * ν j))⁻¹
    let comp : ℝ := ∑ j ∈ G, (Real.log (S (ph j)) - Real.log (Bb j))
    let T : ℝ := ∑ j ∈ F, Real.log (S (ph j)) + ((L : ℝ) - 1) * Real.log 2
    have hGF : G ⊆ F := fun j hj => Finset.mem_of_mem_erase (show j ∈ F.erase j₁ from hj)
    have hGsub : G ⊆ Finset.Icc 1 L := by
      intro j hj
      have h1 : j ∈ F := hGF hj
      exact Finset.mem_of_mem_erase (show j ∈ (Finset.Icc 1 L).erase j₀ from h1)
    have hGmem : ∀ j ∈ G, j ∈ Finset.Icc 1 L ∧ j ≠ j₀ ∧ j ≠ j₁ := by
      intro j hj
      have h1 : j ∈ F := hGF hj
      have h2 : j ∈ (Finset.Icc 1 L).erase j₀ := h1
      have h3 : j ∈ F.erase j₁ := hj
      exact ⟨Finset.mem_of_mem_erase h2, Finset.ne_of_mem_erase h2, Finset.ne_of_mem_erase h3⟩
    have hbadsub : bad ⊆ G := fun j hj => (Finset.mem_filter.mp hj).1
    have hdiff : ∀ j ∈ G, |nn (ph j) - ν j| ≤ η := by
      intro j hj
      obtain ⟨hjI, _, _⟩ := hGmem j hj
      have h1 : |nn (ph j) - ν j| ≤ nn (ph j - νa j) := abs_nn_sub_nn_le _ _
      have h2 : nn (ph j - νa j) ≤ η := hphdiff j hjI
      linarith
    have hτ0 : ∀ j ∈ G, 0 < nn (ph j) := by
      intro j hj
      obtain ⟨hjI, hjn0, _⟩ := hGmem j hj
      have h1 := hnnφ j hjI hjn0
      have h2 : (0 : ℝ) < 3 / (20 * (L : ℝ)) := by positivity
      linarith
    have hτh : ∀ j ∈ G, nn (ph j) ≤ 1 / 2 := fun j _ => nn_le_half _
    have hτsep : ∀ j ∈ G, 3 / (20 * (L : ℝ)) ≤ nn (ph j) := by
      intro j hj
      obtain ⟨hjI, hjn0, _⟩ := hGmem j hj
      exact hnnφ j hjI hjn0
    have hν0 : ∀ j ∈ G, 0 < ν j := by
      intro j hj
      obtain ⟨hjI, _, hjn1⟩ := hGmem j hj
      exact hνpos j hjI hjn1
    have hνh : ∀ j ∈ G, ν j ≤ 1 / 2 := fun j _ => nn_le_half _
    have hνsep : ∀ j ∈ G, 1 / (2 * (L : ℝ)) ≤ ν j := by
      intro j hj
      obtain ⟨hjI, _, hjn1⟩ := hGmem j hj
      exact hgrid1 j hjI hjn1
    have hgood : ∀ j ∈ G, j ∉ bad → 2 * Real.pi * η ≤ Real.sin (Real.pi * ν j) := by
      intro j hj hjnb
      by_contra hcon
      exact hjnb (Finset.mem_filter.mpr ⟨hj, lt_of_not_ge hcon⟩)
    have hbad' : ∀ j ∈ bad, Real.sin (Real.pi * ν j) ≤ 2 * Real.pi * η :=
      fun j hj => le_of_lt (Finset.mem_filter.mp hj).2
    have hcomp_bound := comp_sum_sharp (L := L) hL2 (G := G) (τ := fun j => nn (ph j)) (ν := ν)
      (η := η) (bad := bad) hbadsub hηpos hηL hτ0 hτh hτsep hν0 hνh hνsep hdiff hgood hbad'
    have hcomp_eq : comp = ∑ j ∈ G,
        (Real.log (Real.sin (Real.pi * (nn (ph j)))) - Real.log (Real.sin (Real.pi * ν j))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [S_eq_sin_nn', hBsin j]
    have hcomp_abs : |comp|
        ≤ 2 * Real.pi * η * β + Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3)
            * (bad.card : ℝ) := by
      rw [hcomp_eq, show β = ∑ j ∈ G, (Real.sin (Real.pi * ν j))⁻¹ from rfl]
      exact hcomp_bound
    have hstep1 : ∑ j ∈ G, (Real.sin (Real.pi * ν j))⁻¹ ≤ ∑ j ∈ G, (2 * ν j)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hjI, _, hjn1⟩ := hGmem j hj
      have h4 : 0 < Real.sin (Real.pi * ν j) := by
        simpa only [Bb, ν, S_eq_sin_nn'] using hBbpos j hjI hjn1
      have h5 : 2 * ν j ≤ Real.sin (Real.pi * ν j) := by
        simpa only [Bb, ν, S_eq_sin_nn'] using two_mul_nn_le_S' (νa j)
      have h6 : 0 < 2 * ν j := by linarith [hνpos j hjI hjn1]
      exact (inv_le_inv₀ h4 h6).mpr h5
    have hstep2 : ∑ j ∈ G, (2 * ν j)⁻¹ ≤ ∑ j ∈ (Finset.Icc 1 L).erase j₁, (2 * ν j)⁻¹ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (f := fun j => (2 * ν j)⁻¹) (s := G)
        (t := (Finset.Icc 1 L).erase j₁)
      · intro j hj
        have h1 : j ∈ F := Finset.mem_of_mem_erase (show j ∈ F.erase j₁ from hj)
        have h2 : j ≠ j₁ := Finset.ne_of_mem_erase (show j ∈ F.erase j₁ from hj)
        refine Finset.mem_erase.mpr ⟨h2, ?_⟩
        exact Finset.mem_of_mem_erase (show j ∈ (Finset.Icc 1 L).erase j₀ from h1)
      · intro j hj _
        have h2 : j ∈ Finset.Icc 1 L := Finset.mem_of_mem_erase hj
        have h3 : j ≠ j₁ := Finset.ne_of_mem_erase hj
        have h4 : 0 < ν j := hνpos j h2 h3
        positivity
    have hstep3 : ∑ j ∈ (Finset.Icc 1 L).erase j₁, (2 * ν j)⁻¹
        = (2 : ℝ)⁻¹ * ∑ j ∈ (Finset.Icc 1 L).erase j₁, (ν j)⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [mul_inv]
    have hstep4 : ∑ j ∈ (Finset.Icc 1 L).erase j₁, (ν j)⁻¹
        ≤ 4 * (L : ℝ) * (1 + Real.log (L : ℝ)) :=
      grid_sum_bound (q := L) hLpos hcop xx hj₁mem hminν
    have hβ1 : β ≤ 2 * (L : ℝ) * (1 + Real.log (L : ℝ)) := by
      show (∑ j ∈ G, (Real.sin (Real.pi * ν j))⁻¹) ≤ 2 * (L : ℝ) * (1 + Real.log (L : ℝ))
      linarith [hstep1, hstep2, hstep3]
    have hβ2 : β ≤ ((L : ℝ) - 1) * (L : ℝ) := by
      have hpt : ∀ j ∈ G, (Real.sin (Real.pi * ν j))⁻¹ ≤ (L : ℝ) := by
        intro j hj
        obtain ⟨hjI, _, hjn1⟩ := hGmem j hj
        have h6 : 2 * ν j ≤ Real.sin (Real.pi * ν j) := by
          simpa only [Bb, ν, S_eq_sin_nn'] using two_mul_nn_le_S' (νa j)
        have h4a : 0 < ν j := hνpos j hjI hjn1
        have h4 : 0 < Real.sin (Real.pi * ν j) := by linarith
        have h7 := hgrid1 j hjI hjn1
        have h8 : (2 : ℝ) * (1 / (2 * (L : ℝ))) = 1 / (L : ℝ) := by
          field_simp
        have h5 : (1 : ℝ) / (L : ℝ) ≤ Real.sin (Real.pi * ν j) := by linarith
        have h9 : (0 : ℝ) < (1 : ℝ) / (L : ℝ) := one_div_pos.mpr hLR
        have h10 : (Real.sin (Real.pi * ν j))⁻¹ ≤ ((1 : ℝ) / (L : ℝ))⁻¹ :=
          (inv_le_inv₀ h4 h9).mpr h5
        rwa [one_div, inv_inv] at h10
      have h1 : ∑ j ∈ G, (Real.sin (Real.pi * ν j))⁻¹ ≤ ∑ _j ∈ G, (L : ℝ) :=
        Finset.sum_le_sum hpt
      have h2 : ∑ _j ∈ G, (L : ℝ) = (G.card : ℝ) * (L : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have h3 : G.card ≤ L - 1 := by
        have h4 : G.card ≤ F.card := Finset.card_le_card hGF
        have h5 : F.card = L - 1 := by
          dsimp only [F]; rw [Finset.card_erase_of_mem hj₀mem, Nat.card_Icc]; omega
        omega
      have h4 : (G.card : ℝ) ≤ (L : ℝ) - 1 := by
        have h5 : (G.card : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by exact_mod_cast h3
        rw [Nat.cast_sub (by omega : 1 ≤ L)] at h5
        push_cast at h5
        linarith
      show (∑ j ∈ G, (Real.sin (Real.pi * ν j))⁻¹) ≤ ((L : ℝ) - 1) * (L : ℝ)
      rw [h2] at h1
      nlinarith [h1, h4, hLposR.le]
    have hbad_sub : bad ⊆ (Finset.Icc 1 L).filter (fun k => ν k < Real.pi * η) := by
      intro j hj
      have hjG : j ∈ G := hbadsub hj
      have hjsin : Real.sin (Real.pi * ν j) < 2 * Real.pi * η := (Finset.mem_filter.mp hj).2
      obtain ⟨hjI, _, _⟩ := hGmem j hjG
      rw [Finset.mem_filter]
      refine ⟨hjI, ?_⟩
      have h2 : 2 * ν j ≤ Real.sin (Real.pi * ν j) := by
        simpa only [Bb, ν, S_eq_sin_nn'] using two_mul_nn_le_S' (νa j)
      linarith
    have hj₁bad : j₁ ∉ bad := by
      intro hcon
      have h1 : j₁ ∈ G := hbadsub hcon
      have h2 : j₁ ∈ F := Finset.mem_of_mem_erase h1
      dsimp only [G] at h1
      exact Finset.notMem_erase j₁ F h1
    have hbadcard : (bad.card : ℝ) ≤ 2 * Real.pi * η * (L : ℝ) :=
      bad_card_bound (L := L) hLpos hcop xx η hηpos hj₁mem hminν hbad_sub hj₁bad
    have hbadcard2 : (bad.card : ℝ) ≤ (L : ℝ) - 1 := by
      have h1 : bad.card ≤ G.card := Finset.card_le_card hbadsub
      have h2 : G.card ≤ L - 1 := by
        have h4 : G.card ≤ F.card := Finset.card_le_card hGF
        have h5 : F.card = L - 1 := by
          dsimp only [F]; rw [Finset.card_erase_of_mem hj₀mem, Nat.card_Icc]; omega
        omega
      have h3 : (bad.card : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by
        have : bad.card ≤ L - 1 := by omega
        exact_mod_cast this
      rw [Nat.cast_sub (by omega : 1 ≤ L)] at h3
      push_cast at h3
      linarith
    have harith := final_arith (L := L) hL2 hηpos hηL hβ1 hβ2 (by positivity) hbadcard hbadcard2
    by_cases hj₁eq : j₁ = j₀
    · -- ## Case A: the rational minimiser is the irrational one
      have hG_eq_F : G = F := by
        show ((Finset.Icc 1 L).erase j₀).erase j₁ = (Finset.Icc 1 L).erase j₀
        rw [hj₁eq]
        exact Finset.erase_eq_of_notMem (Finset.notMem_erase j₀ (Finset.Icc 1 L))
      have hFmem : ∀ j ∈ F, j ∈ Finset.Icc 1 L ∧ j ≠ j₁ := by
        intro j hj
        have hj' : j ∈ (Finset.Icc 1 L).erase j₀ := by simpa only [F] using hj
        refine ⟨Finset.mem_of_mem_erase hj', ?_⟩
        intro hcon
        exact Finset.ne_of_mem_erase hj' (hcon.trans hj₁eq)
      have hReq : R = ∑ j ∈ F, Real.log (2 * Bb j) := by
        show ∑ j ∈ (Finset.Icc 1 L).erase j₁, Real.log (2 * Bb j)
            = ∑ j ∈ (Finset.Icc 1 L).erase j₀, Real.log (2 * Bb j)
        rw [hj₁eq]
      have hTA : T = comp + R := by
        have h1 : comp = (∑ j ∈ F, Real.log (S (ph j))) - ∑ j ∈ F, Real.log (Bb j) := by
          rw [show comp = ∑ j ∈ F, (Real.log (S (ph j)) - Real.log (Bb j)) by
            show ((∑ j ∈ G, (Real.log (S (ph j)) - Real.log (Bb j)))
              = ∑ j ∈ F, (Real.log (S (ph j)) - Real.log (Bb j)))
            rw [hG_eq_F]]
          simp only [Finset.sum_sub_distrib]
        have h2 : ∑ j ∈ F, Real.log (2 * Bb j)
            = (F.card : ℝ) * Real.log 2 + ∑ j ∈ F, Real.log (Bb j) := by
          have h3 : ∀ j ∈ F, Real.log (2 * Bb j) = Real.log 2 + Real.log (Bb j) := by
            intro j hj
            obtain ⟨hjI, hjn1⟩ := hFmem j hj
            exact Real.log_mul (by norm_num) (ne_of_gt (hBbpos j hjI hjn1))
          rw [Finset.sum_congr rfl h3, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        have h4 : (F.card : ℝ) = (L : ℝ) - 1 := by
          have h5 : F.card = L - 1 := by
            show ((Finset.Icc 1 L).erase j₀).card = L - 1
            rw [Finset.card_erase_of_mem hj₀mem, Nat.card_Icc]; omega
          rw [h5, Nat.cast_sub (by omega : 1 ≤ L)]
          push_cast; ring
        show ((∑ j ∈ F, Real.log (S (ph j))) + ((L : ℝ) - 1) * Real.log 2 = comp + R)
        rw [h1, hReq, h2, h4]
        ring
      have hUpper : T ≤ Real.log (L : ℝ) + 32 * ((η * (L : ℝ)) * Real.log (L : ℝ)) := by
        have h1 : comp ≤ 2 * Real.pi * η * β
            + Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3) * (bad.card : ℝ) :=
          le_trans (le_abs_self comp) hcomp_abs
        have h2 : T ≤ 2 * Real.pi * η * β
            + Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3) * (bad.card : ℝ)
            + Real.log (L : ℝ) := by
          rw [hTA]; linarith
        linarith [h2, harith.1]
      have hLower : -(Real.log (L : ℝ) + 32 * ((η * (L : ℝ)) * Real.log (L : ℝ))) ≤ T := by
        have h1 : T ≥ -(2 * Real.pi * η * β
            + Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3) * (bad.card : ℝ))
            + Real.log (2 * (L : ℝ) / Real.pi) := by
          have ha : comp ≥ -(2 * Real.pi * η * β
              + Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3) * (bad.card : ℝ)) := by
            have := neg_abs_le comp
            linarith [hcomp_abs]
          rw [hTA]; linarith [hRge]
        have h3 : (0 : ℝ) ≤ Real.log (1 + 10 * Real.pi * η * (L : ℝ) / 3) := by
          apply Real.log_nonneg
          have h4 : (0 : ℝ) ≤ 10 * Real.pi * η * (L : ℝ) := by positivity
          linarith
        linarith [h1, harith.2, h3]
      rw [abs_le]
      exact ⟨hLower, hUpper⟩
    · -- ## Case B: the two minimisers differ
      have hQ1 : Real.log (S (ph j₁)) - Real.log (Bb j₀) ≤ Real.pi * η * (L : ℝ) := by
        have hj₀ne : j₀ ≠ j₁ := fun h => hj₁eq h.symm
        have hBb0 : 0 < Bb j₀ := hBbpos j₀ hj₀mem hj₀ne
        have hS1 : S (ph j₁) ≤ Bb j₀ + Real.pi * η := by
          have h3 : nn (ph j₁ - νa j₁) ≤ η := hphdiff j₁ hj₁mem
          have h4 : |S (ph j₁) - Bb j₁| ≤ Real.pi * η := by
            have h5 : |S (ph j₁) - S (νa j₁)| ≤ Real.pi * nn (ph j₁ - νa j₁) :=
              abs_S_sub_S_le_nn _ _
            have h6 : Real.pi * nn (ph j₁ - νa j₁) ≤ Real.pi * η :=
              mul_le_mul_of_nonneg_left h3 Real.pi_pos.le
            linarith
          have h5 : Bb j₁ ≤ Bb j₀ := hj₁min j₀ hj₀mem
          linarith [(abs_le.mp h4).2]
        have h5 : Real.log (S (ph j₁)) ≤ Real.log (Bb j₀ + Real.pi * η) :=
          Real.log_le_log (hSpos j₁ hj₁mem (fun h => hj₀ne h.symm)) hS1
        have h6 : Real.log (Bb j₀ + Real.pi * η) - Real.log (Bb j₀) ≤ Real.pi * η * (L : ℝ) := by
          have h7 : (Bb j₀ + Real.pi * η) / Bb j₀ = 1 + Real.pi * η / Bb j₀ := by
            field_simp
          have h8 : Real.log (Bb j₀ + Real.pi * η) - Real.log (Bb j₀)
              = Real.log (1 + Real.pi * η / Bb j₀) := by
            have hπη : 0 < Real.pi * η := mul_pos Real.pi_pos hηpos
            have hBb2 : 0 < Bb j₀ + Real.pi * η := by linarith
            calc Real.log (Bb j₀ + Real.pi * η) - Real.log (Bb j₀)
                = Real.log ((Bb j₀ + Real.pi * η) / Bb j₀) :=
                  (Real.log_div (ne_of_gt hBb2) (ne_of_gt hBb0)).symm
              _ = Real.log (1 + Real.pi * η / Bb j₀) := by rw [h7]
          rw [h8]
          have h9 : Real.log (1 + Real.pi * η / Bb j₀) ≤ Real.pi * η / Bb j₀ := by
            have h10 := Real.log_le_sub_one_of_pos
              (by positivity : (0 : ℝ) < 1 + Real.pi * η / Bb j₀)
            linarith
          have h10 : (1 : ℝ) / (L : ℝ) ≤ Bb j₀ := by
            have h11 : 2 * ν j₀ ≤ Bb j₀ := two_mul_nn_le_S' (νa j₀)
            have h12 : (1 : ℝ) / (2 * (L : ℝ)) ≤ ν j₀ := hgrid1 j₀ hj₀mem hj₀ne
            have h13 : (2 : ℝ) * (1 / (2 * (L : ℝ))) = 1 / (L : ℝ) := by field_simp
            linarith
          have hπη : 0 < Real.pi * η := mul_pos Real.pi_pos hηpos
          have h11 : Real.pi * η / Bb j₀ ≤ Real.pi * η * (L : ℝ) := by
            rw [div_le_iff₀ hBb0]
            have h10' : (1 : ℝ) ≤ Bb j₀ * (L : ℝ) := (div_le_iff₀ hLR).mp h10
            nlinarith [hπη.le, h10', hBb0.le, hLR.le]
          linarith
        linarith
      have hQ2 : Real.log (S (ph j₁)) - Real.log (Bb j₀)
          ≥ -Real.log (1 + 10 * Real.pi * η * (L : ℝ) / 3) := by
        have hj₀ne : j₀ ≠ j₁ := fun h => hj₁eq h.symm
        have hS1pos : 0 < S (ph j₁) := hSpos j₁ hj₁mem (fun h => hj₀ne h.symm)
        have hS1 : (3 : ℝ) / (10 * (L : ℝ)) ≤ S (ph j₁) := by
          have h1 := hnnφ j₁ hj₁mem (fun h => hj₀ne h.symm)
          have h2 := two_mul_nn_le_S' (ph j₁)
          have h3 : (3 : ℝ) / (10 * (L : ℝ)) = 2 * (3 / (20 * (L : ℝ))) := by
            field_simp
            ring
          linarith
        have hBb0le : Bb j₀ ≤ S (ph j₁) + Real.pi * η := by
          have h3 : nn (ph j₀ - νa j₀) ≤ η := hphdiff j₀ hj₀mem
          have h4 : |S (ph j₀) - Bb j₀| ≤ Real.pi * η := by
            have h5 : |S (ph j₀) - S (νa j₀)| ≤ Real.pi * nn (ph j₀ - νa j₀) :=
              abs_S_sub_S_le_nn _ _
            have h6 : Real.pi * nn (ph j₀ - νa j₀) ≤ Real.pi * η :=
              mul_le_mul_of_nonneg_left h3 Real.pi_pos.le
            linarith
          have h5 : S (ph j₀) ≤ S (ph j₁) := hminS j₁ hj₁mem
          linarith [(abs_le.mp h4).1]
        have h6 : Real.log (S (ph j₁)) - Real.log (Bb j₀)
            ≥ Real.log (S (ph j₁)) - Real.log (S (ph j₁) + Real.pi * η) := by
          have h7 : Real.log (Bb j₀) ≤ Real.log (S (ph j₁) + Real.pi * η) :=
            Real.log_le_log (hBbpos j₀ hj₀mem hj₀ne) hBb0le
          linarith
        refine le_trans ?_ h6
        have h8 : Real.log (S (ph j₁)) - Real.log (S (ph j₁) + Real.pi * η)
            = -Real.log (1 + Real.pi * η / S (ph j₁)) := by
          have hS2 : 0 < S (ph j₁) + Real.pi * η := by
            have hπη : 0 < Real.pi * η := mul_pos Real.pi_pos hηpos
            linarith
          have h9 : (S (ph j₁) + Real.pi * η) / S (ph j₁) = 1 + Real.pi * η / S (ph j₁) := by
            field_simp
          have h9b : Real.log (S (ph j₁)) - Real.log (S (ph j₁) + Real.pi * η)
              = Real.log (S (ph j₁) / (S (ph j₁) + Real.pi * η)) :=
            (Real.log_div (ne_of_gt hS1pos) (ne_of_gt hS2)).symm
          have h9c : S (ph j₁) / (S (ph j₁) + Real.pi * η) = (1 + Real.pi * η / S (ph j₁))⁻¹ := by
            field_simp
          rw [h9b, h9c, Real.log_inv]
        rw [h8]
        have h10 : Real.log (1 + Real.pi * η / S (ph j₁))
            ≤ Real.log (1 + 10 * Real.pi * η * (L : ℝ) / 3) := by
          apply Real.log_le_log (by
            have h13 : (0 : ℝ) ≤ Real.pi * η / S (ph j₁) :=
              div_nonneg (mul_nonneg Real.pi_pos.le hηpos.le) hS1pos.le
            linarith)
          have h11 : Real.pi * η / S (ph j₁) ≤ Real.pi * η / (3 / (10 * (L : ℝ))) :=
            div_le_div_of_nonneg_left (mul_nonneg Real.pi_pos.le hηpos.le)
              (by apply div_pos (by norm_num); linarith) hS1
          have h12 : Real.pi * η / (3 / (10 * (L : ℝ))) = 10 * Real.pi * η * (L : ℝ) / 3 := by
            have h14 : (3 / (10 * (L : ℝ))) ≠ 0 := by
              apply div_ne_zero (by norm_num) (by linarith)
            field_simp
          linarith
        linarith
      have hj₁F : j₁ ∈ F := by
        show j₁ ∈ (Finset.Icc 1 L).erase j₀
        rw [Finset.mem_erase]
        exact ⟨hj₁eq, hj₁mem⟩
      have hG_eq : G = ((Finset.Icc 1 L).erase j₁).erase j₀ := by
        show ((Finset.Icc 1 L).erase j₀).erase j₁ = ((Finset.Icc 1 L).erase j₁).erase j₀
        rw [Finset.erase_right_comm]
      have hH : (Finset.Icc 1 L).erase j₁ = insert j₀ G := by
        have hj₀mem' : j₀ ∈ (Finset.Icc 1 L).erase j₁ := by
          rw [Finset.mem_erase]
          exact ⟨Ne.symm hj₁eq, hj₀mem⟩
        rw [hG_eq]
        exact (Finset.insert_erase hj₀mem').symm
      have hRsplit : R = Real.log (2 * Bb j₀) + ∑ j ∈ G, Real.log (2 * Bb j) := by
        show (∑ j ∈ (Finset.Icc 1 L).erase j₁, Real.log (2 * Bb j))
            = Real.log (2 * Bb j₀) + ∑ j ∈ G, Real.log (2 * Bb j)
        rw [hH, Finset.sum_insert (by rw [hG_eq]; exact Finset.notMem_erase j₀ _)]
      have hF_insert : F = insert j₁ G := (Finset.insert_erase hj₁F).symm
      have hsum2G : ∑ j ∈ G, Real.log (2 * Bb j)
          = (G.card : ℝ) * Real.log 2 + ∑ j ∈ G, Real.log (Bb j) := by
        have h3 : ∀ j ∈ G, Real.log (2 * Bb j) = Real.log 2 + Real.log (Bb j) := by
          intro j hj
          obtain ⟨hjI, _, hjn1⟩ := hGmem j hj
          exact Real.log_mul (by norm_num) (ne_of_gt (hBbpos j hjI hjn1))
        rw [Finset.sum_congr rfl h3, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      have hcardG : (G.card : ℝ) = (L : ℝ) - 2 := by
        have h5 : G.card = L - 2 := by
          show (((Finset.Icc 1 L).erase j₀).erase j₁).card = L - 2
          rw [Finset.card_erase_of_mem hj₁F, Finset.card_erase_of_mem hj₀mem, Nat.card_Icc]
          omega
        rw [h5, Nat.cast_sub (by omega : 2 ≤ L)]
        push_cast; ring
      have hTB : T = comp + R + (Real.log (S (ph j₁)) - Real.log (Bb j₀)) := by
        have h1 : comp = (∑ j ∈ G, Real.log (S (ph j))) - ∑ j ∈ G, Real.log (Bb j) := by
          rw [show comp = ∑ j ∈ G, (Real.log (S (ph j)) - Real.log (Bb j)) by
            show ((∑ j ∈ G, (Real.log (S (ph j)) - Real.log (Bb j)))
              = ∑ j ∈ G, (Real.log (S (ph j)) - Real.log (Bb j)))
            rfl]
          simp only [Finset.sum_sub_distrib]
        have h2 : Real.log (2 * Bb j₀) = Real.log 2 + Real.log (Bb j₀) :=
          Real.log_mul (by norm_num) (ne_of_gt (hBbpos j₀ hj₀mem (fun h => hj₁eq h.symm)))
        have h3 : ∑ j ∈ F, Real.log (S (ph j))
            = Real.log (S (ph j₁)) + ∑ j ∈ G, Real.log (S (ph j)) := by
          rw [hF_insert, Finset.sum_insert (Finset.notMem_erase j₁ F)]
        show ((∑ j ∈ F, Real.log (S (ph j))) + ((L : ℝ) - 1) * Real.log 2
            = comp + R + (Real.log (S (ph j₁)) - Real.log (Bb j₀)))
        rw [h3, h1, hRsplit, hsum2G, h2, hcardG]
        ring
      have hUpper : T ≤ Real.log (L : ℝ) + 32 * ((η * (L : ℝ)) * Real.log (L : ℝ)) := by
        have h1 : comp ≤ 2 * Real.pi * η * β
            + Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3) * (bad.card : ℝ) :=
          le_trans (le_abs_self comp) hcomp_abs
        have h2 : T ≤ 2 * Real.pi * η * β
            + Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3) * (bad.card : ℝ)
            + Real.log (L : ℝ) + Real.pi * η * (L : ℝ) := by
          rw [hTB]; linarith
        linarith [h2, harith.1]
      have hLower : -(Real.log (L : ℝ) + 32 * ((η * (L : ℝ)) * Real.log (L : ℝ))) ≤ T := by
        have h1 : T ≥ -(2 * Real.pi * η * β
            + Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3) * (bad.card : ℝ))
            - Real.log (1 + 10 * Real.pi * η * (L : ℝ) / 3)
            + Real.log (2 * (L : ℝ) / Real.pi) := by
          have ha : comp ≥ -(2 * Real.pi * η * β
              + Real.log (1 + 20 * Real.pi * η * (L : ℝ) / 3) * (bad.card : ℝ)) := by
            have := neg_abs_le comp
            linarith [hcomp_abs]
          rw [hTB]; linarith [hRge, hQ2]
        linarith [h1, harith.2]
      rw [abs_le]
      exact ⟨hLower, hUpper⟩


theorem irrat_blk_shift {α : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hqpos : ∀ m, 0 < q m) (hmono : StrictMono q)
    (hΔpos : ∀ m, 0 < Δ m)
    (hΔeq : ∀ m, Δ m = Work.TMC16Core.fracDist ((q m : ℝ) * α))
    (hΔup : ∀ m, Δ m < 1 / ((q (m + 1) : ℝ)))
    (hΔlo : ∀ m, 1 / (((q (m + 1) : ℝ)) + (q m : ℝ)) < Δ m)
    (hbest : ∀ m k : ℕ, q m ≤ k → k < q (m + 1) →
      Δ m ≤ Work.TMC16Core.fracDist ((k : ℝ) * α))
    {n r : ℕ} (hnr : n ≤ r) {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hℓb : 10 * (ℓ : ℝ) * (q r : ℝ) < (q (r + 1) : ℝ))
    {p : ℤ} {ξ : ℝ} {k₀ : ℤ} {Lsh : ℤ → ℤ}
    (hLsh : ∀ k : ℤ, |Lsh k| ≤ (ℓ : ℤ) - 1)
    (hk₀ : k₀ ∈ Finset.Icc p (p + (q n : ℤ) - 1))
    (hmin : ∀ k ∈ Finset.Icc p (p + (q n : ℤ) - 1),
      |Real.sin (Real.pi * (ξ + ((k + Lsh k * (q r : ℤ) : ℤ) : ℝ) * α))| ≥
        |Real.sin (Real.pi * (ξ + ((k₀ + Lsh k₀ * (q r : ℤ) : ℤ) : ℝ) * α))|) :
    |∑ k ∈ (Finset.Icc p (p + (q n : ℤ) - 1)).erase k₀,
        Real.log |Real.sin (Real.pi * (ξ + ((k + Lsh k * (q r : ℤ) : ℤ) : ℝ) * α))|
      + ((q n : ℝ) - 1) * Real.log 2|
      ≤ Real.log (q n : ℝ)
        + 32 * ((Δ n + (ℓ : ℝ) * Δ r) * (q n : ℝ) * Real.log (q n : ℝ)) := by
  exact irrat_blk_shift_master hqpos hmono hΔpos hΔeq hΔup hΔlo hbest
    (blk_sep_base hqpos hmono hΔpos hΔeq hΔup hΔlo hbest)
    hnr hℓ hℓb hLsh hk₀ hmin

end Work.TMC16Core.Core

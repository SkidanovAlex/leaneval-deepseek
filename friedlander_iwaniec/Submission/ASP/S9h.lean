/-
  Companion paper, §9: the modified density `g̃` of (9.5),

      `g̃(p) = (g(p) − g(p²))/(1 − g(p²))`,

  satisfies the hypotheses (1.8) and (1.9) *by (9.1)* (`0 ≤ g(p²) ≤ g(p)`, `g(p²) ≪ p^{−2}`).

  Contents:
  * `gtilVal_nonneg`, `gtilVal_lt_one`, `gtilVal_le` — the hypothesis (1.8) for `g̃`
    (`0 ≤ g̃(p) < 1`, `g̃(p) ≪ p^{−1}`);
  * `sub_gtilVal_eq` — the exact difference `g − g̃ = g(p²)(1 − g(p))/(1 − g(p²)) ≥ 0`;
  * `sum_gtilVal_eq` — `∑_{p ≤ y} g̃(p) = ∑_{p ≤ y} g(p) − ∑_{p ≤ y}(g(p) − g̃(p))`;
  * `tsum_sub_partial_le` — the correction sum converges with rate `1/y`
    (the precise form of `∑_{ν > y} g(ν²) = O(1/y)` coming from (9.1));
  * `sum_gtilVal_19` — the transfer of (1.9) from `g` to `g̃`.
-/
import Mathlib
import Submission.Commons.Analysis.Hilbert.discrete_hilbert_transform_maximal_weak_type_one_hilbert

namespace Submission.ASP

open Finset

noncomputable section

/-- `g̃(p) = (g(p) − g(p²))/(1 − g(p²))` — the companion's modified density (9.5) at primes. -/
def gtilVal (g : ℕ → ℝ) (p : ℕ) : ℝ := (g p - g (p ^ 2)) / (1 - g (p ^ 2))

/-- (1.8) for `g̃`: nonnegativity, from `0 ≤ g(p²) ≤ g(p) < 1`. -/
lemma gtilVal_nonneg {g : ℕ → ℝ} {p : ℕ} (h0 : 0 ≤ g (p ^ 2)) (hle : g (p ^ 2) ≤ g p)
    (h1 : g p < 1) : 0 ≤ gtilVal g p := by
  rw [gtilVal]
  exact div_nonneg (by linarith) (by linarith)

/-- (1.8) for `g̃`: `g̃(p) < 1`. -/
lemma gtilVal_lt_one {g : ℕ → ℝ} {p : ℕ} (h1 : g p < 1) (h2 : g (p ^ 2) < 1) :
    gtilVal g p < 1 := by
  rw [gtilVal, div_lt_one (by linarith)]
  linarith

/-- (1.8) for `g̃`: `g̃(p) ≤ 2C₀/p` whenever `g(p) ≤ C₀/p` and `g(p²) ≤ 1/2`. -/
lemma gtilVal_le {g : ℕ → ℝ} {p : ℕ} {C0 : ℝ} (hC0 : 0 ≤ C0)
    (hg : g p ≤ C0 / p) (h0 : 0 ≤ g (p ^ 2)) (hden : g (p ^ 2) ≤ 1 / 2) :
    gtilVal g p ≤ 2 * C0 / p := by
  have hnum : g p - g (p ^ 2) ≤ C0 / p := by linarith
  have hden' : 1 / 2 ≤ 1 - g (p ^ 2) := by linarith
  rw [gtilVal, div_le_iff₀ (by linarith)]
  have hstep : g p - g (p ^ 2) ≤ (2 * C0 / p) * (1 / 2) := by
    have : (2 * C0 / p) * (1 / 2) = C0 / p := by ring
    rw [this]; exact hnum
  have h2p : 0 ≤ 2 * C0 / p := div_nonneg (by linarith) (Nat.cast_nonneg p)
  calc g p - g (p ^ 2) ≤ (2 * C0 / p) * (1 / 2) := hstep
    _ ≤ (2 * C0 / p) * (1 - g (p ^ 2)) := mul_le_mul_of_nonneg_left hden' h2p

/-- The exact difference `g(p) − g̃(p)`. -/
lemma sub_gtilVal_eq (g : ℕ → ℝ) {p : ℕ} (h2 : g (p ^ 2) ≠ 1) :
    g p - gtilVal g p = g (p ^ 2) * (1 - g p) / (1 - g (p ^ 2)) := by
  rw [gtilVal]
  field_simp
  ring

/-- `∑_{p ≤ y} g̃(p) = ∑_{p ≤ y} g(p) − ∑_{p ≤ y}(g(p) − g̃(p))`. -/
lemma sum_gtilVal_eq (g : ℕ → ℝ) (y : ℕ) :
    (∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, gtilVal g p)
      = (∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, g p)
        - ∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, (g p - gtilVal g p) := by
  rw [Finset.sum_sub_distrib]
  ring

/-- **The correction sum converges with rate `1/y`**: if `h ≥ 0`, `h = 0` off the primes and
`h(p) ≤ C/p²` on the primes, then `∑' h − ∑_{n ≤ y} h(n) ≤ 2C/y`.  This is the quantitative
form of `∑_{p > y} g(p²) ≪ 1/y` used to transfer (1.9) to `g̃`. -/
theorem tsum_sub_partial_le {h : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C) (h0 : ∀ n, 0 ≤ h n)
    (hz : ∀ n, ¬ n.Prime → h n = 0) (hbd : ∀ n, n.Prime → h n ≤ C / (n : ℝ) ^ 2)
    (y : ℕ) (hy : 1 ≤ y) :
    (∑' n : ℕ, h n) - ∑ n ∈ Finset.range (y + 1), h n ≤ 2 * C / (y : ℝ) := by
  classical
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
  -- summability of `h` by comparison with `C/n²`
  have hsum1 : Summable (fun n : ℕ => C * (1 / (n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num : (1 : ℕ) < 2)).mul_left C
  have hle : ∀ n, h n ≤ C * (1 / (n : ℝ) ^ 2) := by
    intro n
    by_cases hn : n.Prime
    · refine le_trans (hbd n hn) (le_of_eq ?_)
      rw [mul_one_div]
    · rw [hz n hn]
      positivity
  have hsum : Summable h := Summable.of_nonneg_of_le h0 hle hsum1
  have htend := hsum.hasSum.tendsto_sum_nat
  have htend' : Filter.Tendsto
      (fun N : ℕ => (∑ n ∈ Finset.range N, h n) - ∑ n ∈ Finset.range (y + 1), h n)
      Filter.atTop (nhds ((∑' n : ℕ, h n) - ∑ n ∈ Finset.range (y + 1), h n)) :=
    htend.sub tendsto_const_nhds
  have htarget : (0 : ℝ) ≤ 2 * C / (y : ℝ) :=
    div_nonneg (by linarith) (le_of_lt hy0)
  refine le_of_tendsto' htend' (fun N => ?_)
  rcases Nat.lt_or_ge (y + 1) N with hN | hN
  · have hgeo : (∑ n ∈ Finset.Ico (y + 1) N, (1 / (n : ℝ) ^ 2))
        ≤ 2 / ((y + 1 : ℕ) : ℝ) := by
      refine Commons.Analysis.Hilbert.sum_inv_sq_le_of_ge (R := y + 1) (by omega)
        (fun d hd => (Finset.mem_Ico.mp hd).1)
    have hstep : (∑ n ∈ Finset.Ico (y + 1) N, C * (1 / (n : ℝ) ^ 2))
        ≤ C * (2 / ((y + 1 : ℕ) : ℝ)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hgeo hC
    have hcast : ((y + 1 : ℕ) : ℝ) = (y : ℝ) + 1 := by push_cast; ring
    have hquot : C * (2 / ((y : ℝ) + 1)) ≤ 2 * C / (y : ℝ) := by
      rw [← mul_div_assoc, div_le_div_iff₀ (by linarith) hy0]
      nlinarith
    calc (∑ n ∈ Finset.range N, h n) - ∑ n ∈ Finset.range (y + 1), h n
        = ∑ n ∈ Finset.Ico (y + 1) N, h n := (Finset.sum_Ico_eq_sub h (le_of_lt hN)).symm
      _ ≤ ∑ n ∈ Finset.Ico (y + 1) N, C * (1 / (n : ℝ) ^ 2) :=
          Finset.sum_le_sum (fun n _ => hle n)
      _ ≤ C * (2 / ((y + 1 : ℕ) : ℝ)) := hstep
      _ = C * (2 / ((y : ℝ) + 1)) := by rw [hcast]
      _ ≤ 2 * C / (y : ℝ) := hquot
  · have hmono : (∑ n ∈ Finset.range N, h n) ≤ ∑ n ∈ Finset.range (y + 1), h n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hN)
        (fun i _ _ => h0 i)
    linarith

/-- **Companion §9, (1.9) for `g̃`**: if `g` satisfies (1.9) with error `err` and the correction
`g − g̃` also converges with error `err`, then `g̃` satisfies (1.9) with the same error and the
constant `c − Hc`. -/
theorem sum_gtilVal_19 (g : ℕ → ℝ) {c Hc K Kc : ℝ} {err : ℕ → ℝ}
    (h19 : ∀ y : ℕ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, g p) - Real.log (Real.log y) - c|
        ≤ K * err y)
    (hcorr : ∀ y : ℕ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, (g p - gtilVal g p)) - Hc|
        ≤ Kc * err y) :
    ∀ y : ℕ, 2 ≤ y →
      |(∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, gtilVal g p)
          - Real.log (Real.log y) - (c - Hc)| ≤ (K + Kc) * err y := by
  intro y hy
  have h := sum_gtilVal_eq g y
  have h1 := h19 y hy
  have h2 := hcorr y hy
  rw [h]
  have heq : ((∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, g p)
        - (∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, (g p - gtilVal g p))
        - Real.log (Real.log y) - (c - Hc))
      = ((∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, g p) - Real.log (Real.log y) - c)
        - ((∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, (g p - gtilVal g p)) - Hc) := by ring
  rw [heq]
  calc |((∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, g p) - Real.log (Real.log y) - c)
        - ((∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, (g p - gtilVal g p)) - Hc)|
      ≤ |(∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, g p) - Real.log (Real.log y) - c|
        + |(∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, (g p - gtilVal g p)) - Hc| := abs_sub _ _
    _ ≤ K * err y + Kc * err y := add_le_add h1 h2
    _ = (K + Kc) * err y := by ring


/-- The correction `g − g̃`, viewed as a function on `ℕ` (supported on the primes). -/
def gcorrect (g : ℕ → ℝ) (n : ℕ) : ℝ := if n.Prime then g n - gtilVal g n else 0

/-- The partial sums of `gcorrect` up to `y` are the prime sums of `g − g̃`. -/
lemma sum_gcorrect_range_eq (g : ℕ → ℝ) (y : ℕ) :
    (∑ n ∈ Finset.range (y + 1), gcorrect g n)
      = ∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, (g p - gtilVal g p) := by
  simp only [gcorrect]
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨hlt, hp⟩
    exact ⟨⟨hp.one_le, by omega⟩, hp⟩
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨by omega, hp⟩

/-- The prime correction sum has a convergent tail of size at most `2C/y`. -/
theorem abs_gcorrect_sub_le (g : ℕ → ℝ) {C2 : ℝ} (hC2 : 0 ≤ C2)
    (hnn : ∀ p, p.Prime → 0 ≤ g p - gtilVal g p)
    (hbd : ∀ p, p.Prime → g p - gtilVal g p ≤ C2 / (p : ℝ) ^ 2)
    (y : ℕ) (hy : 1 ≤ y) :
    |(∑' n : ℕ, gcorrect g n)
        - ∑ p ∈ (Finset.Icc 1 y).filter Nat.Prime, (g p - gtilVal g p)|
      ≤ 2 * C2 / (y : ℝ) := by
  have h0 : ∀ n, 0 ≤ gcorrect g n := by
    intro n
    rw [gcorrect]
    by_cases hn : n.Prime
    · rw [if_pos hn]; exact hnn n hn
    · rw [if_neg hn]
  have hz : ∀ n, ¬ n.Prime → gcorrect g n = 0 := by
    intro n hn; rw [gcorrect, if_neg hn]
  have hb : ∀ n, n.Prime → gcorrect g n ≤ C2 / (n : ℝ) ^ 2 := by
    intro n hn; rw [gcorrect, if_pos hn]; exact hbd n hn
  have hle := tsum_sub_partial_le hC2 h0 hz hb y hy
  rw [sum_gcorrect_range_eq] at hle
  rw [abs_of_nonneg]
  · exact hle
  · have hsum : Summable (gcorrect g) := by
      refine Summable.of_nonneg_of_le h0 (fun n => ?_)
        ((Real.summable_one_div_nat_pow.mpr (by norm_num : (1:ℕ) < 2)).mul_left C2)
      by_cases hn : n.Prime
      · rw [gcorrect, if_pos hn]
        refine le_trans (hbd n hn) (le_of_eq ?_)
        rw [mul_one_div]
      · rw [gcorrect, if_neg hn]; positivity
    have hthis := hsum.sum_le_tsum (Finset.range (y + 1)) (fun i _ => h0 i)
    rw [← sum_gcorrect_range_eq g y]
    exact sub_nonneg.mpr hthis

end

end Submission.ASP

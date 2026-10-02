import Mathlib
import Submission.Commons.NumberTheory.Linnik.tentWeight_spec
import Submission.Commons.NumberTheory.Linnik.tentWeight_bounds
import Submission.Commons.NumberTheory.ArithmeticFunction.sum_vonMangoldt_div_sub_log_bounded
import Submission.Commons.Analysis.Integral.finset_layerCake

namespace Commons.NumberTheory.Linnik

open Finset MeasureTheory
open scoped BigOperators Interval

noncomputable section

/-! ## The principal-character ("Mellin transform") estimate for the tent weight

Heath-Brown (1992), §13, principal-character case of Lemma 13.1: for `L ≥ 2K+2`,
`N ≥ q^L`, the tent-weighted von Mangoldt sum satisfies

`(log q)⁻¹ ∑_{n ≤ N} Λ(n)/n · f(log n / log q) = F(0) + O((log q)⁻¹)`

where `f = tentWeight L K` and `F(0) = ∫₀^∞ f = K²` is the area under the tent.

The proof is elementary.  By the layer-cake identity
(`Commons.Analysis.Integral.finset_layerCake`) the weighted sum equals
`∫₀^K 𝒜(s) ds` where `𝒜(s) = ∑_{n : f(log n/log q) ≥ s} Λ(n)/n`.  For
`0 < s ≤ K` the superlevel set is the interval `[q^{L-2K+s}, q^{L-s}]`, so by
Mertens' first theorem `𝒜(s) = (2K-2s) log q + O(1)` uniformly in `s`; integrating
against `s ∈ (0,K]` gives `K² log q + O(1)`. -/

/-- Mertens' first theorem constant in the form used below. -/
def principalC : ℝ := Real.log 4 + 4 + Real.log 2

lemma principalC_pos : 0 < principalC := by
  unfold principalC
  have h1 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- Mertens' first theorem at integer arguments, with a fixed constant. -/
lemma mertens_int (m : ℕ) (hm : 1 ≤ m) :
    |∑ n ∈ Finset.Icc 1 m, ArithmeticFunction.vonMangoldt n / (n : ℝ) - Real.log (m : ℝ)|
      ≤ principalC := by
  rcases eq_or_lt_of_le hm with h | h
  · subst h
    rw [principalC, Finset.Icc_self, Finset.sum_singleton]
    simp
    have h1 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  · have hb := ArithmeticFunction.sum_vonMangoldt_div_sub_log_nat_bound m h
    have h4 : Real.log 4 + 4 ≤ principalC := by
      unfold principalC
      have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    linarith [hb, h4]

/-! ### Elementary floor/ceiling logarithm bounds -/

lemma log_floor_sub_le {x : ℝ} (hx : 2 ≤ x) :
    |Real.log (⌊x⌋₊ : ℝ) - Real.log x| ≤ Real.log 2 := by
  have hx0 : 0 < x := by linarith
  have h1 : 1 ≤ ⌊x⌋₊ := by
    have h := Nat.floor_mono hx
    have h2 : ⌊(2 : ℝ)⌋₊ = 2 := by norm_num
    rw [h2] at h
    omega
  have hfx : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
  have hle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hge : x - 1 < (⌊x⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one x
    linarith
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hfx hle))]
  rw [← Real.log_div hx0.ne' hfx.ne']
  apply Real.log_le_log (div_pos hx0 hfx)
  rw [div_le_iff₀ hfx]
  nlinarith

lemma log_ceil_sub_one_sub_le {x : ℝ} (hx : 2 ≤ x) :
    |Real.log ((⌈x⌉₊ : ℝ) - 1) - Real.log x| ≤ Real.log 2 := by
  have hx0 : 0 < x := by linarith
  have hcx : (⌈x⌉₊ : ℝ) - 1 < x := by
    have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ x by linarith)
    linarith
  have hcl : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hc0 : (0 : ℝ) < (⌈x⌉₊ : ℝ) - 1 := by linarith
  have hcle : (⌈x⌉₊ : ℝ) - 1 ≤ x := le_of_lt hcx
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hc0 hcle))]
  rw [← Real.log_div hx0.ne' hc0.ne']
  apply Real.log_le_log (div_pos hx0 hc0)
  rw [div_le_iff₀ hc0]
  nlinarith [hcl, hx]

/-! ### Two elementary identities for sums over integer intervals -/

lemma sum_Icc_eq_Icc_sub {f : ℕ → ℝ} {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b + 1) :
    ∑ n ∈ Finset.Icc a b, f n
      = ∑ n ∈ Finset.Icc 1 b, f n - ∑ n ∈ Finset.Icc 1 (a - 1), f n := by
  have hunion : Finset.Icc 1 b = Finset.Icc 1 (a - 1) ∪ Finset.Icc a b := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 1 (a - 1)) (Finset.Icc a b) := by
    rw [Finset.disjoint_left]
    intro n hn1 hn2
    simp only [Finset.mem_Icc] at hn1 hn2
    omega
  rw [hunion, Finset.sum_union hdisj]
  ring

lemma sum_Icc_filter_interval {f : ℕ → ℝ} {N : ℕ} {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ (N : ℝ)) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ => a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b), f n
      = ∑ n ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊, f n := by
  have hset : (Finset.Icc 1 N).filter (fun n : ℕ => a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b)
      = Finset.Icc ⌈a⌉₊ ⌊b⌋₊ := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hn1, hnN⟩, hna, hnb⟩
      exact ⟨Nat.ceil_le.mpr hna, Nat.le_floor hnb⟩
    · rintro ⟨hna, hnb⟩
      have hb0 : 0 ≤ b := by linarith
      have h2 : (n : ℝ) ≤ b := le_trans (by exact_mod_cast hnb) (Nat.floor_le hb0)
      have h1 : 1 ≤ n := by
        have : 1 ≤ ⌈a⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
        omega
      exact ⟨⟨h1, by exact_mod_cast le_trans h2 hb⟩, Nat.ceil_le.mp hna, h2⟩
  rw [hset]

/-! ### A partial-sum notation for `∑_{n ≤ m} Λ(n)/n` -/

/-- The Mertens partial sum `∑_{n ≤ m} Λ(n)/n`. -/
def vmPartial (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 m, ArithmeticFunction.vonMangoldt n / (n : ℝ)

lemma mertens_int' (m : ℕ) (hm : 1 ≤ m) :
    |vmPartial m - Real.log (m : ℝ)| ≤ principalC := mertens_int m hm

/-! ### The superlevel set of the tent weight -/

/-- For `0 < s ≤ K` the superlevel set of the tent weight is the interval
`[L - 2K + s, L - s]`. -/
lemma tentWeight_ge_iff {L K : ℝ} (hK : 0 < K) (hL : 2 * K ≤ L) {s x : ℝ}
    (hs0 : 0 < s) (hsK : s ≤ K) :
    s ≤ tentWeight L K x ↔ L - 2 * K + s ≤ x ∧ x ≤ L - s := by
  rw [tentWeight_spec]
  by_cases h1 : x ≤ L - 2 * K
  · rw [if_pos h1]
    constructor
    · intro h; exact absurd h (by linarith)
    · rintro ⟨h2, h3⟩; linarith
  · by_cases h2 : x ≤ L - K
    · rw [if_neg h1, if_pos h2]
      constructor
      · intro h; exact ⟨by linarith, by linarith⟩
      · rintro ⟨ha, hb⟩; linarith
    · by_cases h3 : x ≤ L
      · rw [if_neg h1, if_neg h2, if_pos h3]
        constructor
        · intro h; exact ⟨by linarith, by linarith⟩
        · rintro ⟨ha, hb⟩; linarith
      · rw [if_neg h1, if_neg h2, if_neg h3]
        constructor
        · intro h; exact absurd h (by linarith)
        · rintro ⟨ha, hb⟩; linarith

/-! ### Converting the level condition into an inequality for `n` -/

lemma rpow_le_nat_iff {Q : ℝ} (hQ : 0 < Q) {y : ℝ} {n : ℕ} (hn : 0 < n) :
    Q ^ y ≤ (n : ℝ) ↔ y * Real.log Q ≤ Real.log (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  constructor
  · intro h
    have h' := Real.log_le_log (Real.rpow_pos_of_pos hQ y) h
    rwa [Real.log_rpow hQ] at h'
  · intro h
    have hle : Real.log Q * y ≤ Real.log (n : ℝ) := by rwa [mul_comm] at h
    have h' : Real.exp (Real.log Q * y) ≤ Real.exp (Real.log (n : ℝ)) := Real.exp_le_exp.mpr hle
    rwa [← Real.rpow_def_of_pos hQ y, Real.exp_log hn0] at h'

lemma nat_le_rpow_iff {Q : ℝ} (hQ : 0 < Q) {y : ℝ} {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ≤ Q ^ y ↔ Real.log (n : ℝ) ≤ y * Real.log Q := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  constructor
  · intro h
    have h' := Real.log_le_log hn0 h
    rwa [Real.log_rpow hQ] at h'
  · intro h
    have hle : Real.log (n : ℝ) ≤ Real.log Q * y := by rwa [mul_comm] at h
    have h' : (n : ℝ) ≤ Real.exp (Real.log Q * y) := by
      have h2 := Real.exp_le_exp.mpr hle
      rwa [Real.exp_log hn0] at h2
    rwa [← Real.rpow_def_of_pos hQ y] at h'

lemma two_le_rpow {Q y : ℝ} (hQ : 2 ≤ Q) (hy : 2 ≤ y) : 2 ≤ Q ^ y := by
  have h1 : (2 : ℝ) ≤ (2 : ℝ) ^ y := by
    have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
      (show (1 : ℝ) ≤ y by linarith)
    rwa [Real.rpow_one] at h
  have h2 : (2 : ℝ) ^ y ≤ Q ^ y := Real.rpow_le_rpow (by norm_num) hQ (by linarith)
  linarith

/-- For `0 < x ≤ K` and `n ≥ 1`, the tent weight of `log n / log q` exceeds `x`
precisely when `q^{L-2K+x} ≤ n ≤ q^{L-x}`. -/
lemma tentWeight_filter_iff {q : ℕ} (hq : 2 ≤ q) {L K : ℝ} (hK : 0 < K)
    (h2K : 2 * K + 2 ≤ L) {x : ℝ} (hx0 : 0 < x) (hxK : x ≤ K) {n : ℕ} (hn : 1 ≤ n) :
    x ≤ tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ))
      ↔ (q : ℝ) ^ (L - 2 * K + x) ≤ (n : ℝ) ∧ (n : ℝ) ≤ (q : ℝ) ^ (L - x) := by
  have h2KL : 2 * K ≤ L := by linarith
  have hQ1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hQ0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hlq0 : 0 < Real.log (q : ℝ) := Real.log_pos hQ1
  have hnpos : 0 < n := by omega
  rw [tentWeight_ge_iff hK h2KL hx0 hxK]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(rpow_le_nat_iff hQ0 hnpos).mpr (by rwa [le_div_iff₀ hlq0] at h1),
           (nat_le_rpow_iff hQ0 hnpos).mpr (by rwa [div_le_iff₀ hlq0] at h2)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [le_div_iff₀ hlq0]; exact (rpow_le_nat_iff hQ0 hnpos).mp h1,
           by rw [div_le_iff₀ hlq0]; exact (nat_le_rpow_iff hQ0 hnpos).mp h2⟩

lemma abs_sub_le_abs_add (P Q : ℝ) : |P - Q| ≤ |P| + |Q| := by
  rw [abs_sub_le_iff]
  refine ⟨?_, ?_⟩ <;> linarith [le_abs_self P, le_abs_self Q, neg_le_abs P, neg_le_abs Q]

/-- **Pointwise bound.**  For `0 < x ≤ K` the level sum
`𝒜(x) = ∑_{n ≤ N, f(log n/log q) ≥ x} Λ(n)/n` satisfies
`𝒜(x) = (2K-2x) log q + O(1)`, with an explicit absolute constant. -/
lemma tentWeight_sum_pointwise {q N : ℕ} (hq : 2 ≤ q) {L K : ℝ} (hK : 0 < K)
    (h2K : 2 * K + 2 ≤ L) (hN : (q : ℝ) ^ L ≤ (N : ℝ))
    {x : ℝ} (hx0 : 0 < x) (hxK : x ≤ K) :
    |(∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ =>
          x ≤ tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ))),
        ArithmeticFunction.vonMangoldt n / (n : ℝ)) - (2 * K - 2 * x) * Real.log (q : ℝ)|
      ≤ 2 * principalC + 2 * Real.log 2 := by
  have h2KL : 2 * K ≤ L := by linarith
  have hQ1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hQ0 : (0 : ℝ) < (q : ℝ) := by linarith
  have hQ2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  set A : ℝ := L - 2 * K + x with hA
  set B : ℝ := L - x with hB
  have hA2 : 2 ≤ A := by rw [hA]; linarith
  have hB2 : 2 ≤ B := by rw [hB]; linarith
  set a : ℝ := (q : ℝ) ^ A with ha
  set b : ℝ := (q : ℝ) ^ B with hb
  have ha2 : 2 ≤ a := by rw [ha]; exact two_le_rpow hQ2 hA2
  have hb2 : 2 ≤ b := by rw [hb]; exact two_le_rpow hQ2 hB2
  have ha1 : (1 : ℝ) ≤ a := by linarith
  have hab : a ≤ b := by
    rw [ha, hb, hA, hB]
    exact Real.rpow_le_rpow_of_exponent_le (le_of_lt hQ1) (by linarith)
  have hbN : b ≤ (N : ℝ) := by
    rw [hb, hB]
    calc (q : ℝ) ^ (L - x) ≤ (q : ℝ) ^ L :=
          Real.rpow_le_rpow_of_exponent_le (le_of_lt hQ1) (by linarith)
      _ ≤ (N : ℝ) := hN
  -- rewrite the filtering predicate
  have hflt : (Finset.Icc 1 N).filter (fun n : ℕ =>
        x ≤ tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)))
      = (Finset.Icc 1 N).filter (fun n : ℕ => a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b) := by
    apply Finset.filter_congr
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h := tentWeight_filter_iff hq hK h2K hx0 hxK hn.1
    rw [ha, hb, hA, hB]
    exact h
  rw [hflt]
  rw [sum_Icc_filter_interval (f := fun n => ArithmeticFunction.vonMangoldt n / (n : ℝ))
        ha1 hab hbN]
  -- reduce the interval sum to a difference of partial sums
  have hceil1 : 1 ≤ ⌈a⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hgap : ⌈a⌉₊ ≤ ⌊b⌋₊ + 1 := by
    have hcast1 : ((⌈a⌉₊ - 1 : ℕ) : ℝ) = (⌈a⌉₊ : ℝ) - 1 := by
      rw [Nat.cast_sub hceil1]; norm_num
    have hlt : ((⌈a⌉₊ - 1 : ℕ) : ℝ) < b := by
      have h1 : (⌈a⌉₊ : ℝ) - 1 < a := by
        have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ a by linarith)
        linarith
      rw [hcast1]; linarith
    have := Nat.le_floor (le_of_lt hlt)
    omega
  rw [sum_Icc_eq_Icc_sub (f := fun n => ArithmeticFunction.vonMangoldt n / (n : ℝ)) hceil1 hgap]
  change |vmPartial ⌊b⌋₊ - vmPartial (⌈a⌉₊ - 1) - (2 * K - 2 * x) * Real.log (q : ℝ)|
      ≤ 2 * principalC + 2 * Real.log 2
  -- log identities
  have hlogb : Real.log b = B * Real.log (q : ℝ) := by rw [hb]; exact Real.log_rpow hQ0 B
  have hloga : Real.log a = A * Real.log (q : ℝ) := by rw [ha]; exact Real.log_rpow hQ0 A
  have hlogba : Real.log b - Real.log a = (2 * K - 2 * x) * Real.log (q : ℝ) := by
    rw [hlogb, hloga, hA, hB]; ring
  have hcast1 : ((⌈a⌉₊ - 1 : ℕ) : ℝ) = (⌈a⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hceil1]; norm_num
  -- Mertens bounds
  have hm2 : 1 ≤ ⌊b⌋₊ := (Nat.one_le_floor_iff b).mpr (by linarith)
  have hm1 : 1 ≤ ⌈a⌉₊ - 1 := by
    have h2 : ⌈(2 : ℝ)⌉₊ = 2 := by norm_num
    have h : ⌈(2 : ℝ)⌉₊ ≤ ⌈a⌉₊ := Nat.ceil_mono (show (2 : ℝ) ≤ a by linarith)
    rw [h2] at h
    omega
  have hX : |vmPartial ⌊b⌋₊ - Real.log (⌊b⌋₊ : ℝ)| ≤ principalC := mertens_int' ⌊b⌋₊ hm2
  have hY : |vmPartial (⌈a⌉₊ - 1) - Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ)| ≤ principalC :=
    mertens_int' (⌈a⌉₊ - 1) hm1
  have hZ : |Real.log (⌊b⌋₊ : ℝ) - Real.log b| ≤ Real.log 2 := log_floor_sub_le hb2
  have hW : |Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ) - Real.log a| ≤ Real.log 2 := by
    have h := log_ceil_sub_one_sub_le ha2
    rwa [← hcast1] at h
  -- reorganise
  have hkey : vmPartial ⌊b⌋₊ - vmPartial (⌈a⌉₊ - 1) - (2 * K - 2 * x) * Real.log (q : ℝ)
      = (vmPartial ⌊b⌋₊ - Real.log (⌊b⌋₊ : ℝ))
        - (vmPartial (⌈a⌉₊ - 1) - Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ))
        + (Real.log (⌊b⌋₊ : ℝ) - Real.log b)
        - (Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ) - Real.log a) := by
    rw [← hlogba]; ring
  have hPQ : |vmPartial ⌊b⌋₊ - Real.log (⌊b⌋₊ : ℝ)
      - (vmPartial (⌈a⌉₊ - 1) - Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ))|
      ≤ |vmPartial ⌊b⌋₊ - Real.log (⌊b⌋₊ : ℝ)|
        + |vmPartial (⌈a⌉₊ - 1) - Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ)| := by
    exact abs_sub_le_abs_add (vmPartial ⌊b⌋₊ - Real.log (⌊b⌋₊ : ℝ))
      (vmPartial (⌈a⌉₊ - 1) - Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ))
  have hRS : |(Real.log (⌊b⌋₊ : ℝ) - Real.log b)
      - (Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ) - Real.log a)|
      ≤ |Real.log (⌊b⌋₊ : ℝ) - Real.log b|
        + |Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ) - Real.log a| := by
    exact abs_sub_le_abs_add (Real.log (⌊b⌋₊ : ℝ) - Real.log b)
      (Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ) - Real.log a)
  rw [hkey]
  rw [show (vmPartial ⌊b⌋₊ - Real.log (⌊b⌋₊ : ℝ))
        - (vmPartial (⌈a⌉₊ - 1) - Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ))
        + (Real.log (⌊b⌋₊ : ℝ) - Real.log b)
        - (Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ) - Real.log a)
      = ((vmPartial ⌊b⌋₊ - Real.log (⌊b⌋₊ : ℝ))
        - (vmPartial (⌈a⌉₊ - 1) - Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ)))
        + ((Real.log (⌊b⌋₊ : ℝ) - Real.log b)
          - (Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ) - Real.log a)) from by ring]
  calc |((vmPartial ⌊b⌋₊ - Real.log (⌊b⌋₊ : ℝ))
          - (vmPartial (⌈a⌉₊ - 1) - Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ)))
        + ((Real.log (⌊b⌋₊ : ℝ) - Real.log b)
          - (Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ) - Real.log a))|
      ≤ |(vmPartial ⌊b⌋₊ - Real.log (⌊b⌋₊ : ℝ))
          - (vmPartial (⌈a⌉₊ - 1) - Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ))|
        + |(Real.log (⌊b⌋₊ : ℝ) - Real.log b)
          - (Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ) - Real.log a)| := abs_add_le _ _
    _ ≤ (|vmPartial ⌊b⌋₊ - Real.log (⌊b⌋₊ : ℝ)|
          + |vmPartial (⌈a⌉₊ - 1) - Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ)|)
        + (|Real.log (⌊b⌋₊ : ℝ) - Real.log b|
          + |Real.log ((⌈a⌉₊ - 1 : ℕ) : ℝ) - Real.log a|) := add_le_add hPQ hRS
    _ ≤ 2 * principalC + 2 * Real.log 2 := by linarith [hX, hY, hZ, hW]

/-- **The principal-character Mellin estimate (real form).** -/
theorem tentSum_principal_real :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ}, 2 ≤ q → ∀ {L K : ℝ}, 0 < K → K ≤ 1 → 2 * K + 2 ≤ L →
      ∀ N : ℕ, (q : ℝ) ^ L ≤ (N : ℝ) →
      |(Real.log (q : ℝ))⁻¹ * (∑ n ∈ Finset.Icc 1 N,
            ArithmeticFunction.vonMangoldt n / (n : ℝ)
              * tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ))) - K ^ 2|
          ≤ C * (Real.log (q : ℝ))⁻¹ := by
  refine ⟨2 * principalC + 2 * Real.log 2, ?_, ?_⟩
  · have h1 := principalC_pos
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  · intro q hq L K hK hK1 h2K N hN
    have hK0 : 0 ≤ K := le_of_lt hK
    have h2KL : 2 * K ≤ L := by linarith
    have hQ1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
    have hlq0 : 0 < Real.log (q : ℝ) := Real.log_pos hQ1
    set C1 : ℝ := 2 * principalC + 2 * Real.log 2 with hC1def
    have hC1nn : 0 ≤ C1 := by
      rw [hC1def]
      have h1 := principalC_pos
      have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    -- the level function and the layer-cake identity
    set F : ℝ → ℝ := fun x => ∑ n ∈ Finset.Icc 1 N,
        (if x ≤ tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ))
          then ArithmeticFunction.vonMangoldt n / (n : ℝ) else 0) with hFdef
    have hlayer := Commons.Analysis.Integral.finset_layerCake (Finset.Icc 1 N)
        (fun n => ArithmeticFunction.vonMangoldt n / (n : ℝ))
        (fun n => tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ))) hK0
        (fun n _ => ⟨(tentWeight_bounds hK0 h2KL).1 _,
                     (tentWeight_bounds hK0 h2KL).2.1 _⟩)
    have hlayer' : (∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)
          * tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)))
        = ∫ x in (0 : ℝ)..K, F x := by
      rw [hlayer, hFdef]
    -- integrability of `F`
    have hFint : IntervalIntegrable F volume (0 : ℝ) K := by
      rw [hFdef]
      have hfuneq : (fun x : ℝ => ∑ n ∈ Finset.Icc 1 N,
            (if x ≤ tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ))
              then ArithmeticFunction.vonMangoldt n / (n : ℝ) else 0))
          = ∑ n ∈ Finset.Icc 1 N, (fun x : ℝ =>
              if x ≤ tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ))
                then ArithmeticFunction.vonMangoldt n / (n : ℝ) else 0) := by
        funext x; rw [Finset.sum_apply]
      rw [hfuneq]
      apply IntervalIntegrable.sum
      intro n hn
      rw [intervalIntegrable_iff]
      have hbase : IntegrableOn (fun _ : ℝ => ArithmeticFunction.vonMangoldt n / (n : ℝ))
          (Ι (0 : ℝ) K) volume := by
        rw [← intervalIntegrable_iff]; exact intervalIntegrable_const
      have hind : IntegrableOn ((Set.Iic (tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)))).indicator
          (fun _ : ℝ => ArithmeticFunction.vonMangoldt n / (n : ℝ))) (Ι (0 : ℝ) K) volume :=
        hbase.indicator measurableSet_Iic
      have hfun : (fun x : ℝ => if x ≤ tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ))
            then ArithmeticFunction.vonMangoldt n / (n : ℝ) else 0)
          = (Set.Iic (tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)))).indicator
              (fun _ : ℝ => ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
        funext x
        rw [Set.indicator_apply]
        simp only [Set.mem_Iic]
      rw [hfun]
      exact hind
    -- integrability of the linear comparison function
    have hGint : IntervalIntegrable (fun x : ℝ => (2 * K - 2 * x) * Real.log (q : ℝ))
        volume (0 : ℝ) K :=
      Continuous.intervalIntegrable (by continuity) 0 K
    -- value of the comparison integral
    have hGval : ∫ x in (0 : ℝ)..K, (2 * K - 2 * x) * Real.log (q : ℝ)
        = K ^ 2 * Real.log (q : ℝ) := by
      have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) K,
          HasDerivAt (fun y : ℝ => Real.log (q : ℝ) * (2 * K * y - y ^ 2))
            ((2 * K - 2 * x) * Real.log (q : ℝ)) x := by
        intro x hx
        have h1 : HasDerivAt (fun y : ℝ => 2 * K * y) (2 * K) x := by
          simpa using (hasDerivAt_id x).const_mul (2 * K)
        have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
          simpa using hasDerivAt_pow 2 x
        have h3 : HasDerivAt (fun y : ℝ => 2 * K * y - y ^ 2) (2 * K - 2 * x) x := h1.sub h2
        have h4 := h3.const_mul (Real.log (q : ℝ))
        simpa [mul_comm, mul_left_comm, mul_assoc] using h4
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        (by apply Continuous.intervalIntegrable; continuity)]
      ring
    -- pointwise comparison on `(0, K]`
    have hbnd : ∀ x ∈ Ι (0 : ℝ) K,
        ‖F x - (2 * K - 2 * x) * Real.log (q : ℝ)‖ ≤ C1 := by
      intro x hx
      rw [Set.uIoc_of_le hK0] at hx
      have hx0 : 0 < x := hx.1
      have hxK : x ≤ K := hx.2
      rw [Real.norm_eq_abs]
      have hFx : F x = ∑ n ∈ (Finset.Icc 1 N).filter (fun n : ℕ =>
          x ≤ tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ))),
          ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
        rw [hFdef]
        exact (Finset.sum_filter _ _).symm
      rw [hFx, hC1def]
      exact tentWeight_sum_pointwise hq hK h2K hN hx0 hxK
    -- put the pieces together
    have hni := intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hK0] at hni
    have hsub : (∫ x in (0 : ℝ)..K, F x)
        - (∫ x in (0 : ℝ)..K, (2 * K - 2 * x) * Real.log (q : ℝ))
        = ∫ x in (0 : ℝ)..K, (F x - (2 * K - 2 * x) * Real.log (q : ℝ)) :=
      (intervalIntegral.integral_sub hFint hGint).symm
    have hFG : |(∫ x in (0 : ℝ)..K, F x)
        - (∫ x in (0 : ℝ)..K, (2 * K - 2 * x) * Real.log (q : ℝ))| ≤ C1 * K := by
      rw [hsub]; exact hni
    rw [hlayer']
    have hfac : (Real.log (q : ℝ))⁻¹ * (∫ x in (0 : ℝ)..K, F x) - K ^ 2
        = (Real.log (q : ℝ))⁻¹
          * ((∫ x in (0 : ℝ)..K, F x) - K ^ 2 * Real.log (q : ℝ)) := by
      have hlqne : Real.log (q : ℝ) ≠ 0 := ne_of_gt hlq0
      field_simp
    rw [hfac, abs_mul, abs_of_pos (inv_pos.mpr hlq0)]
    calc (Real.log (q : ℝ))⁻¹ * |(∫ x in (0 : ℝ)..K, F x) - K ^ 2 * Real.log (q : ℝ)|
        = (Real.log (q : ℝ))⁻¹
          * |(∫ x in (0 : ℝ)..K, F x)
              - (∫ x in (0 : ℝ)..K, (2 * K - 2 * x) * Real.log (q : ℝ))| := by
          rw [hGval]
      _ ≤ (Real.log (q : ℝ))⁻¹ * (C1 * K) :=
          mul_le_mul_of_nonneg_left hFG (le_of_lt (inv_pos.mpr hlq0))
      _ ≤ (Real.log (q : ℝ))⁻¹ * C1 :=
          mul_le_mul_of_nonneg_left (mul_le_of_le_one_right hC1nn hK1)
            (le_of_lt (inv_pos.mpr hlq0))
      _ = C1 * (Real.log (q : ℝ))⁻¹ := by ring

/-- **Linnik's principal-character Mellin estimate** (Heath-Brown 1992, §13, principal
character case of Lemma 13.1): the tent-weighted von Mangoldt sum, normalised by
`log q`, differs from the area `K ^ 2` of the tent by `O(1 / log q)`. -/
theorem tentMellin_principal :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ}, 2 ≤ q → ∀ {L K : ℝ}, 0 < K → K ≤ 1 → 2 * K + 2 ≤ L →
      ∀ N : ℕ, (q : ℝ) ^ L ≤ (N : ℝ) →
      ‖(Real.log (q : ℝ))⁻¹ * (∑ n ∈ Finset.Icc 1 N,
            (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) *
              ((Commons.NumberTheory.Linnik.tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ))
          - ((K ^ 2 : ℝ) : ℂ)‖ ≤ C * (Real.log (q : ℝ))⁻¹ := by
  obtain ⟨C, hCpos, hC⟩ := tentSum_principal_real
  refine ⟨C, hCpos, ?_⟩
  intro q hq L K hK hK1 h2K N hN
  set S : ℝ := ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n / (n : ℝ)
      * tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) with hSdef
  have hterm : ∀ n ∈ Finset.Icc 1 N,
      (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ)
        * ((tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ)
      = ((ArithmeticFunction.vonMangoldt n / (n : ℝ)
          * tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ) := by
    intro n hn
    push_cast
    ring
  have hcast : (∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ)
        * ((tentWeight L K (Real.log (n : ℝ) / Real.log (q : ℝ)) : ℝ) : ℂ))
      = ((S : ℝ) : ℂ) := by
    rw [Finset.sum_congr rfl hterm, ← Complex.ofReal_sum, ← hSdef]
  rw [hcast]
  have hnorm : (Real.log (q : ℝ))⁻¹ * ((S : ℝ) : ℂ) - ((K ^ 2 : ℝ) : ℂ)
      = (((Real.log (q : ℝ))⁻¹ * S - K ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hnorm, Complex.norm_real, Real.norm_eq_abs]
  exact hC hq hK hK1 h2K N hN

end

end Commons.NumberTheory.Linnik

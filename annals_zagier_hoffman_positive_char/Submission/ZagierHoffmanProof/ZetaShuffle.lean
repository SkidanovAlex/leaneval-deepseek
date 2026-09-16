/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.StepB3
import Submission.ZagierHoffmanProof.StepD
import Submission.ZagierHoffmanProof.StepL1
import Submission.ZagierHoffmanProof.Basic
import Submission.ZagierHoffmanProof.DepthTwo
import Submission.Commons.Topology.Algebra.Valued.exp_balls_is_basis
import Submission.Commons.Topology.Algebra.Valued.summable_of_tendsto_v_zero
import Submission.Commons.Topology.InfiniteSum.fin_sum_tsum
import Submission.Commons.Topology.InfiniteSum.summable_fin_sum
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option autoImplicit false
set_option maxHeartbeats 8000000

open Polynomial RatFunc
open Filter
open scoped Topology BigOperators

/-!
# Summation of Thakur's level-wise product identity (paper (2.1)) over the levels

Thakur's identity (∗) (the team's `thakur_prod_one`, paper (2.1))

  `P_d(a)·P_d(b) = P_d(a+b) + Σ_{0<i<a+b} Δ^i_{a,b}·S_d(a+b-i, i)`

holds at every level `d ≥ 1`.  This module sums it over the levels, obtaining the **diagonal
identity at the ζ-level**

  `Σ_d P_d(a)·P_d(b) = ζ_A(a+b) + Σ_i Δ^i_{a,b}·ζ_A(a+b-i, i)`

(`tsum_diag_eq`), i.e. the "equal degree" part of the product `ζ_A(a)·ζ_A(b)`, together with the
intermediate statement `zeta_mul_split` expressing the product as
`ζ(a)ζ(b) = ζ(a,b) + ζ(b,a) + Σ_d P_d(a)P_d(b)`.  Together these give Thakur's shuffle relation
for depth-one MZVs (Thakur, *Shuffle relations for function field multizeta values*, IMRN 2010,
Theorem 5.1(2)) and, as a corollary, that the product of two depth-one MZVs lies in `𝒵 (a+b)`.

Everything is stated for an arbitrary finite field `F`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

open Commons.Topology.InfiniteSum

/-- The set of indices of the Δ-sum: `{i : 1 ≤ i ≤ a+b−1}`. -/
abbrev DeltaIdx (A B : ℕ) := {i : ℕ // i ∈ Finset.Icc 1 (A + B - 1)}

/-- ★★ **The diagonal identity at the ζ-level.**  Summing Thakur's level-wise product identity
`thakur_prod_one` over all levels `d` gives

  `Σ_d P_d(a)·P_d(b) = ζ_A(a+b) + Σ_{0<i<a+b} Δ^i_{a,b}·ζ_A(a+b−i, i)`. -/
theorem tsum_diag_eq (a b : ℕ+) :
    (∑' d : ℕ, P F d a * P F d b)
      = ζ_A F (single ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left a.pos (b : ℕ)⟩)
        + ∑ i : DeltaIdx (a : ℕ) (b : ℕ),
            (ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
              ζ_A F (thakurExp (a : ℕ) (b : ℕ) i) := by
  classical
  set n : ℕ+ := ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left a.pos (b : ℕ)⟩ with hn
  have hterm : ∀ d : ℕ, P F d a * P F d b =
      P F d n + ∑ i : DeltaIdx (a : ℕ) (b : ℕ),
            (ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
              S F 2 (by omega) (thakurExp (a : ℕ) (b : ℕ) i) d := by
    intro d
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · subst h0
      rw [P_zero_eq_one F a, P_zero_eq_one F b, one_mul, P_zero_eq_one F n]
      have hz : (∑ i : DeltaIdx (a : ℕ) (b : ℕ),
          (ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
            S F 2 (by omega) (thakurExp (a : ℕ) (b : ℕ) i) 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [S_zero_of_depth_ge_two F (r := 2) (by omega) (by omega)
          (thakurExp (a : ℕ) (b : ℕ) i), mul_zero]
      rw [hz, add_zero]
    · exact thakur_prod_one F d hpos a b
  have h1 : (∑' d : ℕ, P F d a * P F d b)
      = ∑' d : ℕ, (P F d n + ∑ i : DeltaIdx (a : ℕ) (b : ℕ),
              (ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
                S F 2 (by omega) (thakurExp (a : ℕ) (b : ℕ) i) d) :=
    tsum_congr hterm
  have hP : ∀ d : ℕ, S F 1 (by omega : 0 < 1) (single n) d = P F d n :=
    fun d => S_one_eq_P F d (by omega) (single n)
  have hsP : Summable (fun d : ℕ => P F d n) := by
    refine (summable_S F (r := 1) (by omega) (single n)).congr ?_
    intro d
    rw [hP d]
  have hsΔ : Summable (fun d : ℕ => ∑ i : DeltaIdx (a : ℕ) (b : ℕ),
      (ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        S F 2 (by omega) (thakurExp (a : ℕ) (b : ℕ) i) d) :=
    summable_fin_sum _
      (fun i => (summable_S F (r := 2) (by omega) (thakurExp (a : ℕ) (b : ℕ) i)).mul_left _)
  rw [h1, Summable.tsum_add hsP hsΔ, hn]
  congr 1
  · rw [zeta_eq_tsum_block F (r := 1) (by omega) (single n)]
    exact tsum_congr (fun d => (hP d).symm)
  · rw [← fin_sum_tsum (fun (i : DeltaIdx (a : ℕ) (b : ℕ)) (d : ℕ) =>
      (ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
        S F 2 (by omega) (thakurExp (a : ℕ) (b : ℕ) i) d)
      (fun i => (summable_S F (r := 2) (by omega) (thakurExp (a : ℕ) (b : ℕ) i)).mul_left _)]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [tsum_mul_left, zeta_eq_tsum_block F (r := 2) (by omega) (thakurExp (a : ℕ) (b : ℕ) i)]

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## 2. The shuffle relation for depth-one MZVs -/

/-- The depth-one power-sum families are summable. -/
lemma summable_P (a : ℕ+) : Summable (fun d : ℕ => P F d a) := by
  have hP : ∀ d : ℕ, S F 1 (by omega : 0 < 1) (single a) d = P F d a :=
    fun d => S_one_eq_P F d (by omega) (single a)
  refine (summable_S F (r := 1) (by omega) (single a)).congr ?_
  intro d
  rw [hP d]

/-- `∑'_d P_d(a) = ζ_A(a)`. -/
lemma tsum_P_eq_zeta (a : ℕ+) : (∑' d : ℕ, P F d a) = ζ_A F (single a) := by
  rw [zeta_eq_tsum_block F (r := 1) (by omega) (single a)]
  exact tsum_congr (fun d => (S_one_eq_P F d (by omega) (single a)).symm)

/-- The level-`d` block of `ζ_A(a,b)` is the product `P_d(a)·Σ_{e<d} P_e(b)`. -/
lemma S_pair_eq (a b : ℕ+) (d : ℕ) :
    S F 2 (by omega : 0 < 2) (pair a b) d = P F d a * ∑ e ∈ Finset.range d, P F e b := by
  rw [S_d_recursion F 2 (by omega) (by omega) (by omega) (pair a b) d]
  have h0 : (pair a b) ⟨0, by omega⟩ = a := rfl
  have htail : (fun j : Fin 1 => (pair a b) ⟨(j : ℕ) + 1, by omega⟩) = single b := by
    funext j
    rfl
  rw [h0, htail, S_lt_eq_sum_levels F 1 (by omega) (single b) d]
  congr 1
  exact Finset.sum_congr rfl (fun e _ => S_one_eq_P F e (by omega) (single b))

/-- `∑'_d P_d(a)·Σ_{e<d}P_e(b) = ζ_A(a,b)`: the ζ-level form of the first region. -/
lemma tsum_pair_eq_zeta (a b : ℕ+) :
    (∑' d : ℕ, P F d a * ∑ e ∈ Finset.range d, P F e b) = ζ_A F (pair a b) := by
  rw [zeta_eq_tsum_block F (r := 2) (by omega) (pair a b)]
  exact tsum_congr (fun d => (S_pair_eq F a b d).symm)

/-- The "first minus second" block family of the product `ζ_A(a)·ζ_A(b)` is summable. -/
lemma summable_pair_left (a b : ℕ+) :
    Summable (fun d : ℕ => P F d a * ∑ e ∈ Finset.range d, P F e b) := by
  have hS := summable_S F (r := 2) (by omega) (pair a b)
  exact hS.congr (fun d => S_pair_eq F a b d)

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- The "equal degree" (diagonal) family of the product `ζ_A(a)·ζ_A(b)` is summable: the terms
tend to `0` because `v (P_d a) ≤ exp (−d·(a + jMin a))` and `v (P_d b) ≤ 1`. -/
lemma summable_diag (a b : ℕ+) : Summable (fun d : ℕ => P F d a * P F d b) := by
  refine Commons.Topology.Algebra.Valued.summable_of_tendsto_v_zero
    (K := RatFunc.CompletionAtInfty F) ?_
  intro n
  rcases lt_or_ge (0 : ℤ) n with hnpos | hnle
  · -- if the ball is large (`n > 0`) every term lies in it
    filter_upwards with d
    show Valued.v (P F d a * P F d b) < WithZero.exp n
    rw [Valuation.map_mul]
    refine lt_of_le_of_lt (mul_le_mul' (v_P_le_one F d a) (v_P_le_one F d b)) ?_
    rw [one_mul]
    exact lt_of_lt_of_le (WithZero.exp_lt_exp.mpr hnpos) le_rfl
  · -- otherwise all terms with `d ≥ -n + 1` lie in the ball
    filter_upwards [eventually_ge_atTop ((-n).toNat + 1)] with d hd
    show Valued.v (P F d a * P F d b) < WithZero.exp n
    have hDn : (-n : ℤ) < (((-n).toNat + 1 : ℕ) : ℤ) := by
      have h2 : ((-n).toNat : ℤ) = -n := Int.toNat_of_nonneg (by omega)
      push_cast [h2]
      omega
    have hd1 : 1 ≤ d := by omega
    rw [Valuation.map_mul]
    refine lt_of_le_of_lt (mul_le_mul' (v_P_le F d hd1 a) (v_P_le_one F d b)) ?_
    rw [mul_one, WithZero.exp_lt_exp]
    have hdZ : (-n : ℤ) < (d : ℤ) := lt_of_lt_of_le hDn (by exact_mod_cast hd)
    have hC1 : (1 : ℤ) ≤ (a : ℤ) + (jMin F a : ℤ) := by
      have := exp_pos_arg F a
      omega
    have hd0 : (0 : ℤ) ≤ (d : ℤ) := by exact_mod_cast Nat.zero_le d
    have hprod : (d : ℤ) ≤ (d : ℤ) * ((a : ℤ) + (jMin F a : ℤ)) :=
      le_mul_of_one_le_right hd0 hC1
    linarith


variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- **The finite box identity.**  For every `N`, the product of the truncations of the two
level-series splits into the three degree-regions `e < d`, `d < e`, `d = e`. -/
lemma box_identity (a b : ℕ+) (N : ℕ) :
    (∑ d ∈ Finset.range N, P F d a) * (∑ e ∈ Finset.range N, P F e b)
      = (∑ d ∈ Finset.range N, P F d a * ∑ e ∈ Finset.range d, P F e b)
        + (∑ e ∈ Finset.range N, P F e b * ∑ d ∈ Finset.range e, P F d a)
        + (∑ d ∈ Finset.range N, P F d a * P F d b) := by
  -- the pointwise splitting of the inner sum
  have hpt : ∀ d : ℕ, d < N → P F d a * (∑ e ∈ Finset.range N, P F e b)
      = (P F d a * ∑ e ∈ Finset.range d, P F e b) + P F d a * P F d b
        + P F d a * (∑ e ∈ Finset.Ico (d + 1) N, P F e b) := by
    intro d hd
    rw [← mul_add, ← mul_add]
    congr 1
    have h1 := Finset.sum_range_add_sum_Ico (fun e : ℕ => P F e b) (show d + 1 ≤ N by omega)
    rw [Finset.sum_range_succ] at h1
    exact h1.symm
  -- the triangular swap
  have hind1 : ∀ d : ℕ, (∑ e ∈ Finset.range N, if d < e then P F e b else 0)
      = ∑ e ∈ Finset.Ico (d + 1) N, P F e b := by
    intro d
    rw [← Finset.sum_filter]
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  have hind2 : ∀ e : ℕ, e ≤ N → (∑ d ∈ Finset.range N, if d < e then P F d a else 0)
      = ∑ d ∈ Finset.range e, P F d a := by
    intro e he
    rw [← Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hswap : (∑ d ∈ Finset.range N, P F d a * ∑ e ∈ Finset.Ico (d + 1) N, P F e b)
      = ∑ e ∈ Finset.range N, P F e b * ∑ d ∈ Finset.range e, P F d a := by
    have h1 : (∑ d ∈ Finset.range N, P F d a * ∑ e ∈ Finset.Ico (d + 1) N, P F e b)
        = ∑ d ∈ Finset.range N, ∑ e ∈ Finset.range N,
            (if d < e then P F d a * P F e b else 0) := by
      refine Finset.sum_congr rfl ?_
      intro d _
      rw [← hind1 d, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro e _
      by_cases h : d < e
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, mul_zero]
    have h2 : (∑ e ∈ Finset.range N, P F e b * ∑ d ∈ Finset.range e, P F d a)
        = ∑ e ∈ Finset.range N, ∑ d ∈ Finset.range N,
            (if d < e then P F d a * P F e b else 0) := by
      refine Finset.sum_congr rfl ?_
      intro e he
      rw [← hind2 e (Finset.mem_range.mp he).le, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro d _
      by_cases h : d < e
      · rw [if_pos h, if_pos h, mul_comm]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [h1, h2, Finset.sum_comm]
  rw [Finset.sum_mul,
    Finset.sum_congr rfl (fun d hd => hpt d (Finset.mem_range.mp hd)),
    Finset.sum_add_distrib, Finset.sum_add_distrib, hswap]
  ring



variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★★ **The shuffle (stuffle) relation for depth-one MZVs**: for `a b ∈ ℕ+`,

  `ζ_A(a)·ζ_A(b) = ζ_A(a+b) + ζ_A(a,b) + ζ_A(b,a) + Σ_{0<i<a+b} Δ^i_{a,b}·ζ_A(a+b−i, i)`.

The product splits by the degree trichotomy (`box_identity` + limits, using only that the three
region families are summable), and the equal-degree part is the diagonal identity `tsum_diag_eq`. -/
theorem zeta_mul_split (a b : ℕ+) :
    ζ_A F (single a) * ζ_A F (single b)
      = ζ_A F (pair a b) + ζ_A F (pair b a) + (∑' d, P F d a * P F d b) := by
  have hfa : Tendsto (fun N : ℕ => ∑ d ∈ Finset.range N, P F d a) atTop
      (𝓝 (ζ_A F (single a))) := by
    rw [← tsum_P_eq_zeta F a]
    exact (summable_P F a).hasSum.tendsto_sum_nat
  have hfb : Tendsto (fun N : ℕ => ∑ e ∈ Finset.range N, P F e b) atTop
      (𝓝 (ζ_A F (single b))) := by
    rw [← tsum_P_eq_zeta F b]
    exact (summable_P F b).hasSum.tendsto_sum_nat
  have hA : Tendsto (fun N : ℕ => ∑ d ∈ Finset.range N,
      P F d a * ∑ e ∈ Finset.range d, P F e b) atTop (𝓝 (ζ_A F (pair a b))) := by
    rw [← tsum_pair_eq_zeta F a b]
    exact (summable_pair_left F a b).hasSum.tendsto_sum_nat
  have hB : Tendsto (fun N : ℕ => ∑ e ∈ Finset.range N,
      P F e b * ∑ d ∈ Finset.range e, P F d a) atTop (𝓝 (ζ_A F (pair b a))) := by
    rw [← tsum_pair_eq_zeta F b a]
    exact (summable_pair_left F b a).hasSum.tendsto_sum_nat
  have hD : Tendsto (fun N : ℕ => ∑ d ∈ Finset.range N, P F d a * P F d b) atTop
      (𝓝 (∑' d, P F d a * P F d b)) :=
    (summable_diag F a b).hasSum.tendsto_sum_nat
  have hL : Tendsto (fun N : ℕ => (∑ d ∈ Finset.range N, P F d a)
      * (∑ e ∈ Finset.range N, P F e b)) atTop (𝓝 (ζ_A F (single a) * ζ_A F (single b))) :=
    hfa.mul hfb
  have hR : Tendsto (fun N : ℕ =>
      (∑ d ∈ Finset.range N, P F d a * ∑ e ∈ Finset.range d, P F e b)
        + (∑ e ∈ Finset.range N, P F e b * ∑ d ∈ Finset.range e, P F d a)
        + (∑ d ∈ Finset.range N, P F d a * P F d b)) atTop
      (𝓝 (ζ_A F (pair a b) + ζ_A F (pair b a) + (∑' d, P F d a * P F d b))) :=
    (hA.add hB).add hD
  have hEq : (fun N : ℕ => (∑ d ∈ Finset.range N, P F d a) * (∑ e ∈ Finset.range N, P F e b))
      =ᶠ[atTop] (fun N : ℕ =>
        (∑ d ∈ Finset.range N, P F d a * ∑ e ∈ Finset.range d, P F e b)
          + (∑ e ∈ Finset.range N, P F e b * ∑ d ∈ Finset.range e, P F d a)
          + (∑ d ∈ Finset.range N, P F d a * P F d b)) :=
    Eventually.of_forall (fun N => box_identity F a b N)
  exact tendsto_nhds_unique hL (hR.congr' hEq.symm)

/-- ★★★ **Thakur's shuffle relation for depth-one MZVs** (Thakur, IMRN 2010, Theorem 5.1(2)):

  `ζ_A(a)·ζ_A(b) = ζ_A(a+b) + ζ_A(a,b) + ζ_A(b,a) + Σ_{0<i<a+b} Δ^i_{a,b}·ζ_A(a+b−i, i)`. -/
theorem zeta_mul_zeta (a b : ℕ+) :
    ζ_A F (single a) * ζ_A F (single b)
      = ζ_A F (single ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left a.pos (b : ℕ)⟩)
        + ζ_A F (pair a b) + ζ_A F (pair b a)
        + ∑ i : DeltaIdx (a : ℕ) (b : ℕ),
            (ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : RatFunc.CompletionAtInfty F) *
              ζ_A F (thakurExp (a : ℕ) (b : ℕ) i) := by
  rw [zeta_mul_split F a b, tsum_diag_eq F a b]
  ring



variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- Any MZV whose defining tuple has weight `w` lies in `𝒵 w`. -/
lemma zeta_mem_Z {r : ℕ} (𝔰 : Fin r → ℕ+) {w : ℕ} (h : weight r 𝔰 = w) :
    ζ_A F 𝔰 ∈ 𝒵 F w :=
  ζ_A_weight_subset_span F w r ⟨𝔰, h, rfl⟩

/-- ★★ **The product of two depth-one MZVs of weights `a` and `b` lies in `𝒵 (a+b)`**: the
shuffle relation exhibits it as a `K`-linear combination of weight-`(a+b)` MZVs. -/
theorem zeta_single_mul_mem_Z (a b : ℕ+) :
    ζ_A F (single a) * ζ_A F (single b) ∈ 𝒵 F ((a : ℕ) + (b : ℕ)) := by
  rw [zeta_mul_zeta F a b]
  have hweight_thakurExp : ∀ i : DeltaIdx (a : ℕ) (b : ℕ),
      weight 2 (thakurExp (a : ℕ) (b : ℕ) i) = (a : ℕ) + (b : ℕ) :=
    fun i => weight_thakurExp (a : ℕ) (b : ℕ) i
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_
  · exact zeta_mem_Z F (single ⟨(a : ℕ) + (b : ℕ), Nat.add_pos_left a.pos (b : ℕ)⟩)
      (weight_single _)
  · exact zeta_mem_Z F (pair a b) (weight_pair a b)
  · exact zeta_mem_Z F (pair b a) ((weight_pair b a).trans (Nat.add_comm (b : ℕ) (a : ℕ)))
  · refine Submodule.sum_mem _ (fun i _ => ?_)
    have hsm : ((ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : ℤ) : RatFunc.CompletionAtInfty F)
        = (algebraMap (RatFunc F) (RatFunc.CompletionAtInfty F))
            ((ChenDeltaZ F (a : ℕ) (b : ℕ) i.1 : ℤ) : RatFunc F) := by
      rw [map_intCast]
    rw [hsm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (zeta_mem_Z F (thakurExp (a : ℕ) (b : ℕ) i)
      (hweight_thakurExp i))

end ZagierHoffmanPositiveChar

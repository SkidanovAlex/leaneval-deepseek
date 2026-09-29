import Mathlib

open Finset Filter
open scoped BigOperators Topology

/-
# Riemann sums of step functions

A step function on `[0,m]` with breakpoints `a 0 < a 1 < … < a N = m` and values
`c 0, …, c (N-1)` is `G(t) = c i` on `[a i, a (i+1))`.  This module proves the convergence of
its Riemann sums to the average value

`(1/d)·Σ_{j=1}^{d} G(m·j/d) → (1/m)·Σ_i c_i·(a(i+1) - a i)`,

where the right-hand side is `(1/m)∫_0^m G` (the integral of a step function being the sum of
`c_i` times the lengths of the pieces).  The proof is the elementary counting argument: the number
of `j ∈ [1,d]` with `a i ≤ m j/d < a(i+1)` is within `2` of `d·(a(i+1) - a i)/m`, since the
integers `j ∈ [1,d]` in `[α, β)` form the interval `[max 1 ⌈α⌉, min d (⌈β⌉-1)]`
(`filter_Icc_eq_Icc`, `card_filter_Icc_sub_close`).

This is used for the paper's "cost of an integration": the additional denominators coming from
integrating the functions `f_i` are measured by the Riemann sums of the model function of
Lemma `lcm-2`.
-/

namespace Submission.CDT.StepRiemann

/-- A step function with breakpoints `a 0 < a 1 < … < a N` and values `c 0, …, c (N-1)`:
the value at `t` is `c i` when `a i ≤ t < a (i+1)`. -/
noncomputable def stepFun (a c : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range N, if a i ≤ t ∧ t < a (i + 1) then c i else 0

/-- The integers `j ∈ [1,d]` with `α ≤ j < β` form the interval `[max 1 ⌈α⌉, min d (⌈β⌉-1)]`. -/
theorem filter_Icc_eq_Icc (d : ℕ) (α β : ℝ) :
    (Finset.Icc 1 d).filter (fun j : ℕ => α ≤ (j : ℝ) ∧ (j : ℝ) < β)
      = Finset.Icc (max (1:ℕ) ⌈α⌉₊) (min d (⌈β⌉₊ - 1)) := by
  classical
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hj1, hjd⟩, hjα, hjβ⟩
    refine ⟨max_le hj1 ?_, le_min hjd ?_⟩
    · exact Nat.ceil_le.mpr hjα
    · have h : j < ⌈β⌉₊ := Nat.lt_ceil.mpr hjβ
      omega
  · rintro ⟨h1, h2⟩
    have hj1 : 1 ≤ j := le_trans (le_max_left 1 ⌈α⌉₊) h1
    have hjd : j ≤ d := le_trans h2 (min_le_left _ _)
    have hjα : ⌈α⌉₊ ≤ j := le_trans (le_max_right 1 ⌈α⌉₊) h1
    have hjβ : j ≤ ⌈β⌉₊ - 1 := le_trans h2 (min_le_right _ _)
    refine ⟨⟨hj1, hjd⟩, Nat.ceil_le.mp hjα, ?_⟩
    have h3 : j < ⌈β⌉₊ := by
      rcases Nat.eq_zero_or_pos ⌈β⌉₊ with h | h
      · omega
      · omega
    exact Nat.lt_ceil.mp h3

/-- The number of integers `j ∈ [1,d]` with `α ≤ j < β` is within `2` of `β - α`
(for `0 ≤ α ≤ β ≤ d`). -/
theorem card_filter_Icc_sub_close (d : ℕ) (α β : ℝ) (hα : 0 ≤ α) (hαβ : α ≤ β)
    (hβ : β ≤ (d : ℝ)) :
    |(((Finset.Icc 1 d).filter (fun j : ℕ => α ≤ (j : ℝ) ∧ (j : ℝ) < β)).card : ℝ) - (β - α)| ≤ 2 := by
  classical
  rw [filter_Icc_eq_Icc]
  have hceilα' : ((⌈α⌉₊ : ℕ) : ℝ) < α + 1 := Nat.ceil_lt_add_one hα
  have hceilβ : β ≤ ((⌈β⌉₊ : ℕ) : ℝ) := Nat.le_ceil β
  have hA : ((max (1:ℕ) ⌈α⌉₊ : ℕ) : ℝ) ≤ α + 1 := by
    have h2 : ((max (1:ℕ) ⌈α⌉₊ : ℕ) : ℝ) = max 1 (((⌈α⌉₊ : ℕ)) : ℝ) := by
      rw [Nat.cast_max]; simp
    rw [h2]
    exact max_le (by linarith) (le_of_lt hceilα')
  have hA' : α ≤ ((max (1:ℕ) ⌈α⌉₊ : ℕ) : ℝ) := by
    have h2 : ((max (1:ℕ) ⌈α⌉₊ : ℕ) : ℝ) = max 1 (((⌈α⌉₊ : ℕ)) : ℝ) := by
      rw [Nat.cast_max]; simp
    rw [h2]
    exact le_trans (Nat.le_ceil α) (le_max_right _ _)
  have hBsub : ⌈β⌉₊ - 1 ≤ d := by
    have hlt : (⌈β⌉₊ : ℝ) < (d : ℝ) + 1 := by
      have h2 := Nat.ceil_lt_add_one (le_trans hα hαβ)
      linarith [hβ]
    have hle : ⌈β⌉₊ ≤ d := by
      by_contra hcon
      push Not at hcon
      have h3 : (d : ℝ) + 1 ≤ (⌈β⌉₊ : ℝ) := by exact_mod_cast hcon
      linarith
    omega
  have hmin : min d (⌈β⌉₊ - 1) = ⌈β⌉₊ - 1 := min_eq_right hBsub
  have hB : ((min d (⌈β⌉₊ - 1) : ℕ) : ℝ) ≤ β + 1 := by
    rw [hmin]
    have h2 := Nat.ceil_lt_add_one (le_trans hα hαβ)
    have h3 : ((⌈β⌉₊ - 1 : ℕ) : ℝ) ≤ ((⌈β⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le _ _
    linarith
  have hB' : β - 1 ≤ ((min d (⌈β⌉₊ - 1) : ℕ) : ℝ) := by
    rw [hmin]
    have h3 : ((⌈β⌉₊ : ℕ) : ℝ) ≤ ((⌈β⌉₊ - 1 : ℕ) : ℝ) + 1 := by
      have h4 : ⌈β⌉₊ ≤ (⌈β⌉₊ - 1) + 1 := by omega
      exact_mod_cast h4
    linarith [hceilβ]
  by_cases hAB : max (1:ℕ) ⌈α⌉₊ ≤ min d (⌈β⌉₊ - 1)
  · rw [Nat.card_Icc]
    have hcast : ((min d (⌈β⌉₊ - 1) + 1 - max (1:ℕ) ⌈α⌉₊ : ℕ) : ℝ)
        = ((min d (⌈β⌉₊ - 1) : ℕ) : ℝ) + 1 - ((max (1:ℕ) ⌈α⌉₊ : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : max (1:ℕ) ⌈α⌉₊ ≤ min d (⌈β⌉₊ - 1) + 1), Nat.cast_add,
        Nat.cast_one]
    rw [hcast, abs_le]
    constructor <;> linarith
  · have hemp : Finset.Icc (max (1:ℕ) ⌈α⌉₊) (min d (⌈β⌉₊ - 1)) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro j hj
      rw [Finset.mem_Icc] at hj
      omega
    rw [hemp, Finset.card_empty]
    simp only [Nat.cast_zero, zero_sub, abs_neg]
    have hBM : β ≤ α + 1 := by
      have h : min d (⌈β⌉₊ - 1) < max (1:ℕ) ⌈α⌉₊ := lt_of_not_ge hAB
      rcases (min_lt_iff.mp h) with h' | h'
      · have h'R : (d : ℝ) < ((max (1:ℕ) ⌈α⌉₊ : ℕ) : ℝ) := by exact_mod_cast h'
        linarith [h'R, hA, hβ]
      · have h2 : ⌈β⌉₊ ≤ max (1:ℕ) ⌈α⌉₊ := by omega
        have h3 : ((⌈β⌉₊ : ℕ) : ℝ) ≤ ((max (1:ℕ) ⌈α⌉₊ : ℕ) : ℝ) := by exact_mod_cast h2
        linarith
    rw [abs_le]
    constructor <;> linarith



/-- The Riemann sums `(1/d)Σ_{j=1}^d G(mj/d)` of a step function `G` converge to the average
`(1/m)Σ_i c_i (a(i+1) - a i)` of `G` over `[0,m]` (which is `(1/m)∫_0^m G`). -/
theorem tendsto_riemannSum_stepFun (m : ℝ) (hm : 0 < m) (a c : ℕ → ℝ) (N : ℕ)
    (ha0 : 0 ≤ a 0) (hmono : ∀ i < N, a i < a (i + 1)) (hNm : a N ≤ m) :
    Filter.Tendsto (fun d : ℕ =>
        (∑ j ∈ Finset.Icc 1 d, stepFun a c N (m * (j:ℝ) / (d:ℝ))) / (d:ℝ))
      Filter.atTop (nhds ((∑ i ∈ Finset.range N, c i * (a (i + 1) - a i)) / m)) := by
  classical
  have hmono' : ∀ i, i ≤ N → 0 ≤ a i := by
    intro i hi
    induction i with
    | zero => simpa using ha0
    | succ i ih => exact le_trans (ih (by omega)) (le_of_lt (hmono i (by omega)))
  have hle : ∀ i k, i ≤ k → k ≤ N → a i ≤ a k := by
    intro i k _
    induction k with
    | zero =>
      intro _
      have h : i = 0 := by omega
      subst h; exact le_refl _
    | succ k ih =>
      intro hkN
      rcases Nat.eq_or_lt_of_le (by assumption : i ≤ k + 1) with h | h
      · rw [h]
      · have h1 : a i ≤ a k := ih (by omega) (by omega)
        have h2 : a k ≤ a (k + 1) := le_of_lt (hmono k (by omega))
        linarith
  -- the sum of the step function at the sample points
  have hsum : ∀ d : ℕ,
      (∑ j ∈ Finset.Icc 1 d, stepFun a c N (m * (j:ℝ) / (d:ℝ)))
        = ∑ i ∈ Finset.range N, c i * (((Finset.Icc 1 d).filter
            (fun j : ℕ => a i ≤ m * (j:ℝ) / (d:ℝ) ∧ m * (j:ℝ) / (d:ℝ) < a (i + 1))).card : ℝ) := by
    intro d
    simp only [stepFun]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  -- the counting bound
  have hcount : ∀ (i : ℕ), i < N → ∀ (d : ℕ), 1 ≤ d →
      abs ((((Finset.Icc 1 d).filter
            (fun j : ℕ => a i ≤ m * (j:ℝ) / (d:ℝ) ∧ m * (j:ℝ) / (d:ℝ) < a (i + 1))).card : ℝ)
          - (d:ℝ) * (a (i + 1) - a i) / m) ≤ 2 := by
    intro i hi d hd
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hai : 0 ≤ a i := hmono' i (le_of_lt hi)
    have haia : a i < a (i + 1) := hmono i hi
    have hain : a (i + 1) ≤ m := le_trans (hle (i + 1) N (by omega) le_rfl) hNm
    have hset : (Finset.Icc 1 d).filter
          (fun j : ℕ => a i ≤ m * (j:ℝ) / (d:ℝ) ∧ m * (j:ℝ) / (d:ℝ) < a (i + 1))
        = (Finset.Icc 1 d).filter
          (fun j : ℕ => (d:ℝ) * a i / m ≤ (j:ℝ) ∧ (j:ℝ) < (d:ℝ) * a (i + 1) / m) := by
      refine Finset.filter_congr (fun j _ => ?_)
      constructor
      · rintro ⟨h1, h2⟩
        constructor
        · rw [div_le_iff₀ hm]
          have h3 : a i ≤ m * (j:ℝ) / (d:ℝ) := h1
          rw [le_div_iff₀ hdR] at h3
          linarith
        · rw [lt_div_iff₀ hm]
          have h3 : m * (j:ℝ) / (d:ℝ) < a (i + 1) := h2
          rw [div_lt_iff₀ hdR] at h3
          linarith
      · rintro ⟨h1, h2⟩
        constructor
        · rw [le_div_iff₀ hdR]
          have h3 : (d:ℝ) * a i / m ≤ (j:ℝ) := h1
          rw [div_le_iff₀ hm] at h3
          linarith
        · rw [div_lt_iff₀ hdR]
          have h3 : (j:ℝ) < (d:ℝ) * a (i + 1) / m := h2
          rw [lt_div_iff₀ hm] at h3
          linarith
    rw [hset]
    have := card_filter_Icc_sub_close d ((d:ℝ) * a i / m) ((d:ℝ) * a (i + 1) / m)
      (by positivity) (by
        rw [le_div_iff₀ hm]
        have h : (d:ℝ) * a i / m * m = (d:ℝ) * a i := by field_simp
        rw [h]
        exact mul_le_mul_of_nonneg_left (le_of_lt haia) hdR.le) (by
        rw [div_le_iff₀ hm]
        exact mul_le_mul_of_nonneg_left hain hdR.le)
    convert this using 2
    ring
  -- conclusion by squeezing
  have hmain : ∀ d : ℕ, 1 ≤ d →
      |(∑ j ∈ Finset.Icc 1 d, stepFun a c N (m * (j:ℝ) / (d:ℝ))) / (d:ℝ)
          - (∑ i ∈ Finset.range N, c i * (a (i + 1) - a i)) / m|
        ≤ (∑ i ∈ Finset.range N, |c i|) * 2 / (d:ℝ) := by
    intro d hd
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    rw [hsum d]
    simp only [Finset.sum_div]
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ i ∈ Finset.range N,
        |c i * (((Finset.Icc 1 d).filter
            (fun j : ℕ => a i ≤ m * (j:ℝ) / (d:ℝ) ∧ m * (j:ℝ) / (d:ℝ) < a (i + 1))).card : ℝ)
            / (d:ℝ) - c i * (a (i + 1) - a i) / m|
          ≤ |c i| * (2 / (d:ℝ)) := by
      intro i hi
      have hi' : i < N := Finset.mem_range.mp hi
      have h1 := hcount i hi' d hd
      have h2 : c i * (((Finset.Icc 1 d).filter
            (fun j : ℕ => a i ≤ m * (j:ℝ) / (d:ℝ) ∧ m * (j:ℝ) / (d:ℝ) < a (i + 1))).card : ℝ)
            / (d:ℝ) - c i * (a (i + 1) - a i) / m
          = c i * ((((Finset.Icc 1 d).filter
            (fun j : ℕ => a i ≤ m * (j:ℝ) / (d:ℝ) ∧ m * (j:ℝ) / (d:ℝ) < a (i + 1))).card : ℝ)
            / (d:ℝ) - (a (i + 1) - a i) / m) := by ring
      rw [h2, abs_mul]
      have h3 : |(((Finset.Icc 1 d).filter
            (fun j : ℕ => a i ≤ m * (j:ℝ) / (d:ℝ) ∧ m * (j:ℝ) / (d:ℝ) < a (i + 1))).card : ℝ)
            / (d:ℝ) - (a (i + 1) - a i) / m| ≤ 2 / (d:ℝ) := by
        have h4 : ((((Finset.Icc 1 d).filter
            (fun j : ℕ => a i ≤ m * (j:ℝ) / (d:ℝ) ∧ m * (j:ℝ) / (d:ℝ) < a (i + 1))).card : ℝ)
            - (d:ℝ) * (a (i + 1) - a i) / m) / (d:ℝ)
          = (((Finset.Icc 1 d).filter
            (fun j : ℕ => a i ≤ m * (j:ℝ) / (d:ℝ) ∧ m * (j:ℝ) / (d:ℝ) < a (i + 1))).card : ℝ)
            / (d:ℝ) - (a (i + 1) - a i) / m := by
          first | (field_simp; ring) | field_simp
        rw [← h4, abs_div, abs_of_pos hdR]
        exact div_le_div_of_nonneg_right h1 hdR.le
      exact mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    calc |∑ i ∈ Finset.range N,
          (c i * (((Finset.Icc 1 d).filter
            (fun j : ℕ => a i ≤ m * (j:ℝ) / (d:ℝ) ∧ m * (j:ℝ) / (d:ℝ) < a (i + 1))).card : ℝ)
            / (d:ℝ) - c i * (a (i + 1) - a i) / m)|
        ≤ ∑ i ∈ Finset.range N,
          |c i * (((Finset.Icc 1 d).filter
            (fun j : ℕ => a i ≤ m * (j:ℝ) / (d:ℝ) ∧ m * (j:ℝ) / (d:ℝ) < a (i + 1))).card : ℝ)
            / (d:ℝ) - c i * (a (i + 1) - a i) / m| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range N, |c i| * (2 / (d:ℝ)) := Finset.sum_le_sum hterm
      _ = (∑ i ∈ Finset.range N, |c i|) * 2 / (d:ℝ) := by
          rw [Finset.sum_mul, Finset.sum_div]
          exact Finset.sum_congr rfl (fun i _ => by ring)
  -- conclude
  have hbound : Filter.Tendsto
      (fun d : ℕ => (∑ i ∈ Finset.range N, |c i|) * 2 / (d:ℝ)) Filter.atTop (nhds 0) := by
    have h := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
      ((∑ i ∈ Finset.range N, |c i|) * 2)
    simpa [div_eq_mul_inv] using h
  have hzero : Filter.Tendsto (fun d : ℕ =>
      (∑ j ∈ Finset.Icc 1 d, stepFun a c N (m * (j:ℝ) / (d:ℝ))) / (d:ℝ)
        - (∑ i ∈ Finset.range N, c i * (a (i + 1) - a i)) / m) Filter.atTop (nhds 0) := by
    have hneg : Filter.Tendsto (fun d : ℕ => -((∑ i ∈ Finset.range N, |c i|) * 2 / (d:ℝ)))
        Filter.atTop (nhds 0) := by simpa using hbound.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hbound ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop 1] with d hd
      exact neg_le_of_abs_le (hmain d hd)
    · filter_upwards [Filter.eventually_ge_atTop 1] with d hd
      exact le_of_abs_le (hmain d hd)
  have := hzero.add_const ((∑ i ∈ Finset.range N, c i * (a (i + 1) - a i)) / m)
  simpa using this

end StepRiemann

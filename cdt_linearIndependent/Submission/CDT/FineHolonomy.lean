/-
# The denominator rate term `τ♭` of the fine holonomy bound

This module formalises the arithmetic ("denominator") rate term of Calegari–Dimitrov–Tang's
*Theorem `main:elementary form`* (the "fine holonomy bound" of the paper's §"The fine holonomy
bound", eq. `(taub)`).

For an `m × r` array `b = (b_{i,j})` of nonnegative reals whose every column has the *column shape*
of the paper
`0 = b₁ⱼ = ⋯ = b_{u_j, j} < b_{u_j+1, j} = ⋯ = b_{m,j} =: b_j`, `0 ≤ u_j ≤ m`,
and with row sums `σ_i = Σ_j b_{i,j}`, the paper defines

`τ♭(b) := (1/m²)·Σ_{i=1}^m (2i-1)·σ_i`,  and observes that

`τ♭(b) = σ_m − (1/m²)·Σ_j u_j²·b_j`,  with `0 ≤ τ♭(b) ≤ σ_m`.

Equivalently (the paper's display `(finitary rearrangement)`),

`τ♭(b) = Σ_{i=1}^m σ_i · ∫_{(i-1)/m}^{i/m} 2t dt`,

the "increasing rearrangement" reading of the weighted average: the weight `2t` is the cumulative
distribution function of `( [0,1], Lebesgue)`.

The second half of the module evaluates the *additive* rate term `τ♯` of the same theorem on the
paper's Example `ex:li11`, i.e. for the `[1,…,n][1,…,2n]` configuration with
`m = 4`, `Σe_i = max e_i = 1`:
`τ♯(e) = (2/m²)·min_{ξ∈[0,m]} { ξ·Σe_i + (max e_i)·I_ξ^m(ξ) } = 7/16`,
with the minimum attained on the whole interval `ξ ∈ [2,3]` — as the paper states.  We prove the
evaluation of the integrand (`integratedLcm_eval_two_three`) and the resulting upper bound for
`τ♯`.

## A correction of the paper

Example `ex:li11` displays `τ♭(b) = 37/16`, `τ♯(e) = 7/16` and then `τ(b;e) = 21/8 = 2.625`.  The
last number is *inconsistent* with the first two: `37/16 + 7/16 = 11/4 = 2.75`.  The value `21/8`
is the one computed in the *same* example for the cruder array `b₀` (which we verify as
`tauFlat_example_b0`).  Our formalisation records the two correct values.
-/
import Mathlib
import Submission.CDT.IntegratedLcm

open Finset MeasureTheory intervalIntegral
open scoped BigOperators
open Submission.CDT.IntegratedLcm

namespace Submission.CDT.FineHolonomy

/-- The `i`-th row sum `σ_i = Σ_j b_{i,j}` of the paper's array. -/
noncomputable def rowSum (r : ℕ) (b : ℕ → ℕ → ℝ) (i : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 r, b i j

/-- The paper's `τ♭`: the weighted average of the row sums with weights `(2i-1)/m²`. -/
noncomputable def tauFlat (m r : ℕ) (b : ℕ → ℕ → ℝ) : ℝ :=
  (1/(m:ℝ)^2) * ∑ i ∈ Finset.Icc 1 m, (2*(i:ℝ)-1) * rowSum r b i

/-- The sum of the first `n` odd numbers is `n²`. -/
theorem sum_odd_Icc (n : ℕ) : (∑ i ∈ Finset.Icc 1 n, (2*(i:ℝ)-1)) = (n:ℝ)^2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
    push_cast
    ring

/-- The tail form of `sum_odd_Icc`: `Σ_{i=k+1}^{m} (2i-1) = m² - k²` for `k ≤ m`. -/
theorem sum_odd_Icc_tail (m k : ℕ) (hk : k ≤ m) :
    (∑ i ∈ Finset.Icc (k+1) m, (2*(i:ℝ)-1)) = (m:ℝ)^2 - (k:ℝ)^2 := by
  have hdisj : Disjoint (Finset.Icc 1 k) (Finset.Icc (k+1) m) := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_Icc] at hi hi'
    omega
  have hsplit : Finset.Icc 1 m = Finset.Icc 1 k ∪ Finset.Icc (k+1) m := by
    ext i; simp only [Finset.mem_union, Finset.mem_Icc]; omega
  have h := Finset.sum_union (s₁ := Finset.Icc 1 k) (s₂ := Finset.Icc (k+1) m)
    (f := fun i => (2*(i:ℝ)-1)) hdisj
  rw [← hsplit] at h
  rw [sum_odd_Icc m, sum_odd_Icc k] at h
  linarith

/-- The paper's identity `(taub)`: for an array whose every column has the paper's *column shape*
`0 = b₁ⱼ = ⋯ = b_{u_j,j} < b_{u_j+1,j} = ⋯ = b_{m,j}` (encoded as
`b i j = if i ≤ u_j then 0 else b m j`, with `u_j ≤ m`), the weighted average of the row sums
equals `σ_m - (1/m²)·Σ_j u_j²·b_j`, where `σ_m = Σ_j b_{m,j} = Σ_j b_j`. -/
theorem tauFlat_eq (m r : ℕ) (hm : 0 < m) (b : ℕ → ℕ → ℝ) (u : ℕ → ℕ)
    (hu : ∀ j ∈ Finset.Icc 1 r, u j ≤ m)
    (hshape : ∀ i ∈ Finset.Icc 1 m, ∀ j ∈ Finset.Icc 1 r,
      b i j = if i ≤ u j then 0 else b m j) :
    tauFlat m r b
      = (∑ j ∈ Finset.Icc 1 r, b m j)
        - (1/(m:ℝ)^2) * ∑ j ∈ Finset.Icc 1 r, ((u j : ℝ))^2 * b m j := by
  have hinner : ∀ j ∈ Finset.Icc 1 r,
      (∑ i ∈ Finset.Icc 1 m, (2*(i:ℝ)-1) * b i j)
        = (m:ℝ)^2 * b m j - ((u j : ℝ))^2 * b m j := by
    intro j hj
    have hterm : ∀ i ∈ Finset.Icc 1 m,
        (2*(i:ℝ)-1) * b i j
          = if ¬ i ≤ u j then (2*(i:ℝ)-1) * b m j else 0 := by
      intro i hi
      rw [hshape i hi j hj]
      by_cases h : i ≤ u j <;> simp [h]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter,
      show (Finset.Icc 1 m).filter (fun i => ¬ i ≤ u j) = Finset.Icc (u j + 1) m from by
        ext i; simp only [Finset.mem_filter, Finset.mem_Icc]; omega,
      ← Finset.sum_mul, sum_odd_Icc_tail m (u j) (hu j hj)]
    ring
  have hmain : (∑ i ∈ Finset.Icc 1 m, (2*(i:ℝ)-1) * rowSum r b i)
      = (m:ℝ)^2 * (∑ j ∈ Finset.Icc 1 r, b m j)
        - ∑ j ∈ Finset.Icc 1 r, ((u j : ℝ))^2 * b m j := by
    have h1 : ∀ i ∈ Finset.Icc 1 m,
        (2*(i:ℝ)-1) * rowSum r b i = ∑ j ∈ Finset.Icc 1 r, (2*(i:ℝ)-1) * b i j := by
      intro i hi
      rw [rowSum, Finset.mul_sum]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_congr rfl hinner,
      Finset.sum_sub_distrib, Finset.mul_sum]
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  unfold tauFlat
  rw [hmain]
  field_simp

/-- `τ♭ ∈ [0, σ_m]` (the paper's "`\in [0,\sigma_m]`"), `σ_m = Σ_j b_j` being the `m`-th row sum. -/
theorem tauFlat_nonneg_le_rowSum (m r : ℕ) (hm : 0 < m) (b : ℕ → ℕ → ℝ)
    (u : ℕ → ℕ) (hu : ∀ j ∈ Finset.Icc 1 r, u j ≤ m)
    (hb : ∀ j ∈ Finset.Icc 1 r, 0 ≤ b m j)
    (hshape : ∀ i ∈ Finset.Icc 1 m, ∀ j ∈ Finset.Icc 1 r,
      b i j = if i ≤ u j then 0 else b m j) :
    0 ≤ tauFlat m r b ∧ tauFlat m r b ≤ rowSum r b m := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  rw [tauFlat_eq m r hm b u hu hshape, rowSum]
  constructor
  · rw [sub_nonneg]
    have hle : (∑ j ∈ Finset.Icc 1 r, ((u j : ℝ))^2 * b m j)
        ≤ (m:ℝ)^2 * ∑ j ∈ Finset.Icc 1 r, b m j := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have h1 : ((u j : ℝ))^2 ≤ (m:ℝ)^2 := by
        have h2 : (u j : ℝ) ≤ (m:ℝ) := by exact_mod_cast hu j hj
        have h0 : (0:ℝ) ≤ (u j : ℝ) := Nat.cast_nonneg _
        nlinarith
      exact mul_le_mul_of_nonneg_right h1 (hb j hj)
    calc (1/(m:ℝ)^2) * (∑ j ∈ Finset.Icc 1 r, ((u j : ℝ))^2 * b m j)
        ≤ (1/(m:ℝ)^2) * ((m:ℝ)^2 * ∑ j ∈ Finset.Icc 1 r, b m j) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = ∑ j ∈ Finset.Icc 1 r, b m j := by field_simp
  · have hnn : 0 ≤ (1/(m:ℝ)^2) * ∑ j ∈ Finset.Icc 1 r, ((u j : ℝ))^2 * b m j := by
      refine mul_nonneg (by positivity) (Finset.sum_nonneg fun j hj => ?_)
      exact mul_nonneg (by positivity) (hb j hj)
    linarith

/-- The paper's `(finitary rearrangement)` display: `τ♭` is the weighted sum of the row sums
against the distribution function `2t` of `[0,1]`, i.e.
`τ♭(b) = Σ_i σ_i · ∫_{(i-1)/m}^{i/m} 2t dt`. -/
theorem tauFlat_eq_integral (m r : ℕ) (b : ℕ → ℕ → ℝ) :
    tauFlat m r b
      = ∑ i ∈ Finset.Icc 1 m,
          rowSum r b i * (∫ t in ((i:ℝ)-1)/(m:ℝ)..((i:ℝ))/(m:ℝ), 2*t) := by
  have hInt : ∀ i : ℕ, (∫ t in ((i:ℝ)-1)/(m:ℝ)..((i:ℝ))/(m:ℝ), 2*t)
      = (2*(i:ℝ)-1)/(m:ℝ)^2 := by
    intro i
    rw [intervalIntegral.integral_const_mul, integral_id]
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun i _ => by rw [hInt i])]
  unfold tauFlat
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  ring


/-! ## The additive term `τ♯` on the paper's Example `ex:li11`

For the `[1,…,n][1,…,2n]` configuration of the paper's Example `ex:li11` one has `m = 4` and (with
`e = (0,0,1,0)`) `Σe_i = max e_i = 1`, so

`τ♯(e) = (2/16)·min_{ξ∈[0,4]} { ξ + I_ξ^4(ξ) }`.

The substance of the paper's computation is that the integrand is *constant* on `ξ ∈ [2,3]`: there
`I_ξ^4(ξ) = 7/2 - ξ`, whence the value `7/16`.  We prove the evaluation of `I_ξ^4(ξ)`
(`integratedLcm_two_three`) and the certified bound `τ♯(e) ≤ 7/16` (`tauSharp_example`). -/

theorem harmonicFun_eq_zero_of_le (ξ : ℝ) (h1 : 1 ≤ ξ) {t : ℝ} (ht : t ∈ Set.Icc 1 ξ) :
    harmonicFun ξ t = 0 := by
  have hξ : 0 < ξ := lt_of_lt_of_le zero_lt_one h1
  have hmax : max 1 ξ = ξ := max_eq_right h1
  have hfl : ⌊(t - 1) / max 1 ξ⌋₊ = 0 := by
    rw [hmax, Nat.floor_eq_zero, div_lt_one hξ]
    linarith [ht.2]
  simp [harmonicFun, hfl]

theorem harmonicFun_eq_one_of_ge (ξ : ℝ) (h2 : 2 ≤ ξ) {t : ℝ}
    (ht : t ∈ Set.Icc (ξ + 1) 4) : harmonicFun ξ t = 1 := by
  have hξ : 0 < ξ := by linarith
  have hmax : max 1 ξ = ξ := max_eq_right (by linarith)
  have hfl : ⌊(t - 1) / max 1 ξ⌋₊ = 1 := by
    rw [hmax]
    exact Nat.floor_eq_on_Ico 1 _ ⟨by rw [le_div_iff₀ hξ]; push_cast; linarith [ht.1],
      by rw [div_lt_iff₀ hξ]; push_cast; linarith [ht.2]⟩
  rw [harmonicFun, hfl, Finset.Icc_self, Finset.sum_singleton]
  norm_num

theorem correctionFun_eq_sub (ξ : ℝ) (h2 : 2 ≤ ξ) {t : ℝ} (h1 : ξ < t) (h2' : t < ξ + 1) :
    correctionFun ξ t = t - ξ := by
  have hξ : 0 < ξ := by linarith
  have hmax : max 1 ξ = ξ := max_eq_right (by linarith)
  have hmax0 : max 0 (ξ - 1) = ξ - 1 := max_eq_right (by linarith)
  have hfl : ⌊(t + max 0 (ξ - 1)) / max 1 ξ⌋₊ = 1 := by
    rw [hmax, hmax0]
    exact Nat.floor_eq_on_Ico 1 _ ⟨by rw [le_div_iff₀ hξ]; push_cast; linarith,
      by rw [div_lt_iff₀ hξ]; push_cast; linarith⟩
  rw [correctionFun, hfl]
  simp only [Nat.cast_one, div_one]
  rw [max_eq_left (by linarith : (0:ℝ) ≤ t - ξ)]

theorem correctionFun_eq_zero_of_ge (ξ : ℝ) (h2 : 2 ≤ ξ) {t : ℝ}
    (ht : t ∈ Set.Icc (ξ + 1) 4) : correctionFun ξ t = 0 := by
  have hξ : 0 < ξ := by linarith
  have hmax : max 1 ξ = ξ := max_eq_right (by linarith)
  have hmax0 : max 0 (ξ - 1) = ξ - 1 := max_eq_right (by linarith)
  have hfl : ⌊(t + max 0 (ξ - 1)) / max 1 ξ⌋₊ = 2 := by
    rw [hmax, hmax0]
    exact Nat.floor_eq_on_Ico 2 _ ⟨by rw [le_div_iff₀ hξ]; push_cast; linarith [ht.1],
      by rw [div_lt_iff₀ hξ]; push_cast; linarith [ht.2]⟩
  have hle : t / ((2:ℕ):ℝ) - ξ ≤ 0 := by
    have : t / ((2:ℕ):ℝ) ≤ ξ := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < ((2:ℕ):ℝ))]; push_cast; linarith [ht.2]
    linarith
  rw [correctionFun, hfl, max_eq_right hle]

theorem intervalIntegrable_correctionFun' (w a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (correctionFun w) volume a b := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hab]
  exact (integrableOn_correctionFun w b).mono_set
    (fun t ht => ⟨lt_of_le_of_lt ha ht.1, ht.2⟩)

theorem intervalIntegrable_harmonicFun' (w a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (harmonicFun w) volume a b := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hab]
  exact (integrableOn_harmonicFun w b).mono_set
    (fun t ht => ⟨lt_of_le_of_lt ha ht.1, ht.2⟩)

theorem integral_correctionFun_two_three (ξ : ℝ) (h2 : 2 ≤ ξ) (h3 : ξ ≤ 3) :
    (∫ t in ξ..4, correctionFun ξ t) = 1/2 := by
  have h4 : ξ + 1 ≤ 4 := by linarith
  have h1ξ : (1:ℝ) ≤ ξ := by linarith
  have hic1 : IntervalIntegrable (correctionFun ξ) volume ξ (ξ + 1) :=
    intervalIntegrable_correctionFun' ξ ξ (ξ + 1) h1ξ (by linarith)
  have hic2 : IntervalIntegrable (correctionFun ξ) volume (ξ + 1) 4 :=
    intervalIntegrable_correctionFun' ξ (ξ + 1) 4 (by linarith) h4
  have hsplit := integral_add_adjacent_intervals hic1 hic2
  have hsub : {t : ℝ | ¬ (t ∈ Set.uIoc ξ (ξ + 1) → correctionFun ξ t = t - ξ)} ⊆ {ξ + 1} := by
    intro t ht
    have h' : t ∈ Set.uIoc ξ (ξ + 1) ∧ correctionFun ξ t ≠ t - ξ := Classical.not_imp.mp ht
    rw [Set.uIoc_of_le (by linarith : ξ ≤ ξ + 1)] at h'
    simp only [Set.mem_singleton_iff]
    by_contra hne
    exact h'.2 (correctionFun_eq_sub ξ h2 h'.1.1 (lt_of_le_of_ne h'.1.2 hne))
  have hae : ∀ᵐ t ∂volume, t ∈ Set.uIoc ξ (ξ + 1) → correctionFun ξ t = t - ξ := by
    rw [MeasureTheory.ae_iff]
    exact measure_mono_null hsub (measure_singleton (ξ + 1))
  have h1 : (∫ t in ξ..(ξ + 1), correctionFun ξ t) = 1/2 := by
    rw [intervalIntegral.integral_congr_ae hae,
      intervalIntegral.integral_sub intervalIntegrable_id intervalIntegrable_const,
      integral_id, intervalIntegral.integral_const]
    simp
    ring
  have hzero : (∫ t in (ξ + 1)..4, correctionFun ξ t) = 0 := by
    have hEq : Set.EqOn (correctionFun ξ) (fun _ => (0:ℝ)) (Set.uIcc (ξ + 1) 4) := by
      intro t ht
      rw [Set.uIcc_of_le h4] at ht
      exact correctionFun_eq_zero_of_ge ξ h2 ht
    rw [intervalIntegral.integral_congr hEq]
    simp
  rw [hzero] at hsplit
  linarith

theorem integral_harmonicFun_two_three (ξ : ℝ) (h2 : 2 ≤ ξ) (h3 : ξ ≤ 3) :
    (∫ t in ξ..4, harmonicFun ξ t) = 3 - ξ := by
  have h1ξ : (1:ℝ) ≤ ξ := by linarith
  have h10 : (∫ t in 1..ξ, harmonicFun ξ t) = 0 := by
    have hEq : Set.EqOn (harmonicFun ξ) (fun _ => (0:ℝ)) (Set.uIcc 1 ξ) := by
      intro t ht
      rw [Set.uIcc_of_le h1ξ] at ht
      exact harmonicFun_eq_zero_of_le ξ h1ξ ht
    rw [intervalIntegral.integral_congr hEq]
    simp
  have h14 : (∫ t in 1..4, harmonicFun ξ t) = 3 - ξ := by
    rw [integral_harmonicFun 4 ξ (by norm_num)]
    have hξ : 0 < ξ := by linarith
    have hmax : max 1 ξ = ξ := max_eq_right h1ξ
    have hfl : ⌊((4:ℝ) - 1) / max 1 ξ⌋₊ = 1 := by
      rw [hmax]
      exact Nat.floor_eq_on_Ico 1 _ ⟨by rw [le_div_iff₀ hξ]; push_cast; linarith,
        by rw [div_lt_iff₀ hξ]; push_cast; linarith⟩
    rw [hfl, Finset.Icc_self, Finset.sum_singleton, hmax]
    simp only [Nat.cast_one, one_div, one_mul, inv_one]
    rw [max_eq_right (by linarith : (1:ℝ) ≤ 1 + ξ),
      max_eq_left (by linarith : (0:ℝ) ≤ 4 - (1 + ξ))]
    ring
  have hadj := integral_add_adjacent_intervals
    (intervalIntegrable_harmonicFun' ξ 1 ξ (by norm_num) h1ξ)
    (intervalIntegrable_harmonicFun' ξ ξ 4 h1ξ (by linarith))
  rw [h10, h14] at hadj
  linarith

/-- The paper's Example `ex:li11` computation: for every `ξ ∈ [2,3]`,
`I_ξ^4(ξ) = 7/2 - ξ`; hence `ξ·Σe + (max e)·I_ξ^4(ξ) = 7/2` for `Σe = max e = 1`, the constancy
that makes `[2,3]` the minimising interval of `τ♯`. -/
theorem integratedLcm_two_three (ξ : ℝ) (h2 : 2 ≤ ξ) (h3 : ξ ≤ 3) :
    integratedLcm ξ 4 ξ = 7/2 - ξ := by
  have hmin : min ξ 1 = 1 := min_eq_right (by linarith)
  have hmax : max ξ 1 = ξ := max_eq_left (by linarith)
  have hfirst : (∫ t in min ξ 1..1, max (t - ξ) 0) = 0 := by
    rw [hmin, intervalIntegral.integral_same]
  rw [integratedLcm, hfirst, hmax,
    integral_harmonicFun_two_three ξ h2 h3, integral_correctionFun_two_three ξ h2 h3]
  ring

/-- `0 ≤ I_u^v(w)` whenever `max u 1 ≤ v` (the three integrands are nonnegative and the intervals
are correctly oriented). -/
theorem integratedLcm_nonneg (u v w : ℝ) (h : max u 1 ≤ v) :
    0 ≤ integratedLcm u v w := by
  have h1 : min u 1 ≤ 1 := min_le_right _ _
  have h2 : max u 1 ≤ v := h
  have hA : 0 ≤ ∫ t in min u 1..1, max (t - w) 0 :=
    intervalIntegral.integral_nonneg h1 fun t _ => le_max_right _ _
  have hB : 0 ≤ ∫ t in max u 1..v, harmonicFun w t :=
    intervalIntegral.integral_nonneg h2 fun t _ => harmonicFun_nonneg w t
  have hC : 0 ≤ ∫ t in max u 1..v, correctionFun w t :=
    intervalIntegral.integral_nonneg h2 fun t _ => correctionFun_nonneg w t
  rw [integratedLcm]
  linarith

/-- The paper's additive rate term `τ♯(e) = (2/m²)·min_{ξ∈[0,m]}{ ξ·Σe_i + (max e_i)·I_ξ^m(ξ) }`
of Theorem `main:elementary form`, as an infimum over `ξ ∈ [0,m]`. -/
noncomputable def tauSharp (m : ℕ) (esum emax : ℝ) : ℝ :=
  (2/(m:ℝ)^2) * sInf ((fun ξ : ℝ => ξ * esum + emax *
    integratedLcm ξ m ξ) '' Set.Icc 0 m)

/-- A nonnegative function with nonempty domain has nonnegative infimum. -/
theorem le_sInf_image {f : ℝ → ℝ} {s : Set ℝ} (hs : s.Nonempty) (hf : ∀ x ∈ s, 0 ≤ f x) :
    0 ≤ sInf (f '' s) := by
  refine le_csInf (hs.image f) ?_
  rintro y ⟨x, hx, rfl⟩
  exact hf x hx

/-- The image of a bounded set of nonnegative values is bounded below. -/
theorem bddBelow_image_of_nonneg {f : ℝ → ℝ} {s : Set ℝ} (hf : ∀ x ∈ s, 0 ≤ f x) :
    BddBelow (f '' s) :=
  ⟨0, fun y hy => by rcases hy with ⟨x, hx, rfl⟩; exact hf x hx⟩

/-- `τ♯ ≥ 0` for nonnegative `e`. -/
theorem tauSharp_nonneg (m : ℕ) (hm : 0 < m) {esum emax : ℝ} (he : 0 ≤ esum)
    (hem : 0 ≤ emax) : 0 ≤ tauSharp m esum emax := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  rw [tauSharp]
  refine mul_nonneg (by positivity) (le_sInf_image ?_ ?_)
  · exact ⟨0, le_refl 0, hm0.le⟩
  · intro ξ hξ
    exact add_nonneg (mul_nonneg hξ.1 he)
      (mul_nonneg hem (integratedLcm_nonneg ξ (m:ℝ) ξ
        (max_le hξ.2 (by exact_mod_cast hm : (1:ℝ) ≤ (m:ℝ)))))

/-- **Example `ex:li11`**: for the `[1,…,n][1,…,2n]` configuration with `m = 4`,
`Σe_i = max e_i = 1`, the paper's additive term satisfies `τ♯ ≤ 7/16`, as certified by the
minimising interval `ξ ∈ [2,3]`. -/
theorem tauSharp_le_example : tauSharp 4 1 1 ≤ 7/16 := by
  have hmem : (3:ℝ) ∈ Set.Icc (0:ℝ) 4 := ⟨by norm_num, by norm_num⟩
  have hf3 : (fun ξ : ℝ => ξ * 1 + 1 * integratedLcm ξ 4 ξ) 3 = 7/2 := by
    show (3:ℝ) * 1 + 1 * integratedLcm 3 4 3 = 7/2
    rw [integratedLcm_two_three 3 (by norm_num) (by norm_num)]
    ring
  have hbdd : BddBelow ((fun ξ : ℝ => ξ * 1 + 1 * integratedLcm ξ 4 ξ) '' Set.Icc (0:ℝ) 4) :=
    bddBelow_image_of_nonneg (fun ξ hξ =>
      add_nonneg (mul_nonneg hξ.1 zero_le_one)
        (mul_nonneg zero_le_one
          (integratedLcm_nonneg ξ 4 ξ (max_le hξ.2 (by norm_num : (1:ℝ) ≤ 4)))))
  rw [tauSharp]
  have hval : sInf ((fun ξ : ℝ => ξ * 1 + 1 * integratedLcm ξ 4 ξ) '' Set.Icc (0:ℝ) 4) ≤ 7/2 := by
    rw [← hf3]
    exact csInf_le hbdd (Set.mem_image_of_mem _ hmem)
  calc (2/(4:ℝ)^2) * sInf ((fun ξ : ℝ => ξ * 1 + 1 *
        integratedLcm ξ 4 ξ) '' Set.Icc (0:ℝ) 4)
      ≤ (2/(4:ℝ)^2) * (7/2) := mul_le_mul_of_nonneg_left hval (by norm_num)
    _ = 7/16 := by norm_num

end Submission.CDT.FineHolonomy

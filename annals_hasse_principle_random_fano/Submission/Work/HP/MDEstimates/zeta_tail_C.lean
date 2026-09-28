import Mathlib
import Submission.Work.HP.MDEstimates.moebius_multiples_sum
import Submission.Work.HP.MDEstimates.moebius_zeta_tsum_mul
import Submission.Work.HP.MDEstimates.pSeries_tail_tsum_le

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.MDEstimates

/-!
# The Möbius/zeta tail bound `|∑_{ℓ ≤ X} μ(ℓ)/ℓ^s - 1/ζ(s)| ≤ C X^{1-s}`

We prove that for `s > 1` the partial sums of the Dirichlet series `∑ μ(n)/n^s` converge to
`1/ζ(s)` with an error `O(X^{1-s})`, where `ζ(s) = ∑' k, 1/((k:ℝ)+1)^s`.

The two analytic inputs are:

* `moebius_zeta_tsum_mul` : `(∑_{n≥1} μ(n)/n^s) · (∑_{n≥1} 1/n^s) = 1` (the Euler-product /
  Dirichlet-convolution identity), which identifies the limit as `1/ζ(s)`;
* `pSeries_tail_tsum_le` : the integral-test bound `∑_{j≥0} 1/(j+N+1)^s ≤ N^{1-s}/(s-1)`.

The error estimate itself is then immediate from absolute convergence: the tail of the Möbius
series is dominated term by term by the tail of the (positive) `ζ`-series.
-/

/-- The `ζ`-series term `1/(k+1)^s`. -/
def zt (s : ℝ) (k : ℕ) : ℝ := 1 / ((k + 1 : ℕ) : ℝ) ^ s

/-- The Möbius-series term `μ(k+1)/(k+1)^s`. -/
def mob (s : ℝ) (k : ℕ) : ℝ := (ArithmeticFunction.moebius (k + 1) : ℝ) / ((k + 1 : ℕ) : ℝ) ^ s

lemma zt_summable (s : ℝ) (hs : 1 < s) : Summable (zt s) := by
  have h : Summable (fun k : ℕ => 1 / |(k : ℝ) + 1| ^ s) :=
    (Real.summable_one_div_nat_add_rpow 1 s).mpr hs
  refine h.congr (fun k => ?_)
  rw [zt, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
  push_cast
  ring_nf

/-- The Möbius function cast to `ℝ` is bounded by `1` in absolute value. -/
lemma moebius_abs_cast_le_one (n : ℕ) : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

lemma mob_summable (s : ℝ) (hs : 1 < s) : Summable (mob s) := by
  refine Summable.of_norm_bounded (f := mob s) (g := zt s) (zt_summable s hs) (fun k => ?_)
  have hpos : (0 : ℝ) < (((k + 1 : ℕ)) : ℝ) ^ s := Real.rpow_pos_of_pos (by positivity) s
  rw [Real.norm_eq_abs, mob, zt, abs_div, abs_of_pos hpos, div_le_div_iff_of_pos_right hpos]
  exact moebius_abs_cast_le_one (k + 1)

lemma zt_tsum_pos (s : ℝ) (hs : 1 < s) : 0 < ∑' k : ℕ, zt s k := by
  refine Summable.tsum_pos (zt_summable s hs) (fun i => ?_) 0 ?_
  · rw [zt]; positivity
  · rw [zt]; norm_num

lemma mob_tsum_eq (s : ℝ) :
    (∑' k : ℕ, mob s k) = ∑' n : ℕ+, (ArithmeticFunction.moebius (n : ℕ) : ℝ) / ((n : ℕ) : ℝ) ^ s := by
  have h : (∑' k : ℕ, mob s k)
      = ∑' k : ℕ, (fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ s) (k + 1) := by
    refine tsum_congr (fun k => ?_)
    rfl
  rw [h]
  exact (tsum_pnat_eq_tsum_succ (f := fun n : ℕ => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) ^ s)).symm

lemma zt_tsum_eq (s : ℝ) : (∑' k : ℕ, zt s k) = ∑' n : ℕ+, 1 / ((n : ℕ) : ℝ) ^ s := by
  have h : (∑' k : ℕ, zt s k) = ∑' k : ℕ, (fun n : ℕ => 1 / (n : ℝ) ^ s) (k + 1) := by
    refine tsum_congr (fun k => ?_)
    rfl
  rw [h]
  exact (tsum_pnat_eq_tsum_succ (f := fun n : ℕ => 1 / (n : ℝ) ^ s)).symm

lemma zt_tsum_form (s : ℝ) :
    (∑' k : ℕ, zt s k) = ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ s := by
  refine tsum_congr (fun k => ?_)
  rw [zt]
  push_cast
  ring_nf

/-- Partial sums over `Icc 1 N` rewritten as sums over `range N` of the shifted term. -/
lemma sum_Icc_eq_sum_range_mob (s : ℝ) (N : ℕ) :
    (∑ ℓ ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ s)
      = ∑ i ∈ range N, mob s i := by
  rw [← Finset.Ico_succ_right_eq_Icc (1 : ℕ) N]
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr
  · simp
  · intro k _
    rw [mob]
    push_cast
    ring_nf

theorem zeta_tail_C (s : ℝ) (hs : 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 1 ≤ X →
      |(∑ ℓ ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ s) -
        1 / (∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ s)| ≤ C / X ^ (s - 1) := by
  have hspos : 0 < s - 1 := by linarith
  refine ⟨(2 : ℝ) ^ (s - 1) / (s - 1), by positivity, ?_⟩
  intro X hX
  set N := ⌊X⌋₊ with hN
  have hXpos : 0 < X := by linarith
  have hVsum : Summable (mob s) := mob_summable s hs
  -- floor estimates
  have hN1 : 1 ≤ N := by
    rw [hN]
    exact Nat.le_floor (by simpa using hX)
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hN1
  have hN2 : X / 2 ≤ (N : ℝ) := by
    by_cases hX2 : (2 : ℝ) ≤ X
    · have h1 : X - 1 < (N : ℝ) := by
        rw [hN]
        have := Nat.lt_floor_add_one X
        linarith
      have h2 : X / 2 ≤ X - 1 := by linarith
      linarith
    · have h1 : X < 2 := not_le.mp hX2
      have h2 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
      have : X / 2 < 1 := by linarith
      linarith
  -- the limit value `V`
  have hTpos : 0 < (∑' k : ℕ, zt s k) := zt_tsum_pos s hs
  have hVT : (∑' k : ℕ, mob s k) * (∑' k : ℕ, zt s k) = 1 := by
    rw [mob_tsum_eq, zt_tsum_eq]
    exact moebius_zeta_tsum_mul s hs
  have hVeq : (∑' k : ℕ, mob s k) = 1 / (∑' k : ℕ, zt s k) := by
    rw [eq_div_iff (ne_of_gt hTpos)]
    exact hVT
  -- the tail bound
  have hkey : |(∑ i ∈ range N, mob s i) - (∑' k : ℕ, mob s k)| ≤ (N : ℝ) ^ (1 - s) / (s - 1) := by
    have htail : (∑' i : ℕ, mob s (i + N)) = (∑' k : ℕ, mob s k) - ∑ i ∈ range N, mob s i := by
      have h := Summable.sum_add_tsum_nat_add (f := mob s) N hVsum
      linarith
    have hbound : |∑' i : ℕ, mob s (i + N)| ≤ (N : ℝ) ^ (1 - s) / (s - 1) := by
      have hsum : Summable (fun i : ℕ => mob s (i + N)) :=
        (summable_nat_add_iff N).mpr hVsum
      have hnorms : Summable (fun i : ℕ => ‖mob s (i + N)‖) := hsum.norm
      have hupd : Summable (fun j : ℕ => 1 / ((j + N + 1 : ℕ) : ℝ) ^ s) := by
        have h : Summable (fun n : ℕ => 1 / |(n : ℝ) + (N + 1)| ^ s) :=
          (Real.summable_one_div_nat_add_rpow (N + 1) s).mpr hs
        refine h.congr (fun n => ?_)
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + (N + 1))]
        push_cast
        ring_nf
      have hle : ∀ i : ℕ, ‖mob s (i + N)‖ ≤ 1 / ((i + N + 1 : ℕ) : ℝ) ^ s := by
        intro i
        have hpos : (0 : ℝ) < (((i + N + 1 : ℕ)) : ℝ) ^ s := Real.rpow_pos_of_pos (by positivity) s
        rw [Real.norm_eq_abs, mob, abs_div, abs_of_pos hpos, div_le_div_iff_of_pos_right hpos]
        exact moebius_abs_cast_le_one (i + N + 1)
      have h2 : ∑' i : ℕ, ‖mob s (i + N)‖
          ≤ ∑' j : ℕ, 1 / ((j + N + 1 : ℕ) : ℝ) ^ s :=
        Summable.tsum_le_tsum hle hnorms hupd
      have h1 : ‖∑' i : ℕ, mob s (i + N)‖ ≤ ∑' i : ℕ, ‖mob s (i + N)‖ :=
        norm_tsum_le_tsum_norm hnorms
      rw [Real.norm_eq_abs] at h1
      exact le_trans h1 (le_trans h2 (pSeries_tail_tsum_le s hs N hN1))
    rw [show (∑ i ∈ range N, mob s i) - (∑' k : ℕ, mob s k)
          = -(∑' i : ℕ, mob s (i + N)) by rw [htail]; ring, abs_neg]
    exact hbound
  -- final comparison
  have hfinal : (N : ℝ) ^ (1 - s) / (s - 1) ≤ (2 : ℝ) ^ (s - 1) / (s - 1) / X ^ (s - 1) := by
    have h1 : (N : ℝ) ^ (1 - s) ≤ (X / 2) ^ (1 - s) :=
      Real.rpow_le_rpow_of_nonpos (by linarith : 0 < X / 2) hN2 (by linarith : 1 - s ≤ 0)
    have h2 : (X / 2) ^ (1 - s) = X ^ (1 - s) * 2 ^ (s - 1) := by
      rw [Real.div_rpow (le_of_lt hXpos) (by norm_num) (1 - s), div_eq_mul_inv,
        ← Real.rpow_neg (show (0 : ℝ) ≤ 2 by norm_num) (1 - s), show -(1 - s) = s - 1 by ring]
    have h3 : X ^ (1 - s) = 1 / X ^ (s - 1) := by
      rw [one_div, ← Real.rpow_neg (le_of_lt hXpos) (s - 1), show -(s - 1) = 1 - s by ring]
    rw [h2] at h1
    have h4 : (N : ℝ) ^ (1 - s) / (s - 1) ≤ (X ^ (1 - s) * 2 ^ (s - 1)) / (s - 1) :=
      div_le_div_of_nonneg_right h1 (le_of_lt hspos)
    refine le_trans h4 (le_of_eq ?_)
    rw [h3]
    ring
  have hS : (∑ ℓ ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.moebius ℓ : ℝ) / (ℓ : ℝ) ^ s)
      = ∑ i ∈ range N, mob s i := sum_Icc_eq_sum_range_mob s N
  rw [hS, ← zt_tsum_form, ← hVeq]
  exact le_trans hkey hfinal

end Work.HP.MDEstimates

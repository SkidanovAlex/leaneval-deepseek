/-
# `Submission.Work.FITop4.Red5.sieve_inner_le_pieces_ref`

The `|μ|`-sharpened companion of `sieve_inner_le_pieces_zint`: the sieve inner sum is bounded by

* `T1`, the cell-coefficient sums `∑_{i,k} ∑_{|w|²=m} ‖∑_{z} β^{ik}_z Z(Re wz)‖`;
* `T2`, the sharp second error term
  `∑_{i,k} ∑_{|w|²=m} ∑_{z} 2·badInd(|z|²)·‖β^{ik}_z Z(Re wz)‖`;
* `T3`, the radial-defect term
  `∑_{|w|²=m} ∑_{z} cGInd(|z|²)·(1 - ∑_i p_i(|z|²))·|μ(|z|²)|·τ(|z|²)·Z(Re wz)`,

where `cGInd` is the indicator of the five sieve conditions and the factor `|μ(|z|²)|` is kept
explicitly (rather than discarded through `|μ| ≤ 1`).  This is the termwise-sharp majorant of the
radial defect sum and the natural statement used downstream.
-/
import Mathlib
import Submission.Work.FITop4.Red5.sieve_inner_le_pieces_zint
import Submission.Work.FITop4.Red5.piecesSetup

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The third term: the `|μ|`-weighted majorant of the radial defect -/

/-- **The `|μ|`-weighted bound of the radial-defect sum.**  For a nonnegative radial weight
`η(n) = 1 - ∑_i p_i(n)` on the annulus, the absolute value of the weighted Gaussian sum
`∑_{|w|²=m} ∑_z η(|z|²) μ(|z|²) γ(|z|²;C) Z(Re wz)` is dominated by the explicit double sum
`∑_{|w|²=m} ∑_z cGInd(|z|²) η(|z|²) |μ(|z|²)| τ(|z|²) Z(Re wz)`: termwise on the support `cGPred`
one uses `|γ| ≤ τ`, and off it the summand vanishes. -/
lemma zint_third_bound_ref {m x N Pz : ℕ} {C τ : ℝ} {K : ℕ} {p : Fin K → ℝ → ℝ}
    (hweight : ∀ z ∈ primAnn (2 * N), 0 ≤ 1 - ∑ i, p i ((Work.FIPlan.gnorm z : ℕ) : ℝ)) :
    |∑ w ∈ wSph m, innerSum m N x Pz C τ (fun n => 1 - ∑ i, p i n) w|
      ≤ ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
          cGInd m N x Pz τ (Work.FIPlan.gnorm z)
            * (1 - ∑ i, p i ((Work.FIPlan.gnorm z : ℕ) : ℝ))
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by
  simp only [innerSum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum (fun w _ => ?_)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum (fun z hz => ?_)
  have hη : 0 ≤ 1 - ∑ i, p i ((Work.FIPlan.gnorm z : ℕ) : ℝ) := hweight z hz
  have hZ : 0 ≤ (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := Zint_nonneg _
  have hmg : |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)
      * Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z)|
      ≤ |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
        * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (Work.FITop3.abs_gammaTrunc_le C _) (abs_nonneg _)
  by_cases hc : cGPred m N x Pz τ (Work.FIPlan.gnorm z)
  · rw [if_pos hc, cGInd, if_pos hc]
    calc |(1 - ∑ i, p i ((Work.FIPlan.gnorm z : ℕ) : ℝ)) * zFactor C w z|
        = (1 - ∑ i, p i ((Work.FIPlan.gnorm z : ℕ) : ℝ))
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)
                * Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z)|
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by
          rw [zFactor, abs_mul, abs_of_nonneg hη, abs_mul, abs_of_nonneg hZ]; ring
      _ ≤ (1 - ∑ i, p i ((Work.FIPlan.gnorm z : ℕ) : ℝ))
            * (|(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
              * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ))
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmg hη) hZ
      _ = 1 * (1 - ∑ i, p i ((Work.FIPlan.gnorm z : ℕ) : ℝ))
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by ring
  · rw [if_neg hc, abs_zero, cGInd, if_neg hc]
    simp

/-! ## The main theorem -/

theorem sieve_inner_le_pieces_ref
    (m x N Pz : ℕ) (C τ θ : ℝ) (K K' : ℕ)
    (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
    (Pa : Fin K → Fin K' → Work.FITop.Params)
    (hm : 1 ≤ m) (hN : 1 ≤ N) (hP2 : 2 ≤ Pz) (ha : ∀ i, (N : ℝ) ≤ a i)
    (hPaN : ∀ i k, (Pa i k).N = a i)
    (hPaC : ∀ i k, (Pa i k).C = C)
    (hPaPz : ∀ i k, (Pa i k).Pz = Pz)
    (hPaθ : ∀ i k, (Pa i k).θ = θ)
    (hPatau : ∀ (i : Fin K) (k : Fin K') n, n ≤ 2 * N → (((n.divisors.card : ℕ) : ℝ) ≤ τ) →
        (((n.divisors.card : ℕ) : ℝ) ≤ (Pa i k).τ))
    (hp0 : ∀ i u, 0 ≤ p i u) (hp1 : ∀ i u, p i u ≤ 1)
    (hpsup : ∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i)
    (hq0 : ∀ k α, 0 ≤ q k α) (hq0z : ∀ k, q k 0 = 0)
    (hqsup : ∀ k α, q k α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ)
    (hang : ∀ α, -Real.pi ≤ α → α ≤ Real.pi → (∑ k, q k (α - φ k)) = 1)
    (hpsum : ∀ u, (N : ℝ) < u → u ≤ 2 * (N : ℝ) → (∑ i, p i u) ≤ 1) :
    |∑ n ∈ Finset.Icc 1 (2 * N),
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0)|
      ≤ (∑ i, ∑ k, ∑ w ∈ wSph m,
            ‖∑ z ∈ primAnn (2 * N),
              pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
        + (∑ i, ∑ k, ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
            2 * badInd m x τ (Work.FIPlan.gnorm z)
              * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
        + (∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
            cGInd m N x Pz τ (Work.FIPlan.gnorm z)
              * (1 - ∑ i, p i (Work.FIPlan.gnorm z))
              * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
              * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
              * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) := by
  classical
  set LS : ℝ := ∑ n ∈ Finset.Icc 1 (2 * N),
      (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
        then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
          * Work.FITop.atilFIa (m * n) else 0) with hLSdef
  set T1 : ℝ := ∑ i, ∑ k, ∑ w ∈ wSph m,
      ‖∑ z ∈ primAnn (2 * N), pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖
    with hT1def
  set T2 : ℝ := ∑ i, ∑ k, ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
      2 * badInd m x τ (Work.FIPlan.gnorm z)
        * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ with hT2def
  set T3 : ℝ := ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
      cGInd m N x Pz τ (Work.FIPlan.gnorm z)
        * (1 - ∑ i, p i (Work.FIPlan.gnorm z))
        * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
        * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
        * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) with hT3def
  let H : PieceHyp m x N Pz C τ θ a p φ q Pa :=
    { ha := ha, hPaN := hPaN, hPaC := hPaC, hPaPz := hPaPz, hPaθ := hPaθ, hPatau := hPatau,
      hp0 := hp0, hpsup := hpsup, hq0 := hq0, hq0z := hq0z, hqsup := hqsup, hang := hang }
  -- the radial defect is nonnegative on the annulus
  have hweight : ∀ z ∈ primAnn (2 * N), 0 ≤ 1 - ∑ i, p i ((Work.FIPlan.gnorm z : ℕ) : ℝ) :=
    fun z hz => one_sub_sum_p_nonneg ha hpsup hpsum hz
  by_cases hsf : Squarefree m
  · -- ## the squarefree case
    have hLS : LS = ∑ w ∈ wSph m, innerSum m N x Pz C τ (fun _ => 1) w := by
      rw [hLSdef]
      have h1 : (∑ n ∈ Finset.Icc 1 (2 * N),
            (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
              then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                * Work.FITop.atilFIa (m * n) else 0))
          = ∑ n ∈ Finset.Icc 1 (2 * N),
              (1 : ℝ) * (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
                then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
                  * Work.FITop.atilFIa (m * n) else 0) := by
        apply Finset.sum_congr rfl
        intro n _
        by_cases h : N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
        · rw [if_pos h, one_mul]
        · rw [if_neg h, mul_zero]
      rw [h1, weighted_gauss_identity (η := fun _ => 1) m x N Pz C τ hm hN hP2 hsf]
      apply Finset.sum_congr rfl
      intro w _
      rw [innerSum]
      apply Finset.sum_congr rfl
      intro z _
      by_cases h : cGPred m N x Pz τ (Work.FIPlan.gnorm z)
      · rw [if_pos ((cGPred_iff' m N x Pz τ _).mpr h), if_pos h]
        rw [zFactor]; ring
      · rw [if_neg (fun hc => h ((cGPred_iff' m N x Pz τ _).mp hc)), if_neg h]
    -- the radial partition `1 = ∑_i p_i + (1 - ∑_i p_i)`
    have hsplit : (∑ w ∈ wSph m, innerSum m N x Pz C τ (fun _ => 1) w)
        = (∑ w ∈ wSph m, innerSum m N x Pz C τ (fun n => ∑ i, p i n) w)
          + ∑ w ∈ wSph m, innerSum m N x Pz C τ (fun n => 1 - ∑ i, p i n) w := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w _
      calc innerSum m N x Pz C τ (fun _ => 1) w
          = innerSum m N x Pz C τ (fun n => (∑ i, p i n) + (1 - ∑ i, p i n)) w :=
            innerSum_congr m N x Pz C τ (fun n => by ring) w
        _ = innerSum m N x Pz C τ (fun n => ∑ i, p i n) w
              + innerSum m N x Pz C τ (fun n => 1 - ∑ i, p i n) w :=
            (innerSum_add m N x Pz C τ (fun n => ∑ i, p i n)
              (fun n => 1 - ∑ i, p i n) w).symm
    -- the matched part
    have hA : |∑ w ∈ wSph m, innerSum m N x Pz C τ (fun n => ∑ i, p i n) w| ≤ T1 + T2 := by
      have e1 : (∑ w ∈ wSph m, ∑ i, ∑ k, ‖∑ z ∈ primAnn (2 * N),
            pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖) = T1 :=
        (sum_swap_kw (wSph m) (fun w i k => ‖∑ z ∈ primAnn (2 * N),
            pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)).symm.trans
          hT1def.symm
      have e2 : (∑ w ∈ wSph m, ∑ i, ∑ k, ∑ z ∈ primAnn (2 * N),
            2 * badInd m x τ (Work.FIPlan.gnorm z)
              * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖) = T2 :=
        (sum_swap_kw (wSph m) (fun w i k => ∑ z ∈ primAnn (2 * N),
            2 * badInd m x τ (Work.FIPlan.gnorm z)
              * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)).symm.trans
          hT2def.symm
      rw [← e1, ← e2]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum (fun w _ => per_w_bound_zint H w)) ?_
      rw [Finset.sum_add_distrib]
    -- the third term
    have hB : |∑ w ∈ wSph m, innerSum m N x Pz C τ (fun n => 1 - ∑ i, p i n) w| ≤ T3 :=
      (zint_third_bound_ref hweight).trans (le_of_eq hT3def.symm)
    rw [hLS, hsplit]
    have hbc : |(∑ w ∈ wSph m, innerSum m N x Pz C τ (fun n => ∑ i, p i n) w)
            + ∑ w ∈ wSph m, innerSum m N x Pz C τ (fun n => 1 - ∑ i, p i n) w|
        ≤ (T1 + T2) + T3 := by
      have h1 := abs_add_le (∑ w ∈ wSph m, innerSum m N x Pz C τ (fun n => ∑ i, p i n) w)
        (∑ w ∈ wSph m, innerSum m N x Pz C τ (fun n => 1 - ∑ i, p i n) w)
      linarith [h1, hA, hB]
    calc |(∑ w ∈ wSph m, innerSum m N x Pz C τ (fun n => ∑ i, p i n) w)
            + ∑ w ∈ wSph m, innerSum m N x Pz C τ (fun n => 1 - ∑ i, p i n) w|
        ≤ (T1 + T2) + T3 := hbc
      _ = T1 + T2 + T3 := by ring
  · -- ## `m` not squarefree: the left-hand side vanishes
    have hLS0 : LS = 0 := by
      rw [hLSdef]
      apply Finset.sum_eq_zero
      intro n _
      by_cases h : N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
      · rw [if_pos h]
        have hns : ¬ Squarefree (m * n) := fun hs => hsf (Squarefree.of_mul_left hs)
        rw [atilFIa_eq, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]
        ring
      · rw [if_neg h]
    have h1 : 0 ≤ T1 := by
      rw [hT1def]
      apply Finset.sum_nonneg; intro i _
      apply Finset.sum_nonneg; intro k _
      apply Finset.sum_nonneg; intro w _
      exact norm_nonneg _
    have h2 : 0 ≤ T2 := by
      rw [hT2def]
      apply Finset.sum_nonneg; intro i _
      apply Finset.sum_nonneg; intro k _
      apply Finset.sum_nonneg; intro w _
      apply Finset.sum_nonneg; intro z _
      exact mul_nonneg (mul_nonneg (by norm_num) (badInd_nonneg m x τ (Work.FIPlan.gnorm z)))
        (norm_nonneg _)
    have h3 : 0 ≤ T3 := by
      rw [hT3def]
      apply Finset.sum_nonneg; intro w _
      apply Finset.sum_nonneg; intro z hz
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (cGInd_nonneg m N x Pz τ (Work.FIPlan.gnorm z)) (hweight z hz))
            (abs_nonneg _))
          (by positivity))
        (Zint_nonneg _)
    rw [hLS0, abs_zero]
    linarith

end

end Work.FITop4.Red5

/-
# `Submission.Work.FITop4.Red5.sieve_inner_le_pieces_act`

The *active-`i`* sharpening of `sieve_inner_le_pieces_ref`: the two cell-coefficient errors on the
right-hand side are summed only over the active polar cells `i`, i.e. those with
`m · a i < x`.

The point is that a cell whose radial scale is so large that `m · a i ≥ x` can never meet the
sieve conditions `N < |z|² ≤ 2N`, `m |z|² ≤ x` while `p_i(|z|²) ≠ 0` (the latter forces
`a i < |z|²`, hence `m a i < m |z|² ≤ x`).  Thus the matched sum `innerSum (∑_i p_i)` decomposes
over the *active* cells only, and each cell is bounded by `per_w_bound_zint` after specialization
to a one-element index type.  The radial-defect term `T3` is unchanged.
-/
import Mathlib
import Submission.Work.FITop4.Red5.sieve_inner_le_pieces_ref

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The per-cell comparison

`per_w_bound_zint` bounds the matched sum, expanded over *all* cells `i`, by the cell-coefficient
errors.  For the active-`i` version we need the same bound for a single cell, which is the `K = 1`
specialization of `per_w_bound_zint`. -/
lemma per_w_bound_single {m x N Pz : ℕ} {C τ θ : ℝ} {K K' : ℕ}
    {a : Fin K → ℝ} {p : Fin K → ℝ → ℝ} {φ : Fin K' → ℝ} {q : Fin K' → ℝ → ℝ}
    {Pa : Fin K → Fin K' → Work.FITop.Params}
    (H : PieceHyp m x N Pz C τ θ a p φ q Pa) (i : Fin K) (w : GaussianInt) :
    |innerSum m N x Pz C τ (fun n => p i n) w|
      ≤ (∑ k, ‖∑ z ∈ primAnn (2 * N),
              pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
        + (∑ k, ∑ z ∈ primAnn (2 * N),
            2 * badInd m x τ (Work.FIPlan.gnorm z)
              * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖) := by
  let a' : Fin 1 → ℝ := fun _ => a i
  let p' : Fin 1 → ℝ → ℝ := fun _ => p i
  let Pa' : Fin 1 → Fin K' → Work.FITop.Params := fun _ k => Pa i k
  have H' : PieceHyp m x N Pz C τ θ a' p' φ q Pa' :=
    { ha := fun j => H.ha i
      hPaN := fun j k => H.hPaN i k
      hPaC := fun j k => H.hPaC i k
      hPaPz := fun j k => H.hPaPz i k
      hPaθ := fun j k => H.hPaθ i k
      hPatau := fun j k n hn hτ => H.hPatau i k n hn hτ
      hp0 := fun j u => H.hp0 i u
      hpsup := fun j u hu => H.hpsup i u hu
      hq0 := H.hq0
      hq0z := H.hq0z
      hqsup := H.hqsup
      hang := H.hang }
  have hb := per_w_bound_zint (H := H') w
  simp only [p', Pa', Fin.sum_univ_one] at hb
  exact hb

/-! ## Linearity of `innerSum` in the radial weight -/

lemma innerSum_sum_lin {m N x Pz : ℕ} {C τ : ℝ} {K : ℕ} (p : Fin K → ℝ → ℝ) (w : GaussianInt) :
    innerSum m N x Pz C τ (fun n => ∑ i, p i n) w
      = ∑ i, innerSum m N x Pz C τ (fun n => p i n) w := by
  simp only [innerSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hc : cGPred m N x Pz τ (Work.FIPlan.gnorm z)
  · rw [if_pos hc, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos hc]
  · rw [if_neg hc]
    apply Eq.symm
    apply Finset.sum_eq_zero
    intro i hi
    rw [if_neg hc]

/-! ## The inactive cells contribute nothing -/

/-- If `m · a i ≥ x` then the `i`-th cell contributes nothing to the matched sum: on `cGPred` one
has `m |z|² ≤ x`, while `p_i(|z|²) ≠ 0` forces `a i < |z|²`, i.e. `m a i < m |z|² ≤ x`. -/
lemma innerSum_pi_eq_zero {m x N Pz : ℕ} {C τ θ : ℝ} {K K' : ℕ}
    {a : Fin K → ℝ} {p : Fin K → ℝ → ℝ} {φ : Fin K' → ℝ} {q : Fin K' → ℝ → ℝ}
    {Pa : Fin K → Fin K' → Work.FITop.Params}
    (H : PieceHyp m x N Pz C τ θ a p φ q Pa) (hm : 1 ≤ m)
    {i : Fin K} (hi : ¬ (m:ℝ) * a i < (x:ℝ)) (w : GaussianInt) :
    innerSum m N x Pz C τ (fun n => p i n) w = 0 := by
  rw [innerSum]
  apply Finset.sum_eq_zero
  intro z hz
  by_cases hc : cGPred m N x Pz τ (Work.FIPlan.gnorm z)
  · rw [if_pos hc]
    have hp : p i ((Work.FIPlan.gnorm z : ℕ) : ℝ) = 0 := by
      by_contra hne
      have h1 := (H.hpsup i _ hne).1
      have hm0 : (0:ℝ) < (m:ℝ) := by
        have : (0:ℕ) < m := Nat.lt_of_lt_of_le Nat.zero_lt_one hm
        exact_mod_cast this
      have hlt : (m:ℝ) * a i < (m:ℝ) * ((Work.FIPlan.gnorm z : ℕ) : ℝ) :=
        mul_lt_mul_of_pos_left h1 hm0
      have hxz : (m:ℝ) * ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (x:ℝ) := by
        have := hc.2.2.1
        exact_mod_cast this
      exact hi (lt_of_lt_of_le hlt hxz)
    rw [hp, zero_mul]
  · rw [if_neg hc]

/-- The matched sum decomposes over the *active* cells only. -/
lemma innerSum_sum_eq_filt {m x N Pz : ℕ} {C τ θ : ℝ} {K K' : ℕ}
    {a : Fin K → ℝ} {p : Fin K → ℝ → ℝ} {φ : Fin K' → ℝ} {q : Fin K' → ℝ → ℝ}
    {Pa : Fin K → Fin K' → Work.FITop.Params}
    (H : PieceHyp m x N Pz C τ θ a p φ q Pa) (hm : 1 ≤ m) (w : GaussianInt) :
    innerSum m N x Pz C τ (fun n => ∑ i, p i n) w
      = ∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m:ℝ) * a i < (x:ℝ)),
          innerSum m N x Pz C τ (fun n => p i n) w := by
  rw [innerSum_sum_lin]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : (m:ℝ) * a i < (x:ℝ)
  · rw [if_pos h]
  · rw [if_neg h, innerSum_pi_eq_zero H hm h w]

/-! ## An elementary rearrangement of the two error sums -/

lemma rearrange_filt {K K' : ℕ} (W : Finset GaussianInt) (F : Finset (Fin K)) (Z : Finset GaussianInt)
    (A : GaussianInt → Fin K → Fin K' → ℝ) (B : GaussianInt → Fin K → Fin K' → GaussianInt → ℝ) :
    (∑ w ∈ W, ∑ i ∈ F, ((∑ k, A w i k) + (∑ k, ∑ z ∈ Z, B w i k z)))
      = (∑ i ∈ F, ∑ k, ∑ w ∈ W, A w i k)
        + (∑ i ∈ F, ∑ k, ∑ w ∈ W, ∑ z ∈ Z, B w i k z) := by
  rw [Finset.sum_congr rfl (fun w _ => Finset.sum_add_distrib)]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.sum_comm]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i hi
    rw [Finset.sum_comm]

theorem sieve_inner_le_pieces_act
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
        (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ Work.FITop4.PiCond Pz n ∧ Work.FITop4.TauCond τ n
          then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
            * Work.FITop.atilFIa (m * n) else 0)|
      ≤ (∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)),
            ∑ k, ∑ w ∈ Work.FITop4.Red5.wSph m,
            ‖∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
              Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
        + (∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)),
            ∑ k, ∑ w ∈ Work.FITop4.Red5.wSph m, ∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
            2 * Work.FITop4.Red5.badInd m x τ (Work.FIPlan.gnorm z)
              * ‖Work.FITop4.Red5.pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
        + (∑ w ∈ Work.FITop4.Red5.wSph m, ∑ z ∈ Work.FITop4.Red5.primAnn (2 * N),
            Work.FITop4.Red5.cGInd m N x Pz τ (Work.FIPlan.gnorm z)
              * (1 - ∑ i, p i (Work.FIPlan.gnorm z))
              * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
              * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
              * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) := by
  classical
  set LS : ℝ := ∑ n ∈ Finset.Icc 1 (2 * N),
      (if N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
        then (ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n
          * Work.FITop.atilFIa (m * n) else 0) with hLSdef
  set T1 : ℝ := ∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)),
      ∑ k, ∑ w ∈ wSph m,
        ‖∑ z ∈ primAnn (2 * N),
          pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ with hT1def
  set T2 : ℝ := ∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)),
      ∑ k, ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
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
    -- the matched part, summed over the active cells only
    have hMw : ∀ w ∈ wSph m, |innerSum m N x Pz C τ (fun n => ∑ i, p i n) w|
        ≤ ∑ i ∈ (Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)),
            ((∑ k, ‖∑ z ∈ primAnn (2 * N),
                    pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
              + ∑ k, ∑ z ∈ primAnn (2 * N),
                  2 * badInd m x τ (Work.FIPlan.gnorm z)
                    * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖) := by
      intro w hw
      rw [innerSum_sum_eq_filt H hm w]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      apply Finset.sum_le_sum
      intro i hi
      exact per_w_bound_single H i w
    have hA : |∑ w ∈ wSph m, innerSum m N x Pz C τ (fun n => ∑ i, p i n) w| ≤ T1 + T2 := by
      rw [hT1def, hT2def]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine le_trans (Finset.sum_le_sum hMw) ?_
      exact le_of_eq (rearrange_filt (wSph m)
        ((Finset.univ : Finset (Fin K)).filter (fun i => (m : ℝ) * a i < (x : ℝ)))
        (primAnn (2 * N)) _ _)
    -- the third term is unchanged
    have hB : |∑ w ∈ wSph m, innerSum m N x Pz C τ (fun n => 1 - ∑ i, p i n) w| ≤ T3 := by
      rw [hT3def]
      exact zint_third_bound_ref hweight
    rw [hLS, hsplit]
    have hbc : |(∑ w ∈ wSph m, innerSum m N x Pz C τ (fun n => ∑ i, p i n) w)
            + ∑ w ∈ wSph m, innerSum m N x Pz C τ (fun n => 1 - ∑ i, p i n) w|
        ≤ T1 + T2 + T3 := by
      have h1 := abs_add_le (∑ w ∈ wSph m, innerSum m N x Pz C τ (fun n => ∑ i, p i n) w)
        (∑ w ∈ wSph m, innerSum m N x Pz C τ (fun n => 1 - ∑ i, p i n) w)
      linarith [h1, hA, hB]
    exact hbc
  · -- ## `m` not squarefree: the left-hand side vanishes
    have hLS0 : LS = 0 := by
      rw [hLSdef]
      apply Finset.sum_eq_zero
      intro n hn
      by_cases h : N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n
      · rw [if_pos h]
        have hns : ¬ Squarefree (m * n) := fun hs => hsf (Squarefree.of_mul_left hs)
        rw [atilFIa_eq, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns]
        ring
      · rw [if_neg h]
    have h1 : 0 ≤ T1 := by
      rw [hT1def]
      apply Finset.sum_nonneg; intro i hi
      apply Finset.sum_nonneg; intro k hk
      apply Finset.sum_nonneg; intro w hw
      exact norm_nonneg _
    have h2 : 0 ≤ T2 := by
      rw [hT2def]
      apply Finset.sum_nonneg; intro i hi
      apply Finset.sum_nonneg; intro k hk
      apply Finset.sum_nonneg; intro w hw
      apply Finset.sum_nonneg; intro z hz
      exact mul_nonneg (mul_nonneg (by norm_num) (badInd_nonneg m x τ _)) (norm_nonneg _)
    have h3 : 0 ≤ T3 := by
      rw [hT3def]
      apply Finset.sum_nonneg; intro w hw
      apply Finset.sum_nonneg; intro z hz
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (cGInd_nonneg m N x Pz τ _) (hweight z hz))
            (abs_nonneg _))
          (by positivity))
        (Zint_nonneg _)
    rw [hLS0, abs_zero]
    linarith

end

end Work.FITop4.Red5

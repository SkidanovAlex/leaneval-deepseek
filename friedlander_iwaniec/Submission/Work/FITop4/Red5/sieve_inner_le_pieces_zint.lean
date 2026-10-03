/-
# `Submission.Work.FITop4.Red5.sieve_inner_le_pieces_zint`

The `Zint`-sharpened companion of `sieve_inner_le_pieces`: the sieve inner sum is bounded by

* `T1`, the cell-coefficient sums `∑_{i,k} ∑_{|w|²=m} ‖∑_{z} β^{ik}_z Z(Re wz)‖`;
* `T2`, the sharp second error term `∑_{i,k} ∑_{|w|²=m} ∑_{z} 2·badInd(|z|²)·‖β^{ik}_z Z(Re wz)‖`
  obtained from `term_le_piece` (which keeps the factor `Z(Re wz)`);
* `T3`, the radial-defect term `∑_{|w|²=m} ∑_{z} (1 - ∑_i p_i(|z|²))·τ(|z|²)·Z(Re wz)`.

The difference from `sieve_inner_le_pieces` is only in the second and third terms: the second uses
`term_le_piece` (with `Z`) rather than `term_le_piece_nzc'` (without), and the third is the
explicit `Z`-weighted majorant of the radial defect rather than the bare absolute value of that
sum.
-/
import Mathlib
import Submission.Work.FITop4.Red5.pieceDefs
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FITop4.Red5.piecesPerW
import Submission.Work.FITop4.Red5.anFI_sum_eq_gauss_primary
import Submission.Work.FITop4.Red5.angular_partition_le
import Submission.Work.FITop4.Red5.weighted_gauss_identity
import Submission.Work.FITop4.Red5.sieve_step
import Submission.Work.FITop4.Red5.term_le_piece

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary arithmetic bounds -/

/-- `|μ(n)| ≤ 1`, cast to `ℝ`. -/
lemma abs_moebius_cast_le_one_z (n : ℕ) :
    |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
  have h : |ArithmeticFunction.moebius n| ≤ (1 : ℤ) := ArithmeticFunction.abs_moebius_le_one
  have h2 : (((|ArithmeticFunction.moebius n| : ℤ)) : ℝ) ≤ ((1 : ℤ) : ℝ) := by exact_mod_cast h
  rw [Int.cast_abs] at h2
  simpa using h2

/-- `|μ(n)·γ(n;C)| ≤ τ(n)`. -/
lemma abs_moebius_mul_gammaTrunc_le (C : ℝ) (n : ℕ) :
    |(ArithmeticFunction.moebius n : ℝ) * Work.FIPlan.gammaTrunc C n|
      ≤ ((n.divisors.card : ℕ) : ℝ) := by
  rw [abs_mul]
  have h1 : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    have h := abs_moebius_cast_le_one_z n
    simpa using h
  have h2 : |Work.FIPlan.gammaTrunc C n| ≤ ((n.divisors.card : ℕ) : ℝ) :=
    Work.FITop3.abs_gammaTrunc_le C n
  calc |(ArithmeticFunction.moebius n : ℝ)| * |Work.FIPlan.gammaTrunc C n|
      ≤ 1 * ((n.divisors.card : ℕ) : ℝ) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = ((n.divisors.card : ℕ) : ℝ) := by ring

/-! ## Nonnegativity of the radial defect `1 - ∑_i p_i` on the annulus -/

/-- On `primAnn (2N)` the radial defect `1 - ∑_i p_i(|z|²)` is nonnegative: by the support
condition `hpsup` every `p_i` vanishes below `a_i ≥ N`, and on `N < u ≤ 2N` the partition
hypothesis `hpsum` gives `∑_i p_i(u) ≤ 1`. -/
lemma one_sub_sum_p_nonneg {N K : ℕ} {θ : ℝ} {a : Fin K → ℝ} {p : Fin K → ℝ → ℝ}
    (ha : ∀ i, (N : ℝ) ≤ a i)
    (hpsup : ∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i)
    (hpsum : ∀ u, (N : ℝ) < u → u ≤ 2 * (N : ℝ) → (∑ i, p i u) ≤ 1)
    {z : GaussianInt} (hz : z ∈ primAnn (2 * N)) :
    0 ≤ 1 - ∑ i, p i ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
  have hzle : Work.FIPlan.gnorm z ≤ 2 * N := gnorm_le_of_mem_primAnn hz
  rcases Nat.lt_or_ge N (Work.FIPlan.gnorm z) with hlt | hle
  · have hgt : (N : ℝ) < ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by exact_mod_cast hlt
    have h2 : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
      have h : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by exact_mod_cast hzle
      push_cast at h; linarith
    have := hpsum _ hgt h2
    linarith
  · have hzero : (∑ i, p i ((Work.FIPlan.gnorm z : ℕ) : ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_contra hne
      have h1 := (hpsup i _ hne).1
      have h2 : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle
      linarith [ha i]
    rw [hzero]; norm_num

/-! ## The third term: the `Z`-weighted majorant of the radial defect -/

/-- **The `Z`-weighted bound of the radial-defect sum.**  For a nonnegative radial weight
`η(n) = 1 - ∑_i p_i(n)` on the annulus, the absolute value of the weighted Gaussian sum
`∑_{|w|²=m} ∑_z η(|z|²) μ(|z|²) γ(|z|²;C) Z(Re wz)` is dominated by the explicit double sum
`∑_{|w|²=m} ∑_z η(|z|²) τ(|z|²) Z(Re wz)`: termwise on the support `cGPred` one uses
`|μ·γ| ≤ τ`, and off it the summand vanishes. -/
lemma zint_third_bound {m x N Pz : ℕ} {C τ : ℝ} {K : ℕ} {p : Fin K → ℝ → ℝ}
    (hweight : ∀ z ∈ primAnn (2 * N), 0 ≤ 1 - ∑ i, p i ((Work.FIPlan.gnorm z : ℕ) : ℝ)) :
    |∑ w ∈ wSph m, innerSum m N x Pz C τ (fun n => 1 - ∑ i, p i (n : ℝ)) w|
      ≤ ∑ w ∈ wSph m, ∑ z ∈ primAnn (2 * N),
          (1 - ∑ i, p i ((Work.FIPlan.gnorm z : ℕ) : ℝ))
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by
  simp only [innerSum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum (fun w _ => ?_)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine Finset.sum_le_sum (fun z hz => ?_)
  have hη : 0 ≤ 1 - ∑ i, p i ((Work.FIPlan.gnorm z : ℕ) : ℝ) := hweight z hz
  have hZ : 0 ≤ (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := Zint_nonneg _
  by_cases hc : cGPred m N x Pz τ (Work.FIPlan.gnorm z)
  · rw [if_pos hc]
    have hmg : |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)
        * Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z)|
        ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) :=
      abs_moebius_mul_gammaTrunc_le C _
    calc |(1 - ∑ i, p i ((Work.FIPlan.gnorm z : ℕ) : ℝ)) * zFactor C w z|
        = (1 - ∑ i, p i ((Work.FIPlan.gnorm z : ℕ) : ℝ))
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)
                * Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z)|
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by
          rw [zFactor, abs_mul, abs_of_nonneg hη, abs_mul, abs_of_nonneg hZ]; ring
      _ ≤ (1 - ∑ i, p i ((Work.FIPlan.gnorm z : ℕ) : ℝ))
            * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmg hη) hZ
  · rw [if_neg hc, abs_zero]
    have hc0 : (0 : ℝ) ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by positivity
    exact mul_nonneg (mul_nonneg hη hc0) hZ

/-! ## The sharp second error term -/

/-- **The sharp difference bound of the matched and reconstructed sums.**  The difference
`matchedSum - cfSum = matchedSum - qSum` is bounded termwise by `2·badInd·‖β·Z‖` (this is exactly
`term_le_piece`, which keeps the factor `Z(Re wz)`). -/
lemma matched_sub_cfSum_le {m x N Pz : ℕ} {C τ θ : ℝ} {K K' : ℕ}
    {a : Fin K → ℝ} {p : Fin K → ℝ → ℝ} {φ : Fin K' → ℝ} {q : Fin K' → ℝ → ℝ}
    {Pa : Fin K → Fin K' → Work.FITop.Params}
    (H : PieceHyp m x N Pz C τ θ a p φ q Pa) (w : GaussianInt) :
    |matchedSum m N x Pz C τ φ q Pa p w - cfSum N φ q Pa p w|
      ≤ ∑ i, ∑ k, ∑ z ∈ primAnn (2 * N),
          2 * badInd m x τ (Work.FIPlan.gnorm z)
            * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ := by
  rw [cfSum_eq_qSum H w]
  have hpt : ∀ (i : Fin K) (k : Fin K') (z : GaussianInt), z ∈ primAnn (2 * N) →
      |cGInd m N x Pz τ (Work.FIPlan.gnorm z)
          * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
            * zFactor C w z)
        - QInd Pz (Pa i k) (Work.FIPlan.gnorm z)
          * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
            * zFactor C w z)|
      ≤ 2 * badInd m x τ (Work.FIPlan.gnorm z)
            * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ := by
    intro i k z hz
    set X : ℝ := q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
      * zFactor C w z with hXdef
    have hge : cGInd m N x Pz τ (Work.FIPlan.gnorm z) ≤ QInd Pz (Pa i k) (Work.FIPlan.gnorm z) :=
      cGInd_le_QInd (H.hPaPz i k) (gnorm_le_of_mem_primAnn hz)
        (H.hPatau i k (Work.FIPlan.gnorm z) (gnorm_le_of_mem_primAnn hz))
    have hXabs : |X| = q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
        * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
        * |Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z)|
        * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by
      rw [hXdef, zFactor]
      simp only [abs_mul, abs_of_nonneg (H.hq0 k _), abs_of_nonneg (H.hp0 i _),
        abs_of_nonneg (Zint_nonneg _)]
      ring
    have hmain := term_le_piece (m := m) (N := N) (x := x) (Pz := Pz) (τ := τ)
      (Pa := Pa i k) (φ := φ k) (q := q k) (p := p i)
      (H.hPaPz i k)
      (H.hPatau i k)
      (by rw [H.hPaN i k]; exact H.ha i)
      (fun u hu => by rw [H.hPaN i k, H.hPaθ i k]; exact H.hpsup i u hu)
      (H.hq0z k)
      (fun α hα => by rw [H.hPaθ i k]; exact H.hqsup k α hα)
      (H.hp0 i) (H.hq0 k) z hz w
    rw [H.hPaC i k] at hmain
    rw [show cGInd m N x Pz τ (Work.FIPlan.gnorm z) * X
          - QInd Pz (Pa i k) (Work.FIPlan.gnorm z) * X
        = -((QInd Pz (Pa i k) (Work.FIPlan.gnorm z)
            - cGInd m N x Pz τ (Work.FIPlan.gnorm z)) * X) by ring,
      abs_neg, abs_mul, abs_of_nonneg (sub_nonneg.mpr hge), hXabs]
    calc (QInd Pz (Pa i k) (Work.FIPlan.gnorm z) - cGInd m N x Pz τ (Work.FIPlan.gnorm z))
          * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * |Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z)|
            * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
        = (QInd Pz (Pa i k) (Work.FIPlan.gnorm z) - cGInd m N x Pz τ (Work.FIPlan.gnorm z))
          * q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
          * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
          * |Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z)|
          * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by ring
      _ ≤ 2 * badInd m x τ (Work.FIPlan.gnorm z)
            * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ := hmain
  have hdiff : ∀ i : Fin K,
      (∑ k, ∑ z ∈ primAnn (2 * N),
          cGInd m N x Pz τ (Work.FIPlan.gnorm z)
            * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
              * zFactor C w z))
        - (∑ k, ∑ z ∈ primAnn (2 * N),
          QInd Pz (Pa i k) (Work.FIPlan.gnorm z)
            * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
              * zFactor C w z))
      = ∑ k, ∑ z ∈ primAnn (2 * N),
          (cGInd m N x Pz τ (Work.FIPlan.gnorm z)
              * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
                * zFactor C w z)
            - QInd Pz (Pa i k) (Work.FIPlan.gnorm z)
              * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
                * zFactor C w z)) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_sub_distrib]
  rw [matchedSum, qSum, ← Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun i _ => hdiff i)]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  apply Finset.sum_le_sum; intro i _
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  apply Finset.sum_le_sum; intro k _
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  exact Finset.sum_le_sum (fun z hz => hpt i k z hz)

/-! ## The per-`w` comparison (sharp version) -/

/-- **The per-`w` piece comparison, in the sharp `Z`-weighted form.** -/
lemma per_w_bound_zint {m x N Pz : ℕ} {C τ θ : ℝ} {K K' : ℕ}
    {a : Fin K → ℝ} {p : Fin K → ℝ → ℝ} {φ : Fin K' → ℝ} {q : Fin K' → ℝ → ℝ}
    {Pa : Fin K → Fin K' → Work.FITop.Params}
    (H : PieceHyp m x N Pz C τ θ a p φ q Pa) (w : GaussianInt) :
    |innerSum m N x Pz C τ (fun n => ∑ i, p i n) w|
      ≤ (∑ i, ∑ k, ‖∑ z ∈ primAnn (2 * N),
              pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
        + ∑ i, ∑ k, ∑ z ∈ primAnn (2 * N),
            2 * badInd m x τ (Work.FIPlan.gnorm z)
              * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ := by
  have h1 : innerSum m N x Pz C τ (fun n => ∑ i, p i n) w
      = matchedSum m N x Pz C τ φ q Pa p w := innerSum_eq_matched H w
  have h3 : |matchedSum m N x Pz C τ φ q Pa p w - cfSum N φ q Pa p w|
      ≤ ∑ i, ∑ k, ∑ z ∈ primAnn (2 * N),
          2 * badInd m x τ (Work.FIPlan.gnorm z)
            * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ :=
    matched_sub_cfSum_le H w
  have h4 : ‖pcSum N φ q Pa p w‖
      ≤ ∑ i, ∑ k, ‖∑ z ∈ primAnn (2 * N),
          pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ := by
    rw [pcSum]
    calc ‖∑ i, ∑ k, ∑ z ∈ primAnn (2 * N),
            pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖
        ≤ ∑ i, ‖∑ k, ∑ z ∈ primAnn (2 * N),
            pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i, ∑ k, ‖∑ z ∈ primAnn (2 * N),
            pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ :=
          Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
  rw [h1]
  have hsplit : matchedSum m N x Pz C τ φ q Pa p w
      = cfSum N φ q Pa p w + (matchedSum m N x Pz C τ φ q Pa p w - cfSum N φ q Pa p w) := by
    ring
  rw [hsplit]
  calc |cfSum N φ q Pa p w + (matchedSum m N x Pz C τ φ q Pa p w - cfSum N φ q Pa p w)|
      ≤ |cfSum N φ q Pa p w| + |matchedSum m N x Pz C τ φ q Pa p w - cfSum N φ q Pa p w| :=
        abs_add_le _ _
    _ = ‖pcSum N φ q Pa p w‖ + |matchedSum m N x Pz C τ φ q Pa p w - cfSum N φ q Pa p w| := by
        rw [norm_pcSum]
    _ ≤ (∑ i, ∑ k, ‖∑ z ∈ primAnn (2 * N),
            pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
          + ∑ i, ∑ k, ∑ z ∈ primAnn (2 * N),
              2 * badInd m x τ (Work.FIPlan.gnorm z)
                * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖ :=
        add_le_add h4 h3

/-! ## The main theorem -/

theorem sieve_inner_le_pieces_zint
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
            (1 - ∑ i, p i (Work.FIPlan.gnorm z))
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
      (1 - ∑ i, p i (Work.FIPlan.gnorm z))
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
      (zint_third_bound hweight).trans (le_of_eq hT3def.symm)
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
      exact mul_nonneg (mul_nonneg (hweight z hz) (by positivity)) (Zint_nonneg _)
    rw [hLS0, abs_zero]
    linarith

end

end Work.FITop4.Red5

/-
# `Submission.Work.FITop4.Red5.piecesPerW` — the per-`w` piece comparison

The heart of `sieve_inner_le_pieces`: for a fixed outer variable `w`, the sieve inner sum
`∑_{|z|²≤2N} [conditions] μ(|z|²)γ(|z|²) Z(Re wz)` — after the Gaussian identity — is compared with
the sum of the cell coefficients `pieceCoeff (Pa i k) (φ k) (q k) (p i)`.

The comparison is the decomposition `1 = ∑_i p_i + (1 - ∑_i p_i)` of the radial partition, in which
the first part is expanded further with the angular partition `∑_k q_k = 1`.  The error made in
replacing the exact indicator `cGPred` (the five conditions of the sieve sum) by the support
condition `QInd` of `pieceCoeff` is controlled by `badInd`, exactly the `0/1` factor of the second
error term of `sieve_inner_le_pieces`.
-/
import Mathlib
import Submission.Work.FITop4.Red5.piecesSetup
import Submission.Work.FITop4.Red5.cfVal_eq_Q
import Submission.Work.FITop4.Red5.term_le_piece

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 0. Elementary facts about the primary annulus -/

lemma isPrimary_of_mem_primAnn {R : ℕ} {z : GaussianInt} (h : z ∈ primAnn R) :
    Work.FIPlan.IsPrimary z := (Finset.mem_filter.mp h).2

lemma mem_primAnn_iff {R : ℕ} {z : GaussianInt} :
    z ∈ primAnn R ↔ z ∈ Work.FIPlan.gBox ((R : ℕ) : ℤ) ∧ 1 ≤ Work.FIPlan.gnorm z
      ∧ Work.FIPlan.gnorm z ≤ R ∧ Work.FIPlan.IsPrimary z := by
  simp only [primAnn, Finset.mem_filter]
  tauto

lemma gnorm_le_of_mem_primAnn {R : ℕ} {z : GaussianInt} (h : z ∈ primAnn R) :
    Work.FIPlan.gnorm z ≤ R := (mem_primAnn_iff.mp h).2.2.1

lemma one_le_gnorm_of_mem_primAnn {R : ℕ} {z : GaussianInt} (h : z ∈ primAnn R) :
    1 ≤ Work.FIPlan.gnorm z := (mem_primAnn_iff.mp h).2.1

/-- The norm of a cell coefficient, with the signs of `μ` and `γ` removed. -/
lemma norm_pieceCoeff (Pa : Work.FITop.Params) (φ : ℝ) (q p : ℝ → ℝ) (z : GaussianInt)
    (hq : 0 ≤ q (Complex.arg z.toComplex - φ)) (hp : 0 ≤ p (Work.FIPlan.gnorm z)) :
    ‖pieceCoeff Pa φ q p z‖ = pcInd Pa φ z * (q (Complex.arg z.toComplex - φ)
      * p (Work.FIPlan.gnorm z)
      * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
      * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|) := by
  rw [pieceCoeff_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_cfVal Pa φ q p z hq hp]

/-! ## 1. The sharp indicator inequality -/

/-- **The sharp indicator inequality.**  If both mollifier factors are non-zero at `z` (so that,
by the support conditions, `z` really lies in the polar cell `(Pa, φ)`), then
`(QInd - cGInd) · Z ≤ 2 · badInd · pcInd` for every `0 ≤ Z ≤ 2`.  The point is that the only
non-zero case is `QPred ∧ ¬cGPred`, where `QPred` gives the `(n,Π) = 1` and `τ(n) ≤ Pa.τ` clauses
(so `pcInd = 1`) and `¬cGPred` together with `N < n` (from `p(n) ≠ 0`) gives `¬goodPred`
(so `badInd = 1`). -/
lemma ind_sharp {m N x Pz : ℕ} {τ : ℝ} {Pa : Work.FITop.Params} {φ : ℝ} {q p : ℝ → ℝ}
    (hPz : Pa.Pz = Pz)
    (ha : (N : ℝ) ≤ Pa.N)
    (hpsup : ∀ u : ℝ, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    (hq0z : q 0 = 0)
    (hqsup : ∀ α : ℝ, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * Pa.θ)
    (z : GaussianInt) (hzprim : Work.FIPlan.IsPrimary z)
    (hpn : p ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≠ 0)
    (hqn : q (Complex.arg z.toComplex - φ) ≠ 0)
    {Z : ℝ} (hZ0 : 0 ≤ Z) (hZ2 : Z ≤ 2) :
    (QInd Pz Pa (Work.FIPlan.gnorm z) - cGInd m N x Pz τ (Work.FIPlan.gnorm z)) * Z
      ≤ 2 * badInd m x τ (Work.FIPlan.gnorm z) * pcInd Pa φ z := by
  by_cases hle : QInd Pz Pa (Work.FIPlan.gnorm z) - cGInd m N x Pz τ (Work.FIPlan.gnorm z) ≤ 0
  · have h1 : (QInd Pz Pa (Work.FIPlan.gnorm z) - cGInd m N x Pz τ (Work.FIPlan.gnorm z)) * Z ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hle hZ0
    have h2 : 0 ≤ 2 * badInd m x τ (Work.FIPlan.gnorm z) * pcInd Pa φ z :=
      mul_nonneg (mul_nonneg (by norm_num) (badInd_nonneg m x τ _)) (pcInd_nonneg Pa φ z)
    linarith
  · have hpos : 0 < QInd Pz Pa (Work.FIPlan.gnorm z) - cGInd m N x Pz τ (Work.FIPlan.gnorm z) :=
      not_le.mp hle
    have hQ : QPred Pz Pa (Work.FIPlan.gnorm z) := by
      by_contra hQ'
      rw [QInd, if_neg hQ'] at hpos
      have hc := cGInd_nonneg m N x Pz τ (Work.FIPlan.gnorm z)
      linarith
    have hcG : ¬ cGPred m N x Pz τ (Work.FIPlan.gnorm z) := by
      intro hc
      rw [QInd, if_pos hQ, cGInd, if_pos hc] at hpos
      norm_num at hpos
    have hcpu := hpsup _ hpn
    have hqsp := hqsup _ hqn
    have hNlt : N < Work.FIPlan.gnorm z := by
      have h1 : (N : ℝ) < ((Work.FIPlan.gnorm z : ℕ) : ℝ) := lt_of_le_of_lt ha hcpu.1
      exact_mod_cast h1
    have hargne : Complex.arg z.toComplex - φ ≠ 0 := fun h0 => hqn (by rw [h0]; exact hq0z)
    have hargpos : 0 < Complex.arg z.toComplex - φ := lt_of_le_of_ne hqsp.1 (Ne.symm hargne)
    have hbox : InPolarBox Pa φ z := ⟨hzprim, hcpu.1, hcpu.2, by linarith, by linarith⟩
    have hnsp : NoSmallPrimes Pa z := by
      intro r hr hrle
      exact hQ.1 r hr (by simpa [hPz] using hrle)
    have hpc : pcInd Pa φ z = 1 := by rw [pcInd, if_pos ⟨hbox, hnsp, hQ.2⟩]
    have hbad1 : badInd m x τ (Work.FIPlan.gnorm z) = 1 := by
      rw [badInd]
      split_ifs with hg
      · exact absurd ⟨hg.1, hNlt, hg.2.1, hQ.1, hg.2.2⟩ hcG
      · rfl
    have hQ1 : QInd Pz Pa (Work.FIPlan.gnorm z) ≤ 1 := QInd_one_le _ _ _
    have hcG0 : 0 ≤ cGInd m N x Pz τ (Work.FIPlan.gnorm z) := cGInd_nonneg m N x Pz τ _
    rw [hpc, hbad1]
    have hle1 : QInd Pz Pa (Work.FIPlan.gnorm z) - cGInd m N x Pz τ (Work.FIPlan.gnorm z) ≤ 1 := by
      linarith
    calc (QInd Pz Pa (Work.FIPlan.gnorm z) - cGInd m N x Pz τ (Work.FIPlan.gnorm z)) * Z
        ≤ 1 * 2 := mul_le_mul hle1 hZ2 hZ0 (by norm_num)
      _ = 2 * 1 * 1 := by norm_num

/-- The pointwise bound of the comparison in the form needed for the second error term of
`sieve_inner_le_pieces`: `badInd` and `‖pieceCoeff‖`, without the factor `‖Zc w z‖`. -/
lemma term_le_piece_nzc' {m N x Pz : ℕ} {τ : ℝ} {Pa : Work.FITop.Params} {φ : ℝ} {q p : ℝ → ℝ}
    (hPz : Pa.Pz = Pz)
    (ha : (N : ℝ) ≤ Pa.N)
    (hpsup : ∀ u : ℝ, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    (hq0z : q 0 = 0)
    (hqsup : ∀ α : ℝ, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * Pa.θ)
    (hp0 : ∀ u : ℝ, 0 ≤ p u) (hq0 : ∀ α : ℝ, 0 ≤ q α)
    (z : GaussianInt) (hz : z ∈ primAnn (2 * N)) (w : GaussianInt) :
    (QInd Pz Pa (Work.FIPlan.gnorm z) - cGInd m N x Pz τ (Work.FIPlan.gnorm z))
        * q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
        * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
        * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|
        * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)
      ≤ 2 * badInd m x τ (Work.FIPlan.gnorm z) * ‖pieceCoeff Pa φ q p z‖ := by
  have hAnn : 0 ≤ q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
      * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
      * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)| :=
    mul_nonneg (mul_nonneg (mul_nonneg (hq0 _) (hp0 _)) (abs_nonneg _)) (abs_nonneg _)
  have hnorm := norm_pieceCoeff Pa φ q p z (hq0 _) (hp0 _)
  have hprod : (QInd Pz Pa (Work.FIPlan.gnorm z) - cGInd m N x Pz τ (Work.FIPlan.gnorm z))
        * q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
        * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
        * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|
        * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)
      = ((QInd Pz Pa (Work.FIPlan.gnorm z) - cGInd m N x Pz τ (Work.FIPlan.gnorm z))
          * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
        * (q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
          * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
          * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|) := by ring
  rw [hprod, hnorm]
  by_cases hA : q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
      * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
      * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)| = 0
  · rw [hA]
    simp
  · have hpn : p ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≠ 0 := fun h => hA (by rw [h]; ring)
    have hqn : q (Complex.arg z.toComplex - φ) ≠ 0 := fun h => hA (by rw [h]; ring)
    have hsharp := ind_sharp (m := m) (N := N) (x := x) (Pz := Pz) (τ := τ) (Pa := Pa)
      (φ := φ) (q := q) (p := p) hPz ha hpsup hq0z hqsup z (isPrimary_of_mem_primAnn hz)
      hpn hqn (Zint_nonneg _) (by exact_mod_cast Zint_le_two (Work.FIPlan.cForm w z))
    calc ((QInd Pz Pa (Work.FIPlan.gnorm z) - cGInd m N x Pz τ (Work.FIPlan.gnorm z))
          * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
          * (q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|)
        ≤ (2 * badInd m x τ (Work.FIPlan.gnorm z) * pcInd Pa φ z)
          * (q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|) :=
          mul_le_mul_of_nonneg_right hsharp hAnn
      _ = 2 * badInd m x τ (Work.FIPlan.gnorm z) * (pcInd Pa φ z
          * (q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
            * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
            * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|)) := by ring

/-! ## 1bis. The weighted sums are additive in the radial weight -/

/-- `innerSum` is additive in the radial weight `η`. -/
lemma innerSum_add (m N x Pz : ℕ) (C τ : ℝ) (η₁ η₂ : ℕ → ℝ) (w : GaussianInt) :
    innerSum m N x Pz C τ η₁ w + innerSum m N x Pz C τ η₂ w
      = innerSum m N x Pz C τ (fun n => η₁ n + η₂ n) w := by
  rw [innerSum, innerSum, innerSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  by_cases h : cGPred m N x Pz τ (Work.FIPlan.gnorm z)
  · rw [if_pos h, if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h, if_neg h]; ring

/-- `innerSum` only depends on the values of `η` on the range of `gnorm`. -/
lemma innerSum_congr (m N x Pz : ℕ) (C τ : ℝ) {η₁ η₂ : ℕ → ℝ} (h : ∀ n, η₁ n = η₂ n)
    (w : GaussianInt) :
    innerSum m N x Pz C τ η₁ w = innerSum m N x Pz C τ η₂ w := by
  rw [innerSum, innerSum]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hc : cGPred m N x Pz τ (Work.FIPlan.gnorm z)
  · rw [if_pos hc, if_pos hc, h]
  · rw [if_neg hc, if_neg hc]

lemma sum_swap_kw {K K' : ℕ} (s : Finset GaussianInt) (f : GaussianInt → Fin K → Fin K' → ℝ) :
    (∑ i, ∑ k, ∑ w ∈ s, f w i k) = ∑ w ∈ s, ∑ i, ∑ k, f w i k := by
  rw [show (∑ i, ∑ k, ∑ w ∈ s, f w i k) = ∑ i, ∑ w ∈ s, ∑ k, f w i k from by
        apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_comm]]
  rw [Finset.sum_comm]

/-! ## 2. The matched part is the `(i,k)`-expansion of the weighted sum -/

/-- **The `∑_k q_k = 1` partition turns the weighted inner sum into the `(i,k)`-expanded matched
sum.** -/
lemma innerSum_eq_matched {m x N Pz : ℕ} {C τ θ : ℝ} {K K' : ℕ}
    {a : Fin K → ℝ} {p : Fin K → ℝ → ℝ} {φ : Fin K' → ℝ} {q : Fin K' → ℝ → ℝ}
    {Pa : Fin K → Fin K' → Work.FITop.Params}
    (H : PieceHyp m x N Pz C τ θ a p φ q Pa) (w : GaussianInt) :
    innerSum m N x Pz C τ (fun n => ∑ i, p i n) w = matchedSum m N x Pz C τ φ q Pa p w := by
  have hpt : ∀ z : GaussianInt,
      (if cGPred m N x Pz τ (Work.FIPlan.gnorm z) then
        (∑ i, p i (Work.FIPlan.gnorm z)) * zFactor C w z else 0)
      = ∑ i, ∑ k, cGInd m N x Pz τ (Work.FIPlan.gnorm z)
          * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
            * zFactor C w z) := by
    intro z
    have hq1 : (∑ k, q k (Complex.arg z.toComplex - φ k)) = 1 :=
      H.hang _ (le_of_lt (Complex.neg_pi_lt_arg _)) (Complex.arg_le_pi _)
    have h1 : ∀ i : Fin K, p i (Work.FIPlan.gnorm z)
        = ∑ k, q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z) := by
      intro i
      calc p i (Work.FIPlan.gnorm z) = 1 * p i (Work.FIPlan.gnorm z) := (one_mul _).symm
        _ = (∑ k, q k (Complex.arg z.toComplex - φ k)) * p i (Work.FIPlan.gnorm z) := by rw [hq1]
        _ = ∑ k, q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z) :=
            Finset.sum_mul Finset.univ (fun k => q k (Complex.arg z.toComplex - φ k))
              (p i (Work.FIPlan.gnorm z))
    have hstep : (∑ i, p i (Work.FIPlan.gnorm z)) * zFactor C w z
        = ∑ i, ∑ k, (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z))
            * zFactor C w z := by
      calc (∑ i, p i (Work.FIPlan.gnorm z)) * zFactor C w z
          = (∑ i, ∑ k, q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z))
              * zFactor C w z := by rw [Finset.sum_congr rfl (fun i _ => h1 i)]
        _ = ∑ i, (∑ k, q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z))
              * zFactor C w z :=
            Finset.sum_mul Finset.univ
              (fun i => ∑ k, q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z))
              (zFactor C w z)
        _ = ∑ i, ∑ k, (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z))
              * zFactor C w z := by
            apply Finset.sum_congr rfl
            intro i _
            exact Finset.sum_mul Finset.univ
              (fun k => q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z))
              (zFactor C w z)
    rw [ite_cGPred_mul, hstep, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  rw [innerSum, matchedSum]
  rw [Finset.sum_congr rfl (fun z _ => hpt z)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

/-- **`cfSum` is `qSum`**: pointwise, `cfVal` is the support indicator `QInd` times the mollifier
factors (`cfVal_eq_Q`). -/
lemma cfSum_eq_qSum {m x N Pz : ℕ} {C τ θ : ℝ} {K K' : ℕ}
    {a : Fin K → ℝ} {p : Fin K → ℝ → ℝ} {φ : Fin K' → ℝ} {q : Fin K' → ℝ → ℝ}
    {Pa : Fin K → Fin K' → Work.FITop.Params}
    (H : PieceHyp m x N Pz C τ θ a p φ q Pa) (w : GaussianInt) :
    cfSum N φ q Pa p w = qSum N Pz C φ q Pa p w := by
  rw [cfSum, qSum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro z hz
  rw [cfVal_eq_Q (Pa := Pa i k) (Pz := Pz) (φ k) (q k) (p i) (H.hPaPz i k) z
      (isPrimary_of_mem_primAnn hz)
      (fun u hu => by
        have h := H.hpsup i u hu
        rw [H.hPaN i k, H.hPaθ i k]
        exact h)
      (H.hq0z k)
      (fun α hα => by
        have h := H.hqsup k α hα
        rw [H.hPaθ i k]
        exact h), H.hPaC i k]
  rw [zFactor]
  ring

/-! ## 3. The difference of the matched and reconstructed sums -/

/-- **The difference of the two `(i,k)`-expanded sums is bounded term by term.** -/
lemma matched_sub_qSum_le {m x N Pz : ℕ} {C τ θ : ℝ} {K K' : ℕ}
    {a : Fin K → ℝ} {p : Fin K → ℝ → ℝ} {φ : Fin K' → ℝ} {q : Fin K' → ℝ → ℝ}
    {Pa : Fin K → Fin K' → Work.FITop.Params}
    (H : PieceHyp m x N Pz C τ θ a p φ q Pa) (w : GaussianInt) :
    |matchedSum m N x Pz C τ φ q Pa p w - qSum N Pz C φ q Pa p w|
      ≤ ∑ i, ∑ k, ∑ z ∈ primAnn (2 * N),
          ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z‖ * 2 * badInd m x τ (Work.FIPlan.gnorm z) := by
  have hpt : ∀ (i : Fin K) (k : Fin K') (z : GaussianInt), z ∈ primAnn (2 * N) →
      |cGInd m N x Pz τ (Work.FIPlan.gnorm z)
          * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
            * zFactor C w z)
        - QInd Pz (Pa i k) (Work.FIPlan.gnorm z)
          * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z)
            * zFactor C w z)|
      ≤ ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z‖ * 2 * badInd m x τ (Work.FIPlan.gnorm z) := by
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
    have hmain := term_le_piece_nzc' (m := m) (N := N) (x := x) (Pz := Pz) (τ := τ)
      (Pa := Pa i k) (φ := φ k) (q := q k) (p := p i)
      (H.hPaPz i k)
      (by rw [H.hPaN i k]; exact H.ha i)
      (fun u hu => by
        have h := H.hpsup i u hu
        rw [H.hPaN i k, H.hPaθ i k]
        exact h)
      (H.hq0z k)
      (fun α hα => by
        have h := H.hqsup k α hα
        rw [H.hPaθ i k]
        exact h)
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
            * ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z‖ := hmain
      _ = ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z‖ * 2 * badInd m x τ (Work.FIPlan.gnorm z) := by
          ring
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

/-! ## 4. The per-`w` comparison -/

/-- **The per-`w` piece comparison.**  For a fixed outer variable `w`, the "matched" part
`∑_{|z|²≤2N} [conditions] (∑_i p_i(|z|²)) μ γ Z(Re wz)` is bounded by the cell-coefficient sums over
all pieces plus the second error term. -/
theorem per_w_bound {m x N Pz : ℕ} {C τ θ : ℝ} {K K' : ℕ}
    {a : Fin K → ℝ} {p : Fin K → ℝ → ℝ} {φ : Fin K' → ℝ} {q : Fin K' → ℝ → ℝ}
    {Pa : Fin K → Fin K' → Work.FITop.Params}
    (H : PieceHyp m x N Pz C τ θ a p φ q Pa) (w : GaussianInt) :
    |innerSum m N x Pz C τ (fun n => ∑ i, p i n) w|
      ≤ ∑ i, ∑ k, (‖∑ z ∈ primAnn (2 * N),
              pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖
            + ∑ z ∈ primAnn (2 * N),
                ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z‖ * 2
                  * badInd m x τ (Work.FIPlan.gnorm z)) := by
  have h1 : innerSum m N x Pz C τ (fun n => ∑ i, p i n) w
      = matchedSum m N x Pz C τ φ q Pa p w := innerSum_eq_matched H w
  have h2 : cfSum N φ q Pa p w = qSum N Pz C φ q Pa p w := cfSum_eq_qSum H w
  have h3 : |matchedSum m N x Pz C τ φ q Pa p w - cfSum N φ q Pa p w|
      ≤ ∑ i, ∑ k, ∑ z ∈ primAnn (2 * N),
          ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z‖ * 2 * badInd m x τ (Work.FIPlan.gnorm z) := by
    rw [h2]
    exact matched_sub_qSum_le H w
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
      = cfSum N φ q Pa p w + (matchedSum m N x Pz C τ φ q Pa p w - cfSum N φ q Pa p w) := by ring
  rw [hsplit]
  calc |cfSum N φ q Pa p w + (matchedSum m N x Pz C τ φ q Pa p w - cfSum N φ q Pa p w)|
      ≤ |cfSum N φ q Pa p w| + |matchedSum m N x Pz C τ φ q Pa p w - cfSum N φ q Pa p w| :=
        abs_add_le _ _
    _ = ‖pcSum N φ q Pa p w‖ + |matchedSum m N x Pz C τ φ q Pa p w - cfSum N φ q Pa p w| := by
        rw [norm_pcSum]
    _ ≤ (∑ i, ∑ k, ‖∑ z ∈ primAnn (2 * N),
            pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖)
          + ∑ i, ∑ k, ∑ z ∈ primAnn (2 * N),
              ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z‖ * 2
                * badInd m x τ (Work.FIPlan.gnorm z) :=
        add_le_add h4 h3
    _ = ∑ i, ∑ k, (‖∑ z ∈ primAnn (2 * N),
            pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z‖
          + ∑ z ∈ primAnn (2 * N),
              ‖pieceCoeff (Pa i k) (φ k) (q k) (p i) z‖ * 2
                * badInd m x τ (Work.FIPlan.gnorm z)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _
        rw [← Finset.sum_add_distrib]

end

end Work.FITop4.Red5

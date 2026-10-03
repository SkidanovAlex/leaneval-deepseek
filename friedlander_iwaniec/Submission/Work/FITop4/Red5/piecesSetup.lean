/-
# `Submission.Work.FITop4.Red5.piecesSetup` — the vocabulary of the `sieve_inner_le_pieces` split

The §5.2 sieve step is bounded by *pieces*: the coefficient `β_z` of (4.13)+(5.13) is split into
the polar cells of the angular/radial partition, and the `μ(n)γ(n)ã(mn)` sum is compared with the
cell sums.  This file collects the small amount of vocabulary and the elementary real/complex
bookkeeping that the comparison needs:

* `wSph m` — the sphere `|w|² = m` (the outer sum);
* `primAnn R` — the primary part of the annulus `1 ≤ |z|² ≤ R` (the inner sum);
* `pcCond`/`cfVal` — the support condition of `pieceCoeff` and its **real scalar**, so that
  `pieceCoeff Pa φ q p z = ((cfVal Pa φ q p z : ℝ) : ℂ)`;
* the indicator-valued predicates of the comparison: `cGInd` (the five conditions `N < n`, `mn ≤ x`,
  coprimality, `(n,Π)=1`, `τ(n) ≤ τ`), `badInd` (its failure without the `N < n` clause, i.e. the
  `0/1` factor that appears in the second error term of `sieve_inner_le_pieces`), and `QInd`
  (the `pieceCoeff` support condition in the form `(n,Π) = 1 ∧ τ(n) ≤ Pa.τ`).
-/
import Mathlib
import Submission.Work.FITop4.Red5.pieceDefs

set_option autoImplicit false

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The two summation ranges -/

/-- The sphere `|w|² = m` of the outer variable, cut out of the box `gBox m`. -/
def wSph (m : ℕ) : Finset GaussianInt :=
  (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter (fun w => Work.FIPlan.gnorm w = m)

/-- The primary part of the annulus `1 ≤ |z|² ≤ R` of the inner variable. -/
def primAnn (R : ℕ) : Finset GaussianInt :=
  ((Work.FIPlan.gBox ((R : ℕ) : ℤ)).filter
      (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ R)).filter
    (fun z => Work.FIPlan.IsPrimary z)

/-! ## 2. The support condition of `pieceCoeff` and its real scalar -/

/-- The support condition of `pieceCoeff`: the polar box (5.14), the small-prime condition (5.8)
and the truncation (5.9). -/
def pcCond (Pa : Work.FITop.Params) (φ : ℝ) (z : GaussianInt) : Prop :=
  InPolarBox Pa φ z ∧ NoSmallPrimes Pa z ∧ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) ≤ Pa.τ

/-- The indicator of `pcCond`, as a real number. -/
def pcInd (Pa : Work.FITop.Params) (φ : ℝ) (z : GaussianInt) : ℝ :=
  if pcCond Pa φ z then 1 else 0

lemma pcInd_nonneg (Pa : Work.FITop.Params) (φ : ℝ) (z : GaussianInt) : 0 ≤ pcInd Pa φ z := by
  rw [pcInd]; split_ifs <;> norm_num

lemma pcInd_one_le (Pa : Work.FITop.Params) (φ : ℝ) (z : GaussianInt) : pcInd Pa φ z ≤ 1 := by
  rw [pcInd]; split_ifs <;> norm_num

/-- **The real scalar of the cell coefficient**: `pieceCoeff Pa φ q p z` is the cast of this. -/
def cfVal (Pa : Work.FITop.Params) (φ : ℝ) (q p : ℝ → ℝ) (z : GaussianInt) : ℝ :=
  pcInd Pa φ z * (q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z)
    * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)
    * Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z))

lemma cfVal_apply (Pa : Work.FITop.Params) (φ : ℝ) (q p : ℝ → ℝ) (z : GaussianInt) :
    cfVal Pa φ q p z = pcInd Pa φ z * (q (Complex.arg z.toComplex - φ)
      * p (Work.FIPlan.gnorm z)
      * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)
      * Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)) := rfl

/-- `pieceCoeff` is the cast of its real scalar `cfVal`. -/
lemma pieceCoeff_eq_ofReal (Pa : Work.FITop.Params) (φ : ℝ) (q p : ℝ → ℝ) (z : GaussianInt) :
    pieceCoeff Pa φ q p z = ((cfVal Pa φ q p z : ℝ) : ℂ) := by
  rw [pieceCoeff, cfVal, pcInd, pcCond]
  split_ifs <;> push_cast <;> ring

/-- `Zc w z` is the cast of `Z(Re wz)`. -/
lemma Zc_eq_ofReal (w z : GaussianInt) :
    Work.FITop3.Zc w z = ((Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) : ℂ) := by
  rw [Work.FITop3.Zc]
  push_cast
  ring

lemma Zint_nonneg (b : ℤ) : 0 ≤ (Work.FIPlan.Zint b : ℝ) := by
  rw [Work.FIPlan.Zint]
  split_ifs
  · norm_num
  · positivity

/-- The norm of `Zc` is `Z(Re wz)`. -/
lemma norm_Zc (w z : GaussianInt) :
    ‖Work.FITop3.Zc w z‖ = (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by
  rw [Zc_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Zint_nonneg _)]

/-- **The norm of one cell summand.**  The norm of `pieceCoeff z * Zc w z` is the absolute value of
the real scalar times `Z(Re wz)`. -/
lemma norm_pieceCoeff_mul_Zc (Pa : Work.FITop.Params) (φ : ℝ) (q p : ℝ → ℝ)
    (w z : GaussianInt) :
    ‖pieceCoeff Pa φ q p z * Work.FITop3.Zc w z‖
      = |cfVal Pa φ q p z| * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ) := by
  rw [pieceCoeff_eq_ofReal, Zc_eq_ofReal, ← Complex.ofReal_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (Zint_nonneg _)]

/-- Given `0 ≤ q (arg z - φ)` and `0 ≤ p n`, the absolute value of the real scalar is the scalar
with the signs of `μ` and `γ` removed. -/
lemma abs_cfVal (Pa : Work.FITop.Params) (φ : ℝ) (q p : ℝ → ℝ) (z : GaussianInt)
    (hq : 0 ≤ q (Complex.arg z.toComplex - φ)) (hp : 0 ≤ p (Work.FIPlan.gnorm z)) :
    |cfVal Pa φ q p z| = pcInd Pa φ z * (q (Complex.arg z.toComplex - φ)
      * p (Work.FIPlan.gnorm z)
      * |(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)|
      * |Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z)|) := by
  rw [cfVal_apply]
  have h1 : 0 ≤ pcInd Pa φ z := pcInd_nonneg Pa φ z
  rw [abs_mul, abs_of_nonneg h1]
  congr 1
  simp only [abs_mul, abs_of_nonneg hq, abs_of_nonneg hp]

/-! ## 3. The indicator-valued conditions of the comparison -/

/-- The five conditions of the inner sum of `sieve_inner_le_pieces`, as a predicate of `n`. -/
def cGPred (m N x Pz : ℕ) (τ : ℝ) (n : ℕ) : Prop :=
  Nat.Coprime m n ∧ N < n ∧ m * n ≤ x ∧ PiCond Pz n ∧ TauCond τ n

/-- The three conditions of the second error term (the five of `cGPred` without `N < n`). -/
def goodPred (m x : ℕ) (τ : ℝ) (n : ℕ) : Prop :=
  Nat.Coprime m n ∧ m * n ≤ x ∧ TauCond τ n

/-- `(n,Π) = 1` and `τ(n) ≤ Pa.τ`: the part of the `pieceCoeff` support condition that depends on
the parameter `Pa` (the polar box is handled separately, through `InPolarBox`). -/
def QPred (Pz : ℕ) (Pa : Work.FITop.Params) (n : ℕ) : Prop :=
  PiCond Pz n ∧ (((n.divisors.card : ℕ) : ℝ) ≤ Pa.τ)

lemma cGPred_iff (m N x Pz : ℕ) (τ : ℝ) (n : ℕ) :
    (N < n ∧ m * n ≤ x ∧ Nat.Coprime n m ∧ PiCond Pz n ∧ TauCond τ n)
      ↔ cGPred m N x Pz τ n := by
  rw [cGPred]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h3.symm, h1, h2, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h2, h3, h1.symm, h4, h5⟩

/-- The indicator of `cGPred`, as a real number. -/
def cGInd (m N x Pz : ℕ) (τ : ℝ) (n : ℕ) : ℝ := if cGPred m N x Pz τ n then 1 else 0

/-- The `0/1` factor `(if coprime m n ∧ m n ≤ x ∧ τ(n) ≤ τ then 0 else 1)` of the second error
term of `sieve_inner_le_pieces`. -/
def badInd (m x : ℕ) (τ : ℝ) (n : ℕ) : ℝ := if goodPred m x τ n then 0 else 1

lemma cGPred_iff' (m N x Pz : ℕ) (τ : ℝ) (n : ℕ) :
    (Nat.Coprime m n ∧ N < n ∧ m * n ≤ x ∧ PiCond Pz n ∧ TauCond τ n) ↔ cGPred m N x Pz τ n := by
  rw [cGPred]

lemma ite_eq_badInd (m x : ℕ) (τ : ℝ) (n : ℕ) :
    (if Nat.Coprime m n ∧ m * n ≤ x ∧ (((n.divisors.card : ℕ) : ℝ) ≤ τ) then (0 : ℝ) else 1)
      = badInd m x τ n := by
  rw [badInd, goodPred, TauCond]
  by_cases h : Nat.Coprime m n ∧ m * n ≤ x ∧ (((n.divisors.card : ℕ) : ℝ) ≤ τ)
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]


/-- The indicator of `QPred`, as a real number. -/
def QInd (Pz : ℕ) (Pa : Work.FITop.Params) (n : ℕ) : ℝ := if QPred Pz Pa n then 1 else 0

lemma cGInd_nonneg (m N x Pz : ℕ) (τ : ℝ) (n : ℕ) : 0 ≤ cGInd m N x Pz τ n := by
  rw [cGInd]; split_ifs <;> norm_num

lemma QInd_nonneg (Pz : ℕ) (Pa : Work.FITop.Params) (n : ℕ) : 0 ≤ QInd Pz Pa n := by
  rw [QInd]; split_ifs <;> norm_num

lemma badInd_nonneg (m x : ℕ) (τ : ℝ) (n : ℕ) : 0 ≤ badInd m x τ n := by
  rw [badInd]; split_ifs <;> norm_num

lemma cGInd_one_le (m N x Pz : ℕ) (τ : ℝ) (n : ℕ) : cGInd m N x Pz τ n ≤ 1 := by
  rw [cGInd]; split_ifs <;> norm_num

lemma QInd_one_le (Pz : ℕ) (Pa : Work.FITop.Params) (n : ℕ) : QInd Pz Pa n ≤ 1 := by
  rw [QInd]; split_ifs <;> norm_num

lemma badInd_one_le (m x : ℕ) (τ : ℝ) (n : ℕ) : badInd m x τ n ≤ 1 := by
  rw [badInd]; split_ifs <;> norm_num

/-- `cGPred` implies `QPred` as soon as the truncation of `Pa` dominates `τ` on the range
`n ≤ 2N` (the hypothesis `hPatau` of `sieve_inner_le_pieces`). -/
lemma QPred_of_cGPred {m N x Pz : ℕ} {τ : ℝ} {Pa : Work.FITop.Params} {n : ℕ}
    (hPz : Pa.Pz = Pz) (hn : n ≤ 2 * N)
    (hτ : n ≤ 2 * N → (((n.divisors.card : ℕ) : ℝ) ≤ τ) → (((n.divisors.card : ℕ) : ℝ) ≤ Pa.τ))
    (h : cGPred m N x Pz τ n) : QPred Pz Pa n :=
  ⟨h.2.2.2.1, hτ hn h.2.2.2.2⟩

/-- `badInd` vanishes exactly when the three conditions `goodPred` hold. -/
lemma badInd_eq_zero_iff (m x : ℕ) (τ : ℝ) (n : ℕ) :
    badInd m x τ n = 0 ↔ goodPred m x τ n := by
  rw [badInd]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h0 => absurd h0 one_ne_zero, fun hg => absurd hg h⟩

/-- The `N < n` clause of `cGPred` is what distinguishes it from `goodPred`. -/
lemma goodPred_of_cGPred {m N x Pz : ℕ} {τ : ℝ} {n : ℕ} (h : cGPred m N x Pz τ n) :
    goodPred m x τ n := ⟨h.1, h.2.2.1, h.2.2.2.2⟩

/-! ## 4. The hypotheses and the per-`w` sums of the piece comparison -/

/-- The hypotheses of the §5.2 sieve step that the comparison of the sieve sum with the pieces
uses (the pieces of `sieve_inner_le_pieces`). -/
structure PieceHyp (m x N Pz : ℕ) (C τ θ : ℝ) {K K' : ℕ}
    (a : Fin K → ℝ) (p : Fin K → ℝ → ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
    (Pa : Fin K → Fin K' → Work.FITop.Params) : Prop where
  ha : ∀ i, (N : ℝ) ≤ a i
  hPaN : ∀ i k, (Pa i k).N = a i
  hPaC : ∀ i k, (Pa i k).C = C
  hPaPz : ∀ i k, (Pa i k).Pz = Pz
  hPaθ : ∀ i k, (Pa i k).θ = θ
  hPatau : ∀ i k n, n ≤ 2 * N → (((n.divisors.card : ℕ) : ℝ) ≤ τ) →
    (((n.divisors.card : ℕ) : ℝ) ≤ (Pa i k).τ)
  hp0 : ∀ i u, 0 ≤ p i u
  hpsup : ∀ i u, p i u ≠ 0 → a i < u ∧ u ≤ (1 + θ) * a i
  hq0 : ∀ k α, 0 ≤ q k α
  hq0z : ∀ k, q k 0 = 0
  hqsup : ∀ k α, q k α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ
  hang : ∀ α, -Real.pi ≤ α → α ≤ Real.pi → (∑ k, q k (α - φ k)) = 1

/-- The common factor `μ(|z|²)·γ(|z|²;C)·Z(Re wz)` of every inner sum of the sieve step. -/
def zFactor (C : ℝ) (w z : GaussianInt) : ℝ :=
  (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ)
    * Work.FIPlan.gammaTrunc C (Work.FIPlan.gnorm z)
    * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)

/-- The inner `z`-sum of the sieve step, with an extra radial weight `η`: this is the shape in
which both the left-hand side and the third error term of `sieve_inner_le_pieces` appear after
the Gaussian identity (`Work.FITop4.Red5.weighted_gauss_identity`), with `η ≡ 1` and
`η = 1 - ∑_i p_i` respectively. -/
def innerSum (m N x Pz : ℕ) (C τ : ℝ) (η : ℕ → ℝ) (w : GaussianInt) : ℝ :=
  ∑ z ∈ primAnn (2 * N),
    (if cGPred m N x Pz τ (Work.FIPlan.gnorm z) then
      η (Work.FIPlan.gnorm z) * zFactor C w z else 0)

/-- The cell coefficient sum, summed over the angular and radial pieces. -/
def pcSum {K K' : ℕ} (N : ℕ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
    (Pa : Fin K → Fin K' → Work.FITop.Params) (p : Fin K → ℝ → ℝ)
    (w : GaussianInt) : ℂ :=
  ∑ i, ∑ k, ∑ z ∈ primAnn (2 * N),
    pieceCoeff (Pa i k) (φ k) (q k) (p i) z * Work.FITop3.Zc w z

/-- The real version of `pcSum`: the real scalar `cfVal` of `pieceCoeff` times `Z(Re wz)`. -/
def cfSum {K K' : ℕ} (N : ℕ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
    (Pa : Fin K → Fin K' → Work.FITop.Params) (p : Fin K → ℝ → ℝ)
    (w : GaussianInt) : ℝ :=
  ∑ i, ∑ k, ∑ z ∈ primAnn (2 * N),
    cfVal (Pa i k) (φ k) (q k) (p i) z * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)

/-- The `(i,k)`-expanded "matched" part of `innerSum m N x Pz C τ (∑_i p_i) w`: the indicator
`cGInd` and the `∑_k q_k = 1` partition inserted. -/
def matchedSum {K K' : ℕ} (m N x Pz : ℕ) (C τ : ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
    (Pa : Fin K → Fin K' → Work.FITop.Params) (p : Fin K → ℝ → ℝ) (w : GaussianInt) : ℝ :=
  ∑ i, ∑ k, ∑ z ∈ primAnn (2 * N),
    cGInd m N x Pz τ (Work.FIPlan.gnorm z)
      * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z) * zFactor C w z)

/-- The `(i,k)`-expanded reconstruction of the cell coefficients, with the `pieceCoeff` support
condition replaced by its `(n,Π) = 1`, `τ(n) ≤ Pa.τ` part (the polar box being discharged by the
support of the mollifiers). -/
def qSum {K K' : ℕ} (N Pz : ℕ) (C : ℝ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
    (Pa : Fin K → Fin K' → Work.FITop.Params) (p : Fin K → ℝ → ℝ) (w : GaussianInt) : ℝ :=
  ∑ i, ∑ k, ∑ z ∈ primAnn (2 * N),
    QInd Pz (Pa i k) (Work.FIPlan.gnorm z)
      * (q k (Complex.arg z.toComplex - φ k) * p i (Work.FIPlan.gnorm z) * zFactor C w z)

/-! ## 5. Elementary rewrites for the comparison -/

lemma ite_cGPred_mul (m N x Pz : ℕ) (τ : ℝ) (n : ℕ) (X : ℝ) :
    (if cGPred m N x Pz τ n then X else 0) = cGInd m N x Pz τ n * X := by
  rw [cGInd]; split_ifs <;> ring

lemma ite_goodPred (m x : ℕ) (τ : ℝ) (n : ℕ) :
    (if goodPred m x τ n then (0 : ℝ) else 1) = badInd m x τ n := rfl

/-- `Zint` takes only the values `0, 1, 2`. -/
lemma Zint_le_two (b : ℤ) : Work.FIPlan.Zint b ≤ 2 := by
  rw [Work.FIPlan.Zint]
  split_ifs with h
  · norm_num
  · rw [Work.FIPlan.Zb]
    split_ifs <;> norm_num

/-- `cGPred` implies `QPred` on the range `n ≤ 2N` (the `hPatau` hypothesis), as an inequality of
the corresponding indicators. -/
lemma cGInd_le_QInd {m N x Pz : ℕ} {τ : ℝ} {Pa : Work.FITop.Params} {n : ℕ}
    (hPz : Pa.Pz = Pz) (hn : n ≤ 2 * N)
    (hτ : (((n.divisors.card : ℕ) : ℝ) ≤ τ) → (((n.divisors.card : ℕ) : ℝ) ≤ Pa.τ)) :
    cGInd m N x Pz τ n ≤ QInd Pz Pa n := by
  by_cases hc : cGPred m N x Pz τ n
  · have hq : QPred Pz Pa n := ⟨hc.2.2.2.1, hτ hc.2.2.2.2⟩
    rw [cGInd, if_pos hc, QInd, if_pos hq]
  · rw [cGInd, if_neg hc]
    exact QInd_nonneg _ _ _

/-- The norm of the cell sum is the absolute value of its real version. -/
lemma norm_pcSum {K K' : ℕ} (N : ℕ) (φ : Fin K' → ℝ) (q : Fin K' → ℝ → ℝ)
    (Pa : Fin K → Fin K' → Work.FITop.Params) (p : Fin K → ℝ → ℝ) (w : GaussianInt) :
    ‖pcSum N φ q Pa p w‖ = |cfSum N φ q Pa p w| := by
  have h : pcSum N φ q Pa p w = ((cfSum N φ q Pa p w : ℝ) : ℂ) := by
    rw [pcSum, cfSum, Complex.ofReal_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl; intro z _
    rw [pieceCoeff_eq_ofReal, Zc_eq_ofReal, ← Complex.ofReal_mul]
  rw [h, Complex.norm_real, Real.norm_eq_abs]

end

end Work.FITop4.Red5


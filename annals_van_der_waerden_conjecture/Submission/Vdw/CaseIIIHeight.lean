import Mathlib
import Submission.Vdw.DoubleDisc
import Submission.Vdw.DDFamInt
import Submission.Commons.RingTheory.Polynomial.discr_map_of_natDegree
import Submission.Commons.RingTheory.Polynomial.natDegree_map_eq_of_lc_ne_zero

open Polynomial Filter
open scoped BigOperators

/-!
# Case III: the box height bound for the double discriminant |DD(u)| ≤ H^K

Case III of Bhargava's proof (Section 5) counts box polynomials whose double
discriminant `DD(a₁,…,a_{n−1}) := Disc_{a₀}(Disc_X f)` does not vanish and whose
"large-prime part" `A = ∏_{p | C, p > H^{δ/2}} p` divides `DD(u)`.  The divisor
bookkeeping of that subcase needs the *box height bound*: for upper coefficients
bounded by `H` there is a fixed `K = K(n)` with `|DD(u)| ≤ H^K`.

This module proves exactly that (no interpolation, no determinant gymnastics): since
`DD` is a *fixed* polynomial in `n−1` variables over ℚ (`ddPoly n`), the generic
polynomial-evaluation bound `mvEval_abs_le` gives

  `|DD(u)| ≤ (Σ_{m ∈ supp DD} |coeff_m|) · H^(totalDegree DD)`,

and the exponent is a fixed number depending only on `n`.  Concretely:

- `ddEvalInt_eq_concDD`, `concDDZ_cast_eq_concDD`: the three incarnations of `DD(u)`
  (the MvPolynomial evaluation `ddEvalInt n u : ℚ`, the ℚ-concrete
  `concDD n (uQ u)`, and the honest integer `concDDZ n u : ℤ`) agree after casts —
  so `|concDDZ n u| = |ddEvalInt n u|` as rationals.
- `concDDZ_abs_le`: the explicit pointwise bound
  `(|concDDZ n u| : ℚ) ≤ ddSumAbs n · H^(totalDegree (ddPoly n))` for `H ≥ 1`,
  `|u_i| ≤ H`.
- `concDDZ_box_pow_le`: the eventual power bound used by Case III's subcase (ii):
  `∃ K, ∀ᶠ H, ∀ u ∈ Box(H), |concDDZ n u| ≤ H^K`.

(After Lemma 24 supplies the per-prime divisibility `A | DD(u)` for nonzero `DD(u)`,
this bound makes `ω(A) = O(1)`: each prime factor of `A` exceeds `H^{δ/2}`, and
`A ≤ |DD(u)| ≤ H^K`.)
-/

namespace Submission.Vdw

noncomputable section

-- ---------------------------------------------------------------
-- 1. generic polynomial-evaluation bound (over ℚ)
-- ---------------------------------------------------------------

/-- For a *fixed* polynomial `p` over ℚ, the absolute value of `p` at a point whose
coordinates are bounded by `H ≥ 1` is bounded by the ℓ¹ norm of the coefficient
vector times `H^(totalDegree p)`.  (Each monomial `m` contributes at most
`|coeff m| · H^(deg m) ≤ |coeff m| · H^(totalDegree p)`.) -/
lemma mvEval_abs_le {σ : Type*}
    (p : MvPolynomial σ ℚ) (v : σ → ℚ) (H : ℚ) (hH : 1 ≤ H) (hv : ∀ i, |v i| ≤ H) :
    |MvPolynomial.eval v p| ≤ (p.support.sum fun d => |p.coeff d|) * H ^ p.totalDegree := by
  classical
  rw [MvPolynomial.eval_eq]
  calc
    |∑ d ∈ p.support, (p.coeff d) * ∏ i ∈ d.support, (v i) ^ (d i)|
        ≤ ∑ d ∈ p.support, |(p.coeff d) * ∏ i ∈ d.support, (v i) ^ (d i)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ p.support, |p.coeff d| * H ^ p.totalDegree := by
      refine Finset.sum_le_sum ?_
      intro d hd
      have hprod : |∏ i ∈ d.support, (v i) ^ (d i)| ≤ H ^ p.totalDegree := by
        calc
          |∏ i ∈ d.support, (v i) ^ (d i)| = ∏ i ∈ d.support, |(v i) ^ (d i)| := by rw [Finset.abs_prod]
          _ = ∏ i ∈ d.support, |v i| ^ (d i) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            rw [abs_pow]
          _ ≤ ∏ i ∈ d.support, H ^ (d i) := by
            refine Finset.prod_le_prod (fun i hi => ?_) (fun i hi => ?_)
            · exact pow_nonneg (abs_nonneg _) _
            · exact pow_le_pow_left₀ (abs_nonneg _) (hv i) (d i)
          _ = H ^ (∑ i ∈ d.support, d i) := Finset.prod_pow_eq_pow_sum _ _ _
          _ ≤ H ^ p.totalDegree := pow_le_pow_right₀ hH (MvPolynomial.le_totalDegree hd)
      calc
        |(p.coeff d) * (∏ i ∈ d.support, (v i) ^ (d i))|
            = |p.coeff d| * |∏ i ∈ d.support, (v i) ^ (d i)| := by rw [abs_mul]
        _ ≤ |p.coeff d| * H ^ p.totalDegree :=
          mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
    _ = (∑ d ∈ p.support, |p.coeff d|) * H ^ p.totalDegree := by rw [Finset.sum_mul]

-- ---------------------------------------------------------------
-- 2. agreement of the three incarnations of DD(u)
-- ---------------------------------------------------------------

/-- `ddEvalInt` (MvPolynomial evaluation of `ddPoly` at the cast integer vector) is the
same as the concrete ℚ-double-discriminant `concDD n (uQ u)` (DoubleDisc). -/
lemma ddEvalInt_eq_concDD (n : ℕ) (hn : 2 ≤ n) (u : Fin (n - 1) → ℤ) :
    ddEvalInt n u = concDD n (uQ u) := by
  unfold ddEvalInt
  change MvPolynomial.eval (uQ u) (ddPoly n) = concDD n (uQ u)
  exact ddPoly_eval_concDD n hn (uQ u)

/-- The integer double discriminant `concDDZ n u : ℤ` (DDFamInt), cast to ℚ, equals the
ℚ-concrete double discriminant `concDD n (uQ u)`.  (Outer `Disc_t` commutes with the
coefficient map ℤ ↪ ℚ because `P_u` has degree `n−1` with nonzero leading coefficient
`± nⁿ`.) -/
lemma concDDZ_cast_eq_concDD (n : ℕ) (hn : 2 ≤ n) (u : Fin (n - 1) → ℤ) :
    (concDDZ n u : ℚ) = concDD n (uQ u) := by
  classical
  let ι : ℤ →+* ℚ := Int.castRingHom ℚ
  have hnd := (concInnerZ_natDegree_coeff n hn u).1
  have hlc := (concInnerZ_natDegree_coeff n hn u).2
  have hlcq0 : (concInnerZ n u).coeff (n - 1) ≠ 0 := by
    rw [hlc]
    exact mul_ne_zero (pow_ne_zero (n * (n - 1) / 2) (by norm_num))
      (pow_ne_zero n (by exact_mod_cast (by omega : n ≠ 0)))
  have hlc0 : ((concInnerZ n u).coeff (n - 1) : ℚ) ≠ 0 := by
    exact_mod_cast hlcq0
  have hdeg0 : ((concInnerZ n u).map ι).natDegree = (concInnerZ n u).natDegree := by
    refine Commons.RingTheory.Polynomial.natDegree_map_eq_of_lc_ne_zero ι (p := concInnerZ n u) ?_
    rw [Polynomial.leadingCoeff, hnd]
    exact hlc0
  have hR5 := Commons.RingTheory.Polynomial.discr_map_of_natDegree (R := ℤ) (S := ℚ) ι
    (p := concInnerZ n u) hdeg0
  calc
    (concDDZ n u : ℚ) = ι (Polynomial.discr (concInnerZ n u)) := by
      simp [concDDZ, ι]
    _ = Polynomial.discr ((concInnerZ n u).map ι) := hR5
    _ = Polynomial.discr (concInner n (uQ u)) := by
      rw [concInnerZ_map_conc n (by omega : 1 ≤ n) u]
    _ = concDD n (uQ u) := by rfl

-- ---------------------------------------------------------------
-- 3. the box height bound
-- ---------------------------------------------------------------

/-- ℓ¹ norm of the coefficient vector of `ddPoly n` (a constant depending only on `n`). -/
def ddSumAbs (n : ℕ) : ℚ := (ddPoly n).support.sum fun d => |(ddPoly n).coeff d|

/-- **Case III box height bound.** For `H ≥ 1` and upper coefficients `u` bounded by
`H`, the double discriminant satisfies
`|concDDZ n u| ≤ ddSumAbs n · H^(totalDegree (ddPoly n))`
(where both displayed constants depend only on `n`).  Hence `|DD(u)|` grows at most
polynomially in `H` with a fixed exponent. -/
theorem concDDZ_abs_le (n H : ℕ) (hn : 3 ≤ n) (hH : 1 ≤ H) (u : Fin (n - 1) → ℤ)
    (hu : ∀ i, |u i| ≤ (H : ℤ)) :
    (|concDDZ n u| : ℚ) ≤ ddSumAbs n * (H : ℚ) ^ (ddPoly n).totalDegree := by
  classical
  have hv : ∀ i : Fin (n - 1), |(uQ u i)| ≤ (H : ℚ) := by
    intro i
    change |(u i : ℚ)| ≤ (H : ℚ)
    exact_mod_cast hu i
  have hb := mvEval_abs_le (ddPoly n) (uQ u) (H : ℚ) (by exact_mod_cast hH) hv
  have h1 : |ddEvalInt n u| ≤ ddSumAbs n * (H : ℚ) ^ (ddPoly n).totalDegree := by
    dsimp [ddEvalInt, uQ, ddSumAbs]
    exact hb
  have h2 : (|concDDZ n u| : ℚ) = |ddEvalInt n u| := by
    calc
      (|concDDZ n u| : ℚ) = |(concDDZ n u : ℚ)| := by
        rw [← Int.cast_abs (R := ℚ)]
      _ = |concDD n (uQ u)| := by rw [concDDZ_cast_eq_concDD n (by omega : 2 ≤ n) u]
      _ = |ddEvalInt n u| := by rw [ddEvalInt_eq_concDD n (by omega : 2 ≤ n) u]
  rwa [h2]

/-- **Eventual power bound**: there exists `K` (depending only on `n`) such that for all
sufficiently large `H`, every box-bounded upper coefficient vector `u` satisfies
`|concDDZ n u| ≤ H^K`.  This is the O(H^K) box height bound that Case III's subcase
(ii) bookkeeping needs (bounded number of prime factors of `A = ∏_{p | C, p > H^{δ/2}} p`
dividing a fixed nonzero `DD(u)`). -/
theorem concDDZ_box_pow_le (n : ℕ) (hn : 3 ≤ n) :
    ∃ K : ℕ, ∀ᶠ H : ℕ in atTop, ∀ u : Fin (n - 1) → ℤ, (∀ i, |u i| ≤ (H : ℤ)) →
      (|concDDZ n u| : ℚ) ≤ (H : ℚ) ^ K := by
  classical
  let C : ℚ := ddSumAbs n
  let D : ℕ := (ddPoly n).totalDegree
  refine ⟨D + 1, ?_⟩
  rw [Filter.eventually_atTop]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, C ≤ (N : ℚ) := by
    obtain ⟨N, hN⟩ := exists_nat_gt C
    exact ⟨N, le_of_lt hN⟩
  refine ⟨max N 1, ?_⟩
  intro H hH u hu
  have hH1 : 1 ≤ H := le_trans (le_max_right N 1) hH
  have hHC : C ≤ (H : ℚ) := le_trans hN (by exact_mod_cast (le_trans (le_max_left N 1) hH))
  have hb := concDDZ_abs_le n H hn hH1 u hu
  have hCpow : C * (H : ℚ) ^ D ≤ (H : ℚ) ^ (D + 1) := by
    calc
      C * (H : ℚ) ^ D ≤ (H : ℚ) * (H : ℚ) ^ D :=
        mul_le_mul_of_nonneg_right hHC (pow_nonneg (by positivity : 0 ≤ (H : ℚ)) D)
      _ = (H : ℚ) ^ (D + 1) := by rw [pow_succ]; ring
  dsimp [C, D] at hb hCpow ⊢
  exact le_trans hb hCpow


/-- Real-cast form of the eventual power bound (used when working with ℝ-valued
asymptotics): `|concDDZ n u| ≤ H^K` as reals for all large H and all box-bounded u. -/
theorem concDDZ_box_pow_le_real (n : ℕ) (hn : 3 ≤ n) :
    ∃ K : ℕ, ∀ᶠ H : ℕ in atTop, ∀ u : Fin (n - 1) → ℤ, (∀ i, |u i| ≤ (H : ℤ)) →
      (|concDDZ n u| : ℝ) ≤ (H : ℝ) ^ K := by
  obtain ⟨K, hK⟩ := concDDZ_box_pow_le n hn
  refine ⟨K, ?_⟩
  rw [Filter.eventually_atTop] at hK ⊢
  obtain ⟨N, hN⟩ := hK
  refine ⟨N, ?_⟩
  intro H hH u hu
  exact_mod_cast hN H hH u hu

end

end Submission.Vdw

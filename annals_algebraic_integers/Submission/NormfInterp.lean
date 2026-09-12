import Submission.ThreePages
import Submission.RemezReal
import Submission.WnormShift
import Submission.Quantile
import Submission.Contracts
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

/-!
# Interpolation bound on the n-norm (`eq:normf_interp`)

GOAL (Smith, GON.tex, proof of `prop:Hilbert`, `eq:normf_interp`,
specialised): for `n ≥ 2`, every real polynomial `P` of degree `≤ n`
satisfies

    ‖P‖_n  ≤  n^C · max_{1 ≤ k ≤ n+1} |P(α_k)| / |P_{n+1,μ}'(α_k)|

where `α_k = Quantile.alpha (n+1) k` are the (distinct, real, in
`(aSerre,bSerre)`) roots of the approximating polynomial
`P_{n+1,μ} = ThreePages.approxPoly (n+1) = ∏_{i∈Icc 1 (n+1)} (X − C α_i)`
and `‖·‖_n = Contracts.wnorm n` (weighted n-norm, REAL polynomials).

## Proof route (paper; each ingredient is VERIFIED — cite them)
1. **Lagrange decomposition.**  The polynomials
   `P_k := P_{n+1,μ}/(X − C(α_k))` (degree `n`, exact division since `α_k`
   is a root) form a basis of the degree-≤-n real polynomials, and
   `P_k(α_k) = P_{n+1,μ}'.eval (α_k)` (derivative, product rule — roots are
   simple because quantiles are distinct: `Quantile.alpha_strict_mono`).
   Lagrange's formula: for every real `P` with `P.natDegree ≤ n`,
   `P = ∑_{k ∈ Icc 1 (n+1)} (P.eval(α_k)/P_k(α_k)) · P_k`
   (both sides have degree ≤ n and agree at the `n+1` distinct points
   `α_k`).  You may use Mathlib interpolation lemmas
   (`Polynomial.interpolate`? `Polynomial.eq_of_...`) or prove by
   `P − ∑ c_k P_k` has `n+1` roots and degree ≤ n hence is the zero
   polynomial (use `Polynomial.eq_zero_of_degree_lt_of_eval_eq_zero` or
   `Polynomial.rootMultiplicity`/`roots` counting: a nonzero polynomial of
   degree ≤ n has at most n roots over a field — Mathlib has
   `Polynomial.card_roots`/`Polynomial.eq_zero_of_...`; note the `α_k` are
   pairwise distinct: `Quantile.alpha_strict_mono (n:=n+1)`).
   Define `Pk (n k : ℕ) : Polynomial ℝ := approxPoly (n+1) / (X − C(alpha (n+1) k))`
   (division by a factor that divides exactly — use
   `Polynomial.dvd_iff_isRoot`/`Polynomial.X_sub_C_dvd` style to justify,
   or state the needed identity as `approxPoly (n+1) = (X − C(α_k))·Pk n k`
   and obtain `Pk` by choosing a witness of divisibility).
2. **Norm of `P_k`.**  `RemezReal.weighted_remez_real` applied to
   `P := approxPoly (n+1)` (degree `n+1`, exponent `N := n+1`) with root
   `α_k ∈ Icc aSerre bSerre` gives
   `‖P_k‖_{n+1} ≤ (2·(n+1))^{C_r} · ‖approxPoly (n+1)‖_{n+1}`;
   `ThreePages.approx_norm_bound` (with `n ↦ n+1`) gives
   `‖approxPoly (n+1)‖_{n+1} ≤ (n+1)^{C_a}`; and
   `WnormShift.wnorm_le_succ (k:=n)` gives `‖P_k‖_n ≤ e^{K}·‖P_k‖_{n+1}`.
   Hence `‖P_k‖_n ≤ n^{C₁}` for a fixed `C₁` (absorb the fixed `e^K`, the
   `2`'s and the `(n+1)/n` ratios: `n ≥ 2`).
3. **Conclusion.**  From (1),
   `‖P‖_n ≤ ∑_k |c_k|·‖P_k‖_n ≤ (n+1)·n^{C₁}·max_k |c_k|` where
   `c_k = P(α_k)/P_k(α_k) = P.eval(α_k)/(approxPoly(n+1)).derivative.eval(α_k)`
   (use `wnorm_add_le` iterated or triangle inequality over the finite sum —
   `WnormToolkit.wnorm_add_le`); bound `(n+1)·n^{C₁} ≤ n^{C₂}` for fixed
   `C₂` and `n ≥ 2`.  So with the max defined as the `sSup` over the finite
   set `k ∈ Icc 1 (n+1)` of the ratios (all finite; denominators nonzero —
   prove `(approxPoly (n+1)).derivative.eval (α_k) ≠ 0` from the product
   formula and distinct roots), get the stated inequality.

## Exact statement to prove
Use `alpha := Submission.Quantile.alpha`, `approxPoly :=
Submission.ThreePages.approxPoly`, `wnorm := Submission.Contracts.wnorm`.
The ratio set `{ |P(α_k)| / |P_{n+1,μ}'(α_k)| : 1 ≤ k ≤ n+1 }` is finite and
nonempty; take its `sSup` (the child may introduce the image-set directly in
the proof; state the theorem with an explicit `let`/image-sSup as below).

Everything must be hole-free with axioms only propext/Quot.sound/
Classical.choice.  Read `Submission/ThreePages.lean`,
`Submission/Quantile.lean`, `Submission/RemezReal.lean`,
`Submission/WnormShift.lean`, `Submission/WnormToolkit.lean` for exact
names.  Keep the declaration EXACTLY as written; add helpers freely in this
file (namespace `Submission.NormfInterp`).
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators
open Polynomial

namespace Submission.NormfInterp

open Submission.Quantile
open Submission.ThreePages
open Submission.Contracts

/-- Lagrange denominator polynomial `P_k := P_{n+1,μ}/(X − C(α_k))`. -/
noncomputable def Pk (n k : ℕ) : Polynomial ℝ :=
  approxPoly (n + 1) / (Polynomial.X - Polynomial.C (alpha (n + 1) k))

/-- Cardinality of the node set `Icc 1 (n+1)`. -/
lemma card_nodes (n : ℕ) : (Finset.Icc 1 (n + 1)).card = n + 1 := by
  rw [Nat.card_Icc]
  omega

/-- Quantile values at distinct nodes are distinct. -/
lemma alpha_nodes_ne {n i j : ℕ} (hi : i ∈ Finset.Icc 1 (n + 1))
    (hj : j ∈ Finset.Icc 1 (n + 1)) (hij : i ≠ j) :
    alpha (n + 1) i ≠ alpha (n + 1) j := by
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hin : i ≤ n + 1 := (Finset.mem_Icc.mp hi).2
  have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjn : j ≤ n + 1 := (Finset.mem_Icc.mp hj).2
  have hn : 1 ≤ n + 1 := by omega
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · intro heq
    have hst : alpha (n + 1) i < alpha (n + 1) j :=
      alpha_strict_mono (n := n + 1) hn hi1 hlt hjn
    rw [heq] at hst
    exact (lt_irrefl _) hst
  · intro heq
    have hst : alpha (n + 1) j < alpha (n + 1) i :=
      alpha_strict_mono (n := n + 1) hn hj1 hgt hin
    rw [← heq] at hst
    exact (lt_irrefl _) hst

/-- `alpha (n+1)` is injective on the node finset. -/
lemma alpha_injOn_nodes (n : ℕ) :
    Set.InjOn (alpha (n + 1)) (Finset.Icc 1 (n + 1) : Set ℕ) := by
  intro i hi j hj heq
  by_contra hne
  exact (alpha_nodes_ne (n := n) hi hj hne) heq

/-- Every node is a root of the approximating polynomial. -/
lemma approx_eval_zero {n k : ℕ} (hk : k ∈ Finset.Icc 1 (n + 1)) :
    (approxPoly (n + 1)).eval (alpha (n + 1) k) = 0 := by
  rw [approxPoly_eval]
  exact Finset.prod_eq_zero hk (by simp)

/-- The linear factor at a node divides the approximating polynomial; the
explicit quotient is `Pk n k`. -/
lemma Pk_mul {n k : ℕ} (hk : k ∈ Finset.Icc 1 (n + 1)) :
    (Polynomial.X - Polynomial.C (alpha (n + 1) k)) * Pk n k = approxPoly (n + 1) := by
  unfold Pk
  exact (Polynomial.mul_div_eq_iff_isRoot).mpr (by
    simpa [Polynomial.IsRoot] using approx_eval_zero (n := n) hk)

/-- `Pk n k` is nonzero. -/
lemma Pk_ne_zero {n k : ℕ} (hk : k ∈ Finset.Icc 1 (n + 1)) : Pk n k ≠ 0 := by
  intro hz
  have hG : approxPoly (n + 1) = 0 := by
    rw [← Pk_mul (n := n) hk, hz, mul_zero]
  have hmonic := approxPoly_monic (n + 1) (by omega : 1 ≤ n + 1)
  exact hmonic.ne_zero hG

/-- Degree of the Lagrange denominator polynomial. -/
lemma Pk_natDegree {n k : ℕ} (hk : k ∈ Finset.Icc 1 (n + 1)) : (Pk n k).natDegree = n := by
  have hdegG : (approxPoly (n + 1)).natDegree = n + 1 :=
    approxPoly_natDegree (n + 1) (by omega : 1 ≤ n + 1)
  have hf0 : (Polynomial.X - Polynomial.C (alpha (n + 1) k)) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero (alpha (n + 1) k)
  have hmul := Polynomial.natDegree_mul hf0 (Pk_ne_zero (n := n) hk)
  rw [Pk_mul (n := n) hk, hdegG, Polynomial.natDegree_X_sub_C] at hmul
  omega

/-- Evaluation of `Pk n k` at its own node equals the derivative of the
approximating polynomial there. -/
lemma Pk_eval_self {n k : ℕ} (hk : k ∈ Finset.Icc 1 (n + 1)) :
    (Pk n k).eval (alpha (n + 1) k) =
      (approxPoly (n + 1)).derivative.eval (alpha (n + 1) k) := by
  exact RemezReal.q_alpha_eq (P := approxPoly (n + 1)) (Q := Pk n k)
    (α := alpha (n + 1) k) (Pk_mul (n := n) hk).symm

/-- Evaluation of `Pk n k` at another node vanishes. -/
lemma Pk_eval_other_zero {n k j : ℕ} (hk : k ∈ Finset.Icc 1 (n + 1))
    (hj : j ∈ Finset.Icc 1 (n + 1)) (hkj : k ≠ j) :
    (Pk n k).eval (alpha (n + 1) j) = 0 := by
  have hfac := Pk_mul (n := n) hk
  have hG : (approxPoly (n + 1)).eval (alpha (n + 1) j) = 0 :=
    approx_eval_zero (n := n) hj
  have hdiff : alpha (n + 1) j - alpha (n + 1) k ≠ 0 :=
    sub_ne_zero.mpr (alpha_nodes_ne (n := n) hj hk hkj.symm)
  have hmain : (alpha (n + 1) j - alpha (n + 1) k) * (Pk n k).eval (alpha (n + 1) j) = 0 := by
    calc
      (alpha (n + 1) j - alpha (n + 1) k) * (Pk n k).eval (alpha (n + 1) j)
          = ((Polynomial.X - Polynomial.C (alpha (n + 1) k)) * Pk n k).eval (alpha (n + 1) j) := by
            simp
      _ = (approxPoly (n + 1)).eval (alpha (n + 1) j) := by rw [hfac]
      _ = 0 := hG
  exact (mul_eq_zero.mp hmain).resolve_left hdiff


/-- The product of the linear factors at all nodes except `k`. -/
noncomputable def PkProd (n k : ℕ) : Polynomial ℝ :=
  ∏ j ∈ (Finset.Icc 1 (n + 1)).erase k,
    (Polynomial.X - Polynomial.C (alpha (n + 1) j))

/-- `Pk n k` equals the erasure product (the other nodes' factors). -/
lemma Pk_eq_PkProd {n k : ℕ} (hk : k ∈ Finset.Icc 1 (n + 1)) :
    Pk n k = PkProd n k := by
  have hfac0 : (Polynomial.X - Polynomial.C (alpha (n + 1) k)) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero (alpha (n + 1) k)
  have hprod : (Polynomial.X - Polynomial.C (alpha (n + 1) k)) * PkProd n k =
      approxPoly (n + 1) := by
    unfold PkProd approxPoly
    rw [Finset.mul_prod_erase (s := Finset.Icc 1 (n + 1))
      (f := fun x => Polynomial.X - Polynomial.C (alpha (n + 1) x)) hk]
  -- (X - C α_k) * Pk n k = (X - C α_k) * PkProd n k
  apply mul_left_cancel₀ hfac0
  rw [Pk_mul (n := n) hk]
  exact hprod.symm

/-- The erasure product does not vanish at the remaining node. -/
lemma PkProd_self_ne_zero {n k : ℕ} (hk : k ∈ Finset.Icc 1 (n + 1)) :
    (PkProd n k).eval (alpha (n + 1) k) ≠ 0 := by
  unfold PkProd
  rw [Polynomial.eval_prod]
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  have hmem : j ∈ Finset.Icc 1 (n + 1) := (Finset.mem_erase.mp hj).2
  have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
  have hne : alpha (n + 1) k ≠ alpha (n + 1) j :=
    (alpha_nodes_ne (n := n) hmem hk hjk).symm
  simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_ne_zero.mpr hne]

/-- `Pk n k` does not vanish at its own node. -/
lemma Pk_self_ne_zero {n k : ℕ} (hk : k ∈ Finset.Icc 1 (n + 1)) :
    (Pk n k).eval (alpha (n + 1) k) ≠ 0 := by
  rw [Pk_eq_PkProd hk]
  exact PkProd_self_ne_zero hk

/-- The derivative of the approximating polynomial does not vanish at a node
(roots are simple). -/
lemma derivative_eval_ne_zero {n k : ℕ} (hk : k ∈ Finset.Icc 1 (n + 1)) :
    (approxPoly (n + 1)).derivative.eval (alpha (n + 1) k) ≠ 0 := by
  rw [← Pk_eval_self (n := n) hk]
  exact Pk_self_ne_zero hk

/-- Lagrange coefficient `P(α_k)/P_k(α_k)`. -/
noncomputable def interpCoeff (n : ℕ) (P : Polynomial ℝ) (k : ℕ) : ℝ :=
  P.eval (alpha (n + 1) k) / (Pk n k).eval (alpha (n + 1) k)

/-- The degree-`≤ n` Lagrange interpolant of `P` at the nodes. -/
noncomputable def interpPoly (n : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.Icc 1 (n + 1), interpCoeff n P k • Pk n k

/-- Sum of polynomials with `natDegree ≤ n` again has `natDegree ≤ n`. -/
lemma natDegree_sum_le_of_le {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℝ)
    {n : ℕ} (h : ∀ i ∈ s, (f i).natDegree ≤ n) :
    (∑ i ∈ s, f i).natDegree ≤ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
      rw [Finset.sum_insert has]
      exact (Polynomial.natDegree_add_le _ _).trans
        (max_le (h a (by simp)) (ih (fun i hi => h i (by simp [hi]))))

/-- The interpolant has degree `≤ n`. -/
lemma interpPoly_natDegree_le (n : ℕ) (P : Polynomial ℝ) :
    (interpPoly n P).natDegree ≤ n := by
  unfold interpPoly
  refine natDegree_sum_le_of_le (Finset.Icc 1 (n + 1)) (fun k => interpCoeff n P k • Pk n k) ?_
  intro k hk
  exact le_trans (Polynomial.natDegree_smul_le _ _) (le_of_eq (Pk_natDegree (n := n) hk))

/-- The interpolant agrees with `P` at every node. -/
lemma interpPoly_eval_node {n j : ℕ} {P : Polynomial ℝ}
    (hj : j ∈ Finset.Icc 1 (n + 1)) :
    (interpPoly n P).eval (alpha (n + 1) j) = P.eval (alpha (n + 1) j) := by
  unfold interpPoly
  rw [Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single j]
  · have hd : (Pk n j).eval (alpha (n + 1) j) ≠ 0 := Pk_self_ne_zero (n := n) hj
    simp [interpCoeff, smul_eq_mul]
    field_simp [hd]
  · intro b hb hbj
    have hz : (Pk n b).eval (alpha (n + 1) j) = 0 :=
      Pk_eval_other_zero (n := n) (hk := hb) (hj := hj) (hkj := hbj)
    simp [smul_eq_mul, hz]
  · intro hnj
    exfalso
    exact hnj hj

/-- Lagrange's formula: a degree-`≤ n` polynomial equals its interpolant at
the `n+1` distinct quantile nodes. -/
lemma lagrange_identity {n : ℕ} {P : Polynomial ℝ} (hdeg : P.natDegree ≤ n) :
    P = interpPoly n P := by
  let s : Finset ℕ := Finset.Icc 1 (n + 1)
  have hdegQ : (interpPoly n P).natDegree ≤ n := interpPoly_natDegree_le n P
  have hdegsub : (P - interpPoly n P).natDegree ≤ n := by
    exact le_trans (Polynomial.natDegree_sub_le _ _) (by
      simp only [max_le_iff]
      exact ⟨hdeg, hdegQ⟩)
  have hdeglt : (P - interpPoly n P).degree < ((Finset.Icc 1 (n + 1)).card : WithBot ℕ) := by
    have hlt : (P - interpPoly n P).natDegree < (Finset.Icc 1 (n + 1)).card := by
      rw [card_nodes n]
      omega
    have h1 : (P - interpPoly n P).degree ≤ ↑((P - interpPoly n P).natDegree) :=
      Polynomial.degree_le_natDegree
    exact lt_of_le_of_lt h1 (WithBot.coe_lt_coe.mpr hlt)
  exact Polynomial.eq_of_degree_sub_lt_of_eval_index_eq
    (s := Finset.Icc 1 (n + 1)) (v := fun k : ℕ => alpha (n + 1) k)
    (hvs := alpha_injOn_nodes n) hdeglt (by
      intro k hk
      exact (interpPoly_eval_node (n := n) (j := k) (P := P) hk).symm)


/-! ## Ratio set and basic real inequalities -/

/-- The value `|P(α_k)| / |P_{n+1,μ}'(α_k)|` at a node `k`. -/
noncomputable def ratioVal (n : ℕ) (P : Polynomial ℝ) (k : ℕ) : ℝ :=
  |P.eval (alpha (n + 1) k)| /
    |(approxPoly (n + 1)).derivative.eval (alpha (n + 1) k)|

/-- The set of normalized evaluations at all nodes `1 ≤ k ≤ n+1`. -/
noncomputable def ratioSet (n : ℕ) (P : Polynomial ℝ) : Set ℝ :=
  (fun k : ℕ => ratioVal n P k) '' Set.Icc 1 (n + 1)

/-- `n + 1 ≤ n²` for real `n ≥ 2`. -/
lemma np1_le_n2 {n : ℝ} (hn : 2 ≤ n) : n + 1 ≤ n ^ (2 : ℝ) := by
  have hn0 : 0 ≤ n := by linarith
  have h2n : (2 : ℝ) * n ≤ n ^ (2 : ℕ) := by
    calc
      (2 : ℝ) * n = n * 2 := by ring
      _ ≤ n * n := by exact mul_le_mul_of_nonneg_left (by linarith) hn0
      _ = n ^ (2 : ℕ) := by ring
  have h2n' : n + 1 ≤ (2 : ℝ) * n := by nlinarith
  calc
    n + 1 ≤ (2 : ℝ) * n := h2n'
    _ ≤ n ^ (2 : ℕ) := h2n
    _ = n ^ (2 : ℝ) := (Real.rpow_natCast n (2 : ℕ)).symm

/-- `2(n+1) ≤ n³` for real `n ≥ 2`. -/
lemma two_np1_le_n3 {n : ℝ} (hn : 2 ≤ n) : 2 * (n + 1) ≤ n ^ (3 : ℝ) := by
  have hn0 : 0 ≤ n := by linarith
  have hsq : (4 : ℝ) ≤ n ^ (2 : ℕ) := by
    have hz : 0 ≤ (n - 2) * (n + 2) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  have h4n : (4 : ℝ) * n ≤ n ^ (3 : ℕ) := by
    calc
      (4 : ℝ) * n = n * 4 := by ring
      _ ≤ n * n ^ (2 : ℕ) := by exact mul_le_mul_of_nonneg_left hsq hn0
      _ = n ^ (3 : ℕ) := by ring
  calc
    2 * (n + 1) = 2 * n + 2 := by ring
    _ ≤ 4 * n := by nlinarith
    _ ≤ n ^ (3 : ℕ) := h4n
    _ = n ^ (3 : ℝ) := (Real.rpow_natCast n (3 : ℕ)).symm

/-- Absorption chain: the fixed-power bound for the interpolant numerators. -/
lemma remez_norm_chain {m : ℝ} (hm : 2 ≤ m) (Cr Ca K : ℝ)
    (hCr : 0 ≤ Cr) (hCa : 0 ≤ Ca) (hK : 0 ≤ K) :
    (2 * (m + 1)) ^ Cr * (Real.exp K * (m + 1) ^ Ca) ≤
      m ^ (3 * Cr + 2 * Ca + K / Real.log 2) := by
  have hm0 : 0 < m := by linarith
  have hm0le : 0 ≤ m := le_of_lt hm0
  have hA0 : 0 ≤ (2 * (m + 1)) := by positivity
  have hB0 : 0 ≤ (m + 1) := by positivity
  have h1a : (2 * (m + 1)) ^ Cr ≤ (m ^ (3 : ℝ)) ^ Cr := by
    exact Real.rpow_le_rpow hA0 (two_np1_le_n3 (n := m) hm) hCr
  have h1b : (m ^ (3 : ℝ)) ^ Cr = m ^ (3 * Cr) := by
    rw [Real.rpow_mul hm0le (3 : ℝ) Cr]
  have h1 : (2 * (m + 1)) ^ Cr ≤ m ^ (3 * Cr) := by
    calc
      (2 * (m + 1)) ^ Cr ≤ (m ^ (3 : ℝ)) ^ Cr := h1a
      _ = m ^ (3 * Cr) := h1b
  have h2a : (m + 1) ^ Ca ≤ (m ^ (2 : ℝ)) ^ Ca := by
    exact Real.rpow_le_rpow hB0 (np1_le_n2 (n := m) hm) hCa
  have h2b : (m ^ (2 : ℝ)) ^ Ca = m ^ (2 * Ca) := by
    rw [Real.rpow_mul hm0le (2 : ℝ) Ca]
  have h2 : (m + 1) ^ Ca ≤ m ^ (2 * Ca) := by
    calc
      (m + 1) ^ Ca ≤ (m ^ (2 : ℝ)) ^ Ca := h2a
      _ = m ^ (2 * Ca) := h2b
  have hKb : Real.exp K ≤ m ^ (K / Real.log 2) := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogn : 0 < Real.log m := Real.log_pos (by linarith)
    have hln : Real.log 2 ≤ Real.log m := Real.log_le_log (by norm_num) hm
    have hdiv0 : 0 ≤ K / Real.log 2 := div_nonneg hK (le_of_lt hlog2)
    calc
      Real.exp K = Real.exp ((K / Real.log 2) * Real.log 2) := by
        field_simp [ne_of_gt hlog2]
      _ ≤ Real.exp ((K / Real.log 2) * Real.log m) := by
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hln hdiv0)
      _ = Real.exp (Real.log m * (K / Real.log 2)) := by rw [mul_comm]
      _ = m ^ (K / Real.log 2) := by
        exact (Real.rpow_def_of_pos (x := m) hm0 (K / Real.log 2)).symm
  have hEK0 : 0 ≤ Real.exp K := Real.exp_nonneg K
  have hB1 : 0 ≤ (m + 1) ^ Ca := Real.rpow_nonneg hB0 Ca
  calc
    (2 * (m + 1)) ^ Cr * (Real.exp K * (m + 1) ^ Ca) =
        (2 * (m + 1)) ^ Cr * Real.exp K * (m + 1) ^ Ca := by ring
    _ ≤ m ^ (3 * Cr) * Real.exp K * (m + 1) ^ Ca := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hEK0) hB1
    _ ≤ m ^ (3 * Cr) * Real.exp K * m ^ (2 * Ca) := by
          exact mul_le_mul_of_nonneg_left h2 (mul_nonneg (Real.rpow_nonneg hm0le _) hEK0)
    _ = (m ^ (3 * Cr) * m ^ (2 * Ca)) * Real.exp K := by ring
    _ = m ^ (3 * Cr + 2 * Ca) * Real.exp K := by
          rw [← Real.rpow_add hm0 (3 * Cr) (2 * Ca)]
    _ ≤ m ^ (3 * Cr + 2 * Ca) * m ^ (K / Real.log 2) := by
          exact mul_le_mul_of_nonneg_left hKb (Real.rpow_nonneg hm0le _)
    _ = m ^ (3 * Cr + 2 * Ca + K / Real.log 2) := by
          rw [← Real.rpow_add hm0]

/-- `wnorm` of the zero polynomial is zero. -/
lemma wnorm_zero (k : ℕ) : wnorm k (0 : Polynomial ℝ) = 0 := by
  apply le_antisymm
  · apply WnormToolkit.wnorm_sSup_le
    intro x hx
    simp
  · exact WnormToolkit.wnorm_nonneg k (0 : Polynomial ℝ)

/-- Sub-additivity over finite sums. -/
lemma wnorm_sum_le {ι : Type*} (k : ℕ) (s : Finset ι) (f : ι → Polynomial ℝ) :
    wnorm k (∑ i ∈ s, f i) ≤ ∑ i ∈ s, wnorm k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [wnorm_zero]
  | insert a s has ih =>
      rw [Finset.sum_insert has]
      calc
        wnorm k (f a + ∑ i ∈ s, f i) ≤ wnorm k (f a) + wnorm k (∑ i ∈ s, f i) :=
          WnormToolkit.wnorm_add_le k (f a) (∑ i ∈ s, f i)
        _ ≤ wnorm k (f a) + ∑ i ∈ s, wnorm k (f i) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            (add_le_add_left ih (wnorm k (f a)))
        _ = ∑ i ∈ insert a s, wnorm k (f i) := by
          rw [Finset.sum_insert has]

/-- The ratio set is bounded above (it is the finite image of the node set). -/
lemma ratioSet_bddAbove (n : ℕ) (P : Polynomial ℝ) : BddAbove (ratioSet n P) := by
  unfold ratioSet
  exact ((Set.finite_Icc 1 (n + 1) : (Set.Icc 1 (n + 1) : Set ℕ).Finite).image
    (fun k : ℕ => ratioVal n P k)).bddAbove

/-- Every node ratio is bounded by the supremum of the ratio set. -/
lemma ratio_le_sSup {n k : ℕ} (P : Polynomial ℝ) (hk : k ∈ Finset.Icc 1 (n + 1)) :
    ratioVal n P k ≤ sSup (ratioSet n P) := by
  apply le_csSup (ratioSet_bddAbove n P)
  unfold ratioSet
  refine ⟨k, ?_, rfl⟩
  exact Set.mem_Icc.mpr (Finset.mem_Icc.mp hk)

/-- The ratio set has nonnegative elements, so its supremum is nonnegative. -/
lemma sSup_ratio_nonneg (n : ℕ) (P : Polynomial ℝ) : 0 ≤ sSup (ratioSet n P) := by
  refine Real.sSup_nonneg ?_
  intro y hy
  rcases hy with ⟨k, hk, rfl⟩
  unfold ratioVal
  exact div_nonneg (abs_nonneg _) (abs_nonneg _)

/-- The Lagrange coefficient's absolute value is the node ratio. -/
lemma interpCoeff_abs {n k : ℕ} (P : Polynomial ℝ) (hk : k ∈ Finset.Icc 1 (n + 1)) :
    |interpCoeff n P k| = ratioVal n P k := by
  unfold interpCoeff ratioVal
  rw [Pk_eval_self (n := n) hk]
  rw [abs_div]

/-- The weighted n-norm of a Lagrange numerator is bounded by a fixed power
of `n` (Remez division + the approximating norm + the exponent shift). -/
lemma Pk_wnorm_le : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ,
    k ∈ Finset.Icc 1 (n + 1) → wnorm n (Pk n k) ≤ (n : ℝ) ^ C := by
  rcases RemezReal.weighted_remez_real with ⟨Cr, hCr, hrem⟩
  rcases approx_norm_bound with ⟨Ca, hCa, happ⟩
  let K : ℝ := WnormShift.Kbound
  let C : ℝ := 3 * Cr + 2 * Ca + K / Real.log 2
  refine ⟨C, ?_, ?_⟩
  · have hK0 : 0 ≤ K := WnormShift.Kbound_nonneg
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hd : 0 ≤ K / Real.log 2 := div_nonneg hK0 (le_of_lt hlog2)
    dsimp [C, K]
    nlinarith
  · intro n hn k hk
    have hdegG : (approxPoly (n + 1)).natDegree = n + 1 :=
      approxPoly_natDegree (n + 1) (by omega : 1 ≤ n + 1)
    have hmemIcc : alpha (n + 1) k ∈
        Set.Icc Submission.SerreExample.aSerre Submission.SerreExample.bSerre :=
      alpha_mem_Icc (n := n + 1) (by omega : 1 ≤ n + 1) (Finset.mem_Icc.mp hk).1
        (Finset.mem_Icc.mp hk).2
    have hroot : (approxPoly (n + 1)).eval (alpha (n + 1) k) = 0 :=
      approx_eval_zero (n := n) hk
    rcases hrem n (n + 1) (by omega : 1 ≤ n + 1) (approxPoly (n + 1)) hdegG
      (alpha (n + 1) k) hmemIcc hroot with ⟨Q, hfac, hbnd⟩
    have hQeq : Q = Pk n k := by
      apply mul_left_cancel₀ (Polynomial.X_sub_C_ne_zero (alpha (n + 1) k))
      calc
        (Polynomial.X - Polynomial.C (alpha (n + 1) k)) * Q
            = approxPoly (n + 1) := hfac.symm
        _ = (Polynomial.X - Polynomial.C (alpha (n + 1) k)) * Pk n k :=
              (Pk_mul (n := n) hk).symm
    have hmax : max n (n + 1) = n + 1 := Nat.max_eq_right (by omega)
    have hbnd'' : wnorm n (Pk n k) ≤
        ((2 * (n + 1 : ℕ) : ℕ) : ℝ) ^ Cr * wnorm n (approxPoly (n + 1)) := by
      have hbnd' : wnorm n (Pk n k) ≤
          ((2 * max n (n + 1) : ℕ) : ℝ) ^ Cr * wnorm n (approxPoly (n + 1)) := by
        rw [← hQeq]
        exact hbnd
      simpa [hmax] using hbnd'
    have hshift : wnorm n (approxPoly (n + 1)) ≤
        Real.exp K * wnorm (n + 1) (approxPoly (n + 1)) := by
      dsimp [K]
      exact WnormShift.wnorm_le_succ n (approxPoly (n + 1))
    have happn : wnorm (n + 1) (approxPoly (n + 1)) ≤ ((n + 1 : ℕ) : ℝ) ^ Ca :=
      happ (n + 1) (by omega)
    have hA0 : 0 ≤ ((2 * (n + 1 : ℕ) : ℕ) : ℝ) ^ Cr := by positivity
    have hmain : wnorm n (Pk n k) ≤
        ((2 * (n + 1 : ℕ) : ℕ) : ℝ) ^ Cr *
          (Real.exp K * ((n + 1 : ℕ) : ℝ) ^ Ca) := by
      calc
        wnorm n (Pk n k)
            ≤ ((2 * (n + 1 : ℕ) : ℕ) : ℝ) ^ Cr * wnorm n (approxPoly (n + 1)) := hbnd''
        _ ≤ ((2 * (n + 1 : ℕ) : ℕ) : ℝ) ^ Cr *
              (Real.exp K * wnorm (n + 1) (approxPoly (n + 1))) := by
              exact mul_le_mul_of_nonneg_left hshift hA0
        _ ≤ ((2 * (n + 1 : ℕ) : ℕ) : ℝ) ^ Cr *
              (Real.exp K * ((n + 1 : ℕ) : ℝ) ^ Ca) := by
              exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left happn (Real.exp_nonneg K))
                hA0
    have hm2 : 2 ≤ (n : ℝ) := by exact_mod_cast hn
    have hcast : ((2 * (n + 1 : ℕ) : ℕ) : ℝ) = 2 * ((n : ℝ) + 1) := by simp
    have hcast2 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
    have hchain := remez_norm_chain (m := (n : ℝ)) (Cr := Cr) (Ca := Ca) (K := K)
      hm2 (le_of_lt hCr) (le_of_lt hCa) WnormShift.Kbound_nonneg
    dsimp [C]
    calc
      wnorm n (Pk n k) ≤
          ((2 * (n + 1 : ℕ) : ℕ) : ℝ) ^ Cr *
            (Real.exp K * ((n + 1 : ℕ) : ℝ) ^ Ca) := hmain
      _ = (2 * ((n : ℝ) + 1)) ^ Cr *
            (Real.exp K * ((n : ℝ) + 1) ^ Ca) := by simp [hcast, hcast2]
      _ ≤ (n : ℝ) ^ (3 * Cr + 2 * Ca + K / Real.log 2) := by
            simpa using hchain


/-- Lagrange decomposition bound: the weighted norm of `P` is at most
`(n+1)·n^{C1}` times the largest normalized node evaluation. -/
lemma interp_norm_bound {n : ℕ} (hn : 2 ≤ n) {P : Polynomial ℝ} (hdeg : P.natDegree ≤ n)
    {C1 : ℝ} (hC1n : 0 ≤ (n : ℝ) ^ C1)
    (hPk : ∀ k : ℕ, k ∈ Finset.Icc 1 (n + 1) → wnorm n (Pk n k) ≤ (n : ℝ) ^ C1) :
    wnorm n P ≤ (n : ℝ) ^ (C1 + 2) * sSup (ratioSet n P) := by
  let s : Finset ℕ := Finset.Icc 1 (n + 1)
  have hlag : P = interpPoly n P := lagrange_identity (n := n) (P := P) hdeg
  have hsup0 : 0 ≤ sSup (ratioSet n P) := sSup_ratio_nonneg n P
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hpow : (n : ℝ) ^ ((2 : ℕ) : ℝ) * (n : ℝ) ^ C1 = (n : ℝ) ^ (C1 + 2) := by
    calc
      (n : ℝ) ^ ((2 : ℕ) : ℝ) * (n : ℝ) ^ C1
          = (n : ℝ) ^ (((2 : ℕ) : ℝ) + C1) := (Real.rpow_add hnpos ((2 : ℕ) : ℝ) C1).symm
      _ = (n : ℝ) ^ (C1 + 2) := by
          congr 1
          ring
  have hle1 : ((n + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ ((2 : ℕ) : ℝ) := by
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 : 0 ≤ (n : ℝ) := by linarith
    have h2n : (2 : ℝ) * (n : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := by
      calc
        (2 : ℝ) * (n : ℝ) = (n : ℝ) * 2 := by ring
        _ ≤ (n : ℝ) * (n : ℝ) := by exact mul_le_mul_of_nonneg_left hnR hn0
        _ = (n : ℝ) ^ (2 : ℕ) := by ring
    have h2n' : (n : ℝ) + 1 ≤ (2 : ℝ) * (n : ℝ) := by nlinarith
    calc
      ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
      _ ≤ (2 : ℝ) * (n : ℝ) := h2n'
      _ ≤ (n : ℝ) ^ (2 : ℕ) := h2n
      _ = (n : ℝ) ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast (n : ℝ) (2 : ℕ)).symm
  have hmul0 : 0 ≤ (n : ℝ) ^ C1 * sSup (ratioSet n P) := mul_nonneg hC1n hsup0
  calc
    wnorm n P = wnorm n (interpPoly n P) := congrArg (wnorm n) hlag
    _ ≤ ∑ k ∈ s, wnorm n (interpCoeff n P k • Pk n k) := by
          unfold interpPoly
          exact wnorm_sum_le n s (fun k => interpCoeff n P k • Pk n k)
    _ ≤ ∑ k ∈ s, sSup (ratioSet n P) * (n : ℝ) ^ C1 := by
          apply Finset.sum_le_sum
          intro k hk
          calc
            wnorm n (interpCoeff n P k • Pk n k)
                = |interpCoeff n P k| * wnorm n (Pk n k) :=
                  WnormToolkit.wnorm_smul n (interpCoeff n P k) (Pk n k)
            _ ≤ |interpCoeff n P k| * (n : ℝ) ^ C1 := by
                  exact mul_le_mul_of_nonneg_left (hPk k hk) (abs_nonneg _)
            _ ≤ sSup (ratioSet n P) * (n : ℝ) ^ C1 := by
                  exact mul_le_mul_of_nonneg_right
                    (by
                      rw [interpCoeff_abs (n := n) (k := k) P hk]
                      exact ratio_le_sSup (n := n) (P := P) hk) hC1n
    _ = ((n + 1 : ℕ) : ℝ) * (sSup (ratioSet n P) * (n : ℝ) ^ C1) := by
          have hcard : s.card = n + 1 := by
            dsimp [s]
            exact card_nodes n
          calc
            (∑ k ∈ s, sSup (ratioSet n P) * (n : ℝ) ^ C1)
                = s.card • (sSup (ratioSet n P) * (n : ℝ) ^ C1) := by
                  rw [Finset.sum_const]
            _ = (s.card : ℝ) * (sSup (ratioSet n P) * (n : ℝ) ^ C1) := by simp [nsmul_eq_mul]
            _ = ((n + 1 : ℕ) : ℝ) * (sSup (ratioSet n P) * (n : ℝ) ^ C1) := by
                  rw [hcard]
    _ = ((n + 1 : ℕ) : ℝ) * (n : ℝ) ^ C1 * sSup (ratioSet n P) := by ring
    _ = ((n + 1 : ℕ) : ℝ) * ((n : ℝ) ^ C1 * sSup (ratioSet n P)) := by ring
    _ ≤ (n : ℝ) ^ ((2 : ℕ) : ℝ) * ((n : ℝ) ^ C1 * sSup (ratioSet n P)) := by
          exact mul_le_mul_of_nonneg_right hle1 hmul0
    _ = ((n : ℝ) ^ ((2 : ℕ) : ℝ) * (n : ℝ) ^ C1) * sSup (ratioSet n P) := by ring
    _ = (n : ℝ) ^ (C1 + 2) * sSup (ratioSet n P) := by rw [hpow]

/-- The interpolation bound stated with the ratio set. -/
lemma normf_interp_ratio :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ P : Polynomial ℝ, P.natDegree ≤ n →
      wnorm n P ≤ (n : ℝ) ^ C * sSup (ratioSet n P) := by
  rcases Pk_wnorm_le with ⟨C1, hC1, hPk⟩
  refine ⟨C1 + 2, by linarith, ?_⟩
  intro n hn P hdeg
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hC1n : 0 ≤ (n : ℝ) ^ C1 := Real.rpow_nonneg (le_of_lt hnpos) C1
  exact interp_norm_bound (n := n) (hn := hn) (P := P) (hdeg := hdeg) (C1 := C1) hC1n
    (fun k hk => hPk n hn k hk)


theorem normf_interp :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ P : Polynomial ℝ, P.natDegree ≤ n →
      wnorm n P ≤ (n : ℝ) ^ C *
        sSup ((fun k : ℕ =>
          |P.eval (alpha (n + 1) k)| /
            |(approxPoly (n + 1)).derivative.eval (alpha (n + 1) k)|) ''
          Set.Icc 1 (n + 1)) := by
  simpa [ratioSet, ratioVal] using normf_interp_ratio

end Submission.NormfInterp

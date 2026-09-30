import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (Baker–Wüstholz drive). Route design: BW = Baker–Wüstholz, Crelle 442 (1993); section and lemma numbers are BW's. Shared definitions are in Submission.Work.BW.Defs (namespace Work.BW).
Sibling nodes are dispatched in parallel, each as module Submission.Work.BW.<name> with its statement already in place: liouville_logForm, lehmer_bound, minkowski_basis, kummer_indep, logHeight_intermediate, discriminant_bound, siegel_numberField, small_relation, kummer_reduction, aux_poly, analytic_core, bw_independent, logindep_reduction. multiplicity_prop and group_reduction come later.
If your proof needs a sibling's result, IMPORT its module and use its statement. Do NOT reprove it, and do not restate it under another name. Its sorry disappears when it lands.
The constants are tight (see the notes below): do not weaken any numeric constant in your statement. If you believe the statement is false, give a concrete counterexample.

# analytic_core — BW §14–20 (p. 41–59); 10–20k lines, high risk (long, numerically tight)

**Claim.** Assume `p` satisfies (9) and (12), and `log|Λ| ≤ -9·2^rSD` (10). Then some `P` has
`PolyOut`: it is nonzero, has the degree bounds, and vanishes to order `ξT^{(I)}` along `∂*` at
`(s, α'^s)` for `0 ≤ s ≤ 2S^{(I)}`.

**Sub-lemmas.** Split this one further; each step follows the BW section named.
1. **§14 auxiliary functions.**
   * Set `f(z) = Q(z, e^{M₁},…; t)` along `zⱼ = 2^{-v}z log αⱼ`, and `g(z) = Q(z, α'^z; t)`.
   * Prove (13) `log|f(z)| ≤ ln(p) + hT* + 0.204SD/d + 1.008|z|D`.
   * Prove (14) `log|f - g| ≤ ln(p) + hT* + {0.205/d + 1.01|z|/S - 9·2^r}SD`.
   * The key inequality is `|Λz|D ≤ 0.001|z|D`, from (10).
2. **§15 algebraic estimates (product formula over `K`, and over `K' = K(α'^{1/2})` for
   `s/2`).**
   * Prove (15) and (16) `log|f(z)/f(s)| ≤ dhT* + 1.055SD + 1.008(|z|+|s|)D`.
   * Prove (17) and (18), including the 2-adic Kummer term `2h(D₀+1)log|2|_v`.
   * This needs `[K(α'^{1/2}):K] = 2^r`, from `kummer_indep`.
3. **§16 differential Lemma 6.** `∂*^{t'}Q(t'')` lies in the span of `Q(t)` with
   `∑t ≤ T'+T''`. This is pure polynomial algebra over `Δ`, `Π`, `Θ`, and it needs BW §12's
   independence of `(Δ(z+j;k))^l` (Baker's book, Ch. 3 L2).
4. **§17 differential estimates (21) and (22)** for `f_m(l)/f(s)`.
5. **§18 finite Blaschke products.** Prove (23)–(25): elementary complex analysis on `|z| = R`,
   plus Stirling `X! ≥ (X/e)^X√(2πX)` (Mathlib: `Stirling.le_factorial`-type lemmas).
6. **§19 extrapolation.** Induct on `J = 0..r-1`.
   * Use the Cauchy integral `𝒥 - ℐ = f(s)/F(s)` with `F = B(z;S')^{T'+1}` and `R = 7·2S'`.
   * Then pass to half-integers via the lacunary product `B'`.
   * Mathlib has `Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable`
     (Cauchy formula) and `circleIntegral` bounds.
7. **§20 Kummer descent.** Use the decomposition (28) and Lemma 7.
   * Iterate `I = [50 log(2rd)]` times with `S^{(I)} = ξ^{-rI}S` and `T^{(I)} = ξ^{rI}T`.
   * Check `aI + b^{-I} ≤ 1` with `a = 0.044/(2.5log 2rd)` and `b = 2ξ^r`.
   * Output `P = Q^{(I)}(·;0)` in the variables `Y^{(I)}`. The points are `(s, α'^s)` again,
     because each step substitutes `Y₀ = ½Y₀^{(1)}` and `Yⱼ² = Yⱼ^{(1)}`.

**Numerics.** For `J ≥ 4` the §19 margin is `-0.05S'D`, and `J = 0..3` must be checked
separately with `ξ ≥ 1 - 0.536/(J+2)`. Encode every numeric step as a separate `norm_num`/`nlinarith`
lemma over the real parameters, **before** doing the analysis.
-/


open MvPolynomial

/-! ### Road map for `analytic_core` (BW §14–20)

What is already formalised in this file (all sorry-free):

* `obstruction_aux`, `mvpoly_eq_zero_of_ptS_vanishing` — the sharp obstruction: a polynomial
  constant in `Y₁,…,Y_r` which vanishes on `deg_{Y₀}P + 2` points of the curve is `0`.
* `Qpoly` — the auxiliary polynomial `Q(Y;t)` of BW §13.
* `Qval_eq_eval_Qpoly` — BW §13: `Qval = eval (ptS (lamP …) s) (Qpoly …)`, i.e. hypothesis
  (9) says exactly that the auxiliary polynomial and all its `t`-twists vanish at the points
  of the small range.
* `Qpoly_vanishing_of_hp9` — the direct corollary (input to the extrapolation §19).

Delegated and proved elsewhere (import them when needed):

* `Submission.Work.BW.Qpoly_degreeOf` — `deg_{Y₀}Qpoly ≤ h(D₀+1)`, `deg_{Y_{j+1}}Qpoly ≤ D_j`.
* `Submission.Work.BW.applyDer_Qpoly_span` — BW §16 (differential Lemma 6): the derivative
  `∂₀^{t₀}∏∂*^{t_m} Q(·;0)` lies in the span of the twists `Q(·;t')` with
  `t₀`-order fixed and `∑t' ≤ ∑t`; the proof is the universal triangular identity
  `x^N = ∑_{k≤N} β_{N,k}Δ(x,k)` with constant rational `β`.
* `Submission.Work.BW.parity_decomposition` — BW §20, step 1: the parity decomposition
  `P = ∑_ε Y^ε σ(R_ε)` with halved `Y_{j+1}`-degrees, which is what the substitution
  `Y_{j+1}² ↦ Y_{j+1}` of the descent consumes.
* `Submission.Work.BW.not_polyOut_of_small_degrees` — the obstruction certificate: no `P`
  satisfies `PolyOut` when `⌊pDj/2^{pI}⌋ = 0` and the `s`-range exceeds `deg_{Y₀}`'s budget.

Still missing for `analytic_core` itself (the analytic core of the paper):

* §14–§18: the auxiliary-function estimates (13)–(22) (`f(z) = Q(z, e^{M}; t)`,
  `g(z) = Q(z, α'^z; t)`), using (10) for `|f - g|`, the product formula, and the
  Blaschke-product/Stirling estimates (23)–(25);
* §19: the extrapolation in `J = 0..r-1`, via the Cauchy integral with
  `F = B(z;S')^{T'+1}`, extending the `s`-range to `2S^{(I)}` and shrinking the
  derivative orders;
* §20: the Kummer/half-integer step: from the vanishing of `Q(s/2, α'^{s/2})` for one choice
  of the `2^r` square roots deduce that each component `R_ε` of the parity decomposition
  vanishes (uses `Work.BW.kummer_indep`, `KummerCond`), then iterate `pI` times.

These are the pieces that remain before `analytic_core` can be assembled from the
hypotheses `hp9`, `hp12`, `h10` above.
-/

namespace Work.BW

/-- Auxiliary: for `P` constant in `Y₁,…`, the polynomial `Q = ∑_κ P.coeff κ · X^{κ 0}`
encodes `P` completely, and its values along `ptS` are those of `P`. -/
lemma obstruction_aux {r : ℕ} (ℓ : Fin r → ℂ) (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : ∀ j : Fin (r + 1), j ≠ 0 → P.degreeOf j = 0) :
    let Q : Polynomial ℂ := ∑ κ ∈ P.support, Polynomial.C (P.coeff κ) * Polynomial.X ^ (κ 0)
    Q.natDegree ≤ P.degreeOf 0 ∧
    (∀ s : ℕ, MvPolynomial.eval (ptS ℓ s) P = Q.eval (s : ℂ)) ∧
    P = Polynomial.aeval (MvPolynomial.X (0 : Fin (r+1))) Q := by
  classical
  intro Q
  have key0 : ∀ κ ∈ P.support, κ 0 ≤ P.degreeOf 0 :=
    fun κ hκ => (MvPolynomial.degreeOf_le_iff (n := (0 : Fin (r+1))) (f := P)
      (d := P.degreeOf 0)).mp le_rfl κ hκ
  have key : ∀ κ ∈ P.support, (∀ j : Fin (r+1), j ≠ 0 → κ j = 0) := by
    intro κ hκ j hj
    have h := (MvPolynomial.degreeOf_le_iff (n := j) (f := P) (d := 0)).mp (le_of_eq (hP j hj))
    exact Nat.le_zero.mp (h κ hκ)
  have hline : ∀ κ ∈ P.support, Finsupp.single (0 : Fin (r+1)) (κ 0) = κ := by
    intro κ hκ
    ext j
    by_cases hj : j = 0
    · subst hj; simp
    · rw [Finsupp.single_eq_of_ne (by simpa using hj)]
      exact (key κ hκ j hj).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun κ hκ => ?_
    rw [Polynomial.coeff_C_mul_X_pow]
    rw [if_neg (by have := key0 κ hκ; omega)]
  · intro s
    rw [MvPolynomial.eval_eq', Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun κ hκ => ?_
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    congr 1
    rw [Finset.prod_eq_single (0 : Fin (r+1))]
    · simp [ptS]
    · intro b _ hb
      rw [key κ hκ b hb, pow_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [MvPolynomial.as_sum P, map_sum]
    refine Finset.sum_congr rfl fun κ hκ => ?_
    rw [Polynomial.aeval_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
        MvPolynomial.X_pow_eq_monomial, MvPolynomial.algebraMap_eq, MvPolynomial.C_mul_monomial, mul_one, hline κ hκ]





/-- **Core obstruction.** A polynomial `P ∈ ℂ[Y₀,…,Y_r]` which is constant in `Y₁,…,Y_r`
(i.e. `deg_{Y_j} P = 0` for all `j ≠ 0`) and vanishes at the points `ptS ℓ s` of the curve
`s ↦ (s, e^{sℓ₁}, …)` for `s = 0, …, deg_{Y₀}P + 1` must be identically zero. -/
lemma mvpoly_eq_zero_of_ptS_vanishing {r : ℕ} (ℓ : Fin r → ℂ) (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : ∀ j : Fin (r + 1), j ≠ 0 → P.degreeOf j = 0)
    (hvan : ∀ s : ℕ, s ≤ P.degreeOf 0 + 1 → MvPolynomial.eval (ptS ℓ s) P = 0) : P = 0 := by
  classical
  obtain ⟨hdeg, heval, hPQ⟩ := obstruction_aux ℓ P hP
  set Q : Polynomial ℂ := ∑ κ ∈ P.support, Polynomial.C (P.coeff κ) * Polynomial.X ^ (κ 0) with hQ
  have hQdeg : Q.natDegree ≤ P.degreeOf 0 := by rw [hQ]; exact hdeg
  have hQeval : ∀ s : ℕ, MvPolynomial.eval (ptS ℓ s) P = Q.eval (s : ℂ) := by rw [hQ]; exact heval
  have hQP : P = Polynomial.aeval (MvPolynomial.X (0 : Fin (r + 1))) Q := by rw [hQ]; exact hPQ
  have hQ0 : Q = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q
      (f := fun i : Fin (P.degreeOf 0 + 2) => ((i : ℕ) : ℂ)) ?_ ?_ ?_
    · intro i j hij
      exact Fin.ext (Nat.cast_injective hij)
    · intro i
      rw [← hQeval (i : ℕ)]
      exact hvan (i : ℕ) (by have := i.isLt; omega)
    · rw [Fintype.card_fin]
      have := hQdeg
      omega
  rw [hQP, hQ0]
  simp

noncomputable def Qpoly {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (α' : Fin r → K)
    (h D0 : ℕ) (Dj : Fin r → ℕ) (p : AuxIdx r h D0 Dj → K) (t0 : ℕ) (t : Fin (r - 1) → ℕ) :
    MvPolynomial (Fin (r + 1)) ℂ :=
  ∑ lm : AuxIdx r h D0 Dj,
    MvPolynomial.C (φ (p lm) *
        (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) * (ulcm h : ℂ) ^ t0)
      * Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C ((lm.1 : ℕ) : ℂ))
          (Polynomial.hasseDeriv t0 (deltaPoly h ^ ((lm.2.1 : ℕ) + 1)))
      * ∏ j : Fin r, MvPolynomial.X j.succ ^ ((lm.2.2 j : ℕ))

lemma eval_prod_X_succ {r : ℕ} (ℓ : Fin r → ℂ) (s : ℕ) (lam : Fin r → ℕ) :
    MvPolynomial.eval (ptS ℓ s) (∏ j : Fin r, MvPolynomial.X j.succ ^ (lam j))
      = ∏ j : Fin r, (Complex.exp ((s : ℂ) * ℓ j)) ^ (lam j) := by
  rw [MvPolynomial.eval_prod]
  exact Finset.prod_congr rfl (fun j _ => by
    rw [MvPolynomial.eval_pow, MvPolynomial.eval_X]; rfl)

lemma eval_aeval_Y0 {r : ℕ} (ℓ : Fin r → ℂ) (s : ℕ) (c : ℂ) (q : Polynomial ℚ) :
    MvPolynomial.eval (ptS ℓ s) (Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C c) q)
      = Polynomial.aeval ((s : ℂ) + c) q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, map_mul, map_pow, map_add,
      MvPolynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C,
      MvPolynomial.eval_X, ptS, Fin.cons_zero]

/-- Bridge: the value of the auxiliary polynomial `Qpoly` at the point `ptS (lamP …) s`
is exactly `Qval` (for `s ≥ 0`). -/
theorem Qval_eq_eval_Qpoly {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (α : Fin n → K)
    (b : Fin n → ℤ) (k : Fin n) (v : ℕ) (L : Fin r → Fin n → ℤ) (α' : Fin r → K)
    (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ) (p : AuxIdx r h D0 Dj → K)
    (hexp : ∀ j, Complex.exp (lamP φ α v L j) = φ (α' j)) (t0 : ℕ) (t : Fin (r - 1) → ℕ) (s : ℕ) :
    Qval φ b k L ι α' h D0 Dj p t0 t (s : ℤ)
      = MvPolynomial.eval (ptS (fun j => lamP φ α v L j) s)
          (Qpoly φ b k L ι α' h D0 Dj p t0 t) := by
  classical
  have hfac : ∀ (lm : AuxIdx r h D0 Dj) (j : Fin r),
      φ (α' j) ^ ((s : ℤ) * ((lm.2.2 j : ℕ) : ℤ))
        = (Complex.exp ((s : ℂ) * lamP φ α v L j)) ^ (lm.2.2 j : ℕ) := by
    intro lm j
    rw [← hexp j,
      ← Complex.exp_int_mul (lamP φ α v L j) ((s : ℤ) * ((lm.2.2 j : ℕ) : ℤ)),
      ← Complex.exp_nat_mul ((s : ℂ) * lamP φ α v L j) (lm.2.2 j)]
    congr 1
    push_cast
    ring
  rw [Qval, Qpoly, MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl fun lm _ => ?_
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    eval_aeval_Y0, eval_prod_X_succ]
  simp only [Theta]
  rw [Finset.prod_congr rfl (fun j _ => hfac lm j)]
  push_cast
  ring

/-- Consequence of the bridge: BW (9) (`hp9`) says exactly that the auxiliary polynomial
`Qpoly` — and all of its `t`-twists — vanish at the points `ptS (lamP …) s` of the small range. -/
theorem Qpoly_vanishing_of_hp9 {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (α : Fin n → K)
    (b : Fin n → ℤ) (k : Fin n) (v : ℕ) (L : Fin r → Fin n → ℤ) (α' : Fin r → K)
    (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ) (p : AuxIdx r h D0 Dj → K)
    (hexp : ∀ j, Complex.exp (lamP φ α v L j) = φ (α' j)) (S T : ℕ)
    (hp9 : ∀ (s : ℤ), |s| ≤ (S : ℤ) → ∀ (t0 : ℕ) (t : Fin (r - 1) → ℕ),
        t0 + ∑ m, t m ≤ T → Qval φ b k L ι α' h D0 Dj p t0 t s = 0) :
    ∀ s : ℕ, (s : ℝ) ≤ (S : ℝ) → ∀ (t0 : ℕ) (t : Fin (r - 1) → ℕ),
      t0 + ∑ m, t m ≤ T →
      MvPolynomial.eval (ptS (fun j => lamP φ α v L j) s)
        (Qpoly φ b k L ι α' h D0 Dj p t0 t) = 0 := by
  intro s hs t0 t ht
  rw [← Qval_eq_eval_Qpoly φ α b k v L α' ι h D0 Dj p hexp t0 t s]
  refine hp9 (s : ℤ) ?_ t0 t ht
  rw [abs_of_nonneg (Int.natCast_nonneg s)]
  exact_mod_cast hs

end Work.BW

import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.Qpoly_degreeOf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! # `Y₀`-shadow of the descended polynomial `Q^{(J)}` (BW §20)

Definitions used by `Work.BW.yfree_contradiction` (BW's degenerate-level argument: if every
`D_j < 2^J` then `Q^{(J)}_μ(·;0)` is a polynomial in `Y₀` alone — the substitution
`Y_{j+1}^{λ_j/2^J}` is trivial — and the curve value `fAt ℓ (Q^{(J)}) z` is the value of an
explicit univariate polynomial `ycQ`).

* `ycP h d t = (hasseDeriv t (Δ(·;h)^d))` with `ℚ`-coefficients pushed to `ℂ`;
* `ycY0 h d t a c = ycP h d t` composed with `X ↦ a X + c`;
* `ycQ φ h D0 Dj p J μ t0` is `Q^{(J)}_μ(·; t0, 0)` with the torus monomials dropped.
-/

namespace Work.BW

open MvPolynomial

/-- `(1/t!) (d/dz)^t (Δ(z;h)^d)`, with coefficients pushed from `ℚ` to `ℂ`. -/
noncomputable def ycP (h d t : ℕ) : Polynomial ℂ :=
  (Polynomial.hasseDeriv t (deltaPoly h ^ d)).map (algebraMap ℚ ℂ)

/-- The `Y₀`-part `(1/t!)(d/dz)^t (Δ(z;h)^d)|_{z = aY₀+c}` of a summand of `Q^{(J)}`. -/
noncomputable def ycY0 (h d t : ℕ) (a c : ℂ) : Polynomial ℂ :=
  (ycP h d t).comp (Polynomial.C a * Polynomial.X + Polynomial.C c)

/-- The univariate shadow of `Q^{(J)}_μ(·; t0, 0)`: the sum over the auxiliary index set of the
selected `λ` with the torus monomials dropped (they are `1` when `D_j < 2^J`). -/
noncomputable def ycQ {K : Type*} [Field K] {r : ℕ} (φ : K →+* ℂ) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (p : AuxIdx r h D0 Dj → K) (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) : Polynomial ℂ :=
  ∑ lm : AuxIdx r h D0 Dj,
    if (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j) then
      Polynomial.C (φ (p lm) * (ulcm h : ℂ) ^ t0) *
        ycY0 h ((lm.2.1 : ℕ) + 1) t0 (((2 : ℂ) ^ J)⁻¹) ((lm.1 : ℕ) : ℂ)
    else 0

lemma ycP_zero (h d : ℕ) : ycP h d 0 = (deltaPoly h ^ d).map (algebraMap ℚ ℂ) := by
  simp [ycP]

lemma ycY0_eval (h d t : ℕ) (a c z : ℂ) :
    (ycY0 h d t a c).eval z = (ycP h d t).eval (a * z + c) := by
  rw [ycY0, Polynomial.eval_comp]
  congr 1
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

/-- `Polynomial.aeval` into `ℂ[X]` is "map the coefficients to `ℂ`, then compose". -/
lemma yc_aeval_eq_comp (q : Polynomial ℚ) (x : Polynomial ℂ) :
    Polynomial.aeval x q = (q.map (algebraMap ℚ ℂ)).comp x := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.aeval_add, Polynomial.map_add, Polynomial.add_comp, hp, hq]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.map_monomial, Polynomial.monomial_comp]
    simp [Polynomial.C_eq_algebraMap]

/-- Evaluation of the affine substitution at `z`. -/
lemma yc_eval_lin1 (z a c : ℂ) :
    Polynomial.eval z (Polynomial.C a * Polynomial.X + Polynomial.C c) = a * z + c := by
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

/-- Evaluation of the affine `Y₀`-substitution on the curve. -/
lemma yc_eval_lin {r : ℕ} (ℓ : Fin r → ℂ) (z a c : ℂ) :
    MvPolynomial.eval (ptC ℓ z)
      (MvPolynomial.C a * MvPolynomial.X (0 : Fin (r + 1)) + MvPolynomial.C c) = a * z + c := by
  simp [ptC]

/-- Bridge between the multivariate value of a single summand of `Qdesc` and the univariate
polynomial `ycY0`. -/
lemma yc_eval_aeval {r : ℕ} (ℓ : Fin r → ℂ) (z a c : ℂ) (q : Polynomial ℚ) :
    MvPolynomial.eval (ptC ℓ z)
        (Polynomial.aeval (MvPolynomial.C a * MvPolynomial.X (0 : Fin (r + 1)) +
          MvPolynomial.C c) q)
      = ((q.map (algebraMap ℚ ℂ)).comp
          (Polynomial.C a * Polynomial.X + Polynomial.C c)).eval z := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [Polynomial.aeval_add, Polynomial.map_add, Polynomial.add_comp,
      MvPolynomial.eval_add, Polynomial.eval_add, hp, hq]
  | monomial n a' =>
    rw [Polynomial.aeval_monomial, Polynomial.map_monomial, Polynomial.monomial_comp,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.algebraMap_apply,
      MvPolynomial.eval_C, yc_eval_lin, yc_eval_lin1]

end Work.BW

import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Auxiliary definitions and evaluation algebra for BW (14) (`est14`). This module carries the
definitions (`estCoeff`, `estTorus`, `estSig`, ...) shared with the delegated pieces of the proof,
together with the purely formal rewriting of `f^{(J)}(z) - g^{(J)}(z)` as a sum of `g`-terms
times `(e^{δ_λ} - 1)`. -/

namespace Work.BW

open MvPolynomial

/-! ============ TEMPORARY placeholders (dev only; in the real file these are imports) ============ -/



/-! ### Evaluation algebra for `Q^{(J)}` (BW §14) -/

lemma eval_aeval_ptC {r : ℕ} (a c z : ℂ) (ℓ : Fin r → ℂ) (q : Polynomial ℚ) :
    MvPolynomial.eval (ptC ℓ z)
        (Polynomial.aeval (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C c) q) =
      Polynomial.aeval (a * z + c) q := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n b =>
    simp only [Polynomial.aeval_monomial, map_mul, map_pow, map_add, map_mul,
      MvPolynomial.algebraMap_apply, MvPolynomial.eval_C,
      MvPolynomial.eval_X, ptC, Fin.cons_zero]

lemma ptC_succ {r : ℕ} (ℓ : Fin r → ℂ) (z : ℂ) (j : Fin r) :
    ptC ℓ z j.succ = Complex.exp (z * ℓ j) := by
  simp [ptC]

lemma eval_Qdesc {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ) (k : Fin n)
    (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (p : AuxIdx r h D0 Dj → K) (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (ℓ : Fin r → ℂ) (z : ℂ) :
    MvPolynomial.eval (ptC ℓ z) (Qdesc φ b k L ι h D0 Dj p J μ t0 t) =
      ∑ lm : AuxIdx r h D0 Dj,
        (if ∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j then
          (φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) *
              (ulcm h : ℂ) ^ t0) *
            Polynomial.aeval ((((2 : ℂ) ^ J)⁻¹) * z + ((lm.1 : ℕ) : ℂ))
              (Polynomial.hasseDeriv t0 (deltaPoly h ^ ((lm.2.1 : ℕ) + 1))) *
            ∏ j : Fin r, (Complex.exp (z * ℓ j)) ^ ((lm.2.2 j : ℕ) / 2 ^ J)
        else 0) := by
  rw [Qdesc, map_sum]
  refine Finset.sum_congr rfl (fun lm _ => ?_)
  by_cases hc : ∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j
  · rw [if_pos hc, if_pos hc]
    simp only [map_mul, eval_C, eval_aeval_ptC, map_prod, map_pow, eval_X, ptC_succ]
  · rw [if_neg hc, if_neg hc, map_zero]

abbrev estCond {r : ℕ} (J : ℕ) (μ : Fin r → ℕ) {h D0 : ℕ} {Dj : Fin r → ℕ}
    (lm : AuxIdx r h D0 Dj) : Prop :=
  ∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j

/-- The `λ`-dependent coefficient of the summand: `φ(p(λ))·Π(t)·u(h)^{t₀}·Θ(2^{-J}z+λ_{-1})`. -/
noncomputable def estCoeff {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (p : AuxIdx r h D0 Dj → K) (J : ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (z : ℂ) (lm : AuxIdx r h D0 Dj) : ℂ :=
  (φ (p lm) * (∏ m, Delta (gam b k L (ι m) (fun i => (lm.2.2 i : ℕ))) (t m)) *
      (ulcm h : ℂ) ^ t0) *
    Polynomial.aeval ((((2 : ℂ) ^ J)⁻¹) * z + ((lm.1 : ℕ) : ℂ))
      (Polynomial.hasseDeriv t0 (deltaPoly h ^ ((lm.2.1 : ℕ) + 1)))

/-- The torus part `∏_j (e^{zℓ_j})^{λ_j/2^J}` of the summand. -/
noncomputable def estTorus {r : ℕ} (J : ℕ) (ℓ : Fin r → ℂ) (z : ℂ) (lam : Fin r → ℕ) : ℂ :=
  ∏ j : Fin r, (Complex.exp (z * ℓ j)) ^ (lam j / 2 ^ J)

/-- One summand of `f^{(J)}` (or of `g^{(J)}`, for the two choices of `ℓ`). -/
noncomputable def estGT {K : Type*} [Field K] {n r : ℕ} (φ : K →+* ℂ) (b : Fin n → ℤ)
    (k : Fin n) (L : Fin r → Fin n → ℤ) (ι : Fin (r - 1) → Fin n) (h D0 : ℕ) (Dj : Fin r → ℕ)
    (p : AuxIdx r h D0 Dj → K) (J : ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (ℓ : Fin r → ℂ) (z : ℂ) (lm : AuxIdx r h D0 Dj) : ℂ :=
  estCoeff φ b k L ι h D0 Dj p J t0 t z lm *
    estTorus J ℓ z (fun i => (lm.2.2 i : ℕ))

section Sums

variable {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
  {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
  {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
  {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
  (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)

lemma acg_eq_sum (z : ℂ) :
    acg φ α b k L ι v σ p J μ t0 t z =
      ∑ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
        (if estCond J μ lm then
          estGT φ b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J t0 t
            (fun j => lamP φ α v L j) z lm
        else 0) := by
  classical
  rw [acg, QJ, fAt, eval_Qdesc]
  rfl

lemma acf_eq_sum (z : ℂ) :
    acf φ α b k L ι v σ p J μ t0 t z =
      ∑ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
        (if estCond J μ lm then
          estGT φ b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J t0 t
            (fun j => ellM φ α b k v L j) z lm
        else 0) := by
  classical
  rw [acf, QJ, fAt, eval_Qdesc]
  rfl

end Sums

lemma prod_exp_sub {r : ℕ} (a b : Fin r → ℂ) (n : Fin r → ℕ) :
    (∏ j, Complex.exp (a j) ^ (n j)) - (∏ j, Complex.exp (b j) ^ (n j)) =
      (∏ j, Complex.exp (b j) ^ (n j)) *
        (Complex.exp (∑ j, ((n j : ℂ) * (a j - b j))) - 1) := by
  have h1 : ∀ j : Fin r, Complex.exp (a j) ^ (n j) = Complex.exp ((n j : ℂ) * a j) :=
    fun j => (Complex.exp_nat_mul (a j) (n j)).symm
  have h2 : ∀ j : Fin r, Complex.exp (b j) ^ (n j) = Complex.exp ((n j : ℂ) * b j) :=
    fun j => (Complex.exp_nat_mul (b j) (n j)).symm
  rw [Finset.prod_congr rfl (fun j _ => h1 j), Finset.prod_congr rfl (fun j _ => h2 j)]
  rw [← Complex.exp_sum, ← Complex.exp_sum]
  have hsum : (∑ j, (n j : ℂ) * b j) + (∑ j, (n j : ℂ) * (a j - b j))
      = ∑ j, (n j : ℂ) * a j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hBC : Complex.exp (∑ j, (n j : ℂ) * a j)
      = Complex.exp (∑ j, (n j : ℂ) * b j) * Complex.exp (∑ j, (n j : ℂ) * (a j - b j)) := by
    rw [← Complex.exp_add, hsum]
  rw [hBC]
  ring

/-- The exponent by which the `f`-term differs from the `g`-term in one summand. -/
noncomputable def estSig {K : Type*} [Field K] {n r : ℕ} {h D0 : ℕ} {Dj : Fin r → ℕ}
    (φ : K →+* ℂ) (α : Fin n → K) (b : Fin n → ℤ) (k : Fin n) (v : ℕ)
    (L : Fin r → Fin n → ℤ) (J : ℕ) (z : ℂ) (lm : AuxIdx r h D0 Dj) : ℂ :=
  ∑ j : Fin r,
    (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℂ) * (z * (ellM φ α b k v L j - lamP φ α v L j))

section Diff

variable {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
  {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
  {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
  {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
  (J : ℕ) (μ : Fin r → ℕ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)

/-- `f^{(J)}(z) - g^{(J)}(z)` as a sum of `g`-terms times `(e^{δ_{λ}} - 1)`. -/
lemma acf_sub_acg_eq_sum (z : ℂ) :
    acf φ α b k L ι v σ p J μ t0 t z - acg φ α b k L ι v σ p J μ t0 t z =
      ∑ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
        (if estCond J μ lm then
          estCoeff φ b k L ι (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J t0 t z lm *
            estTorus J (fun j => lamP φ α v L j) z (fun i => (lm.2.2 i : ℕ)) *
            (Complex.exp (estSig φ α b k v L J z lm) - 1)
        else 0) := by
  classical
  rw [acf_eq_sum, acg_eq_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun lm _ => ?_)
  by_cases hc : estCond J μ lm
  · rw [if_pos hc, if_pos hc, if_pos hc]
    simp only [estGT]
    rw [← mul_sub]
    have hT := prod_exp_sub (a := fun j => z * ellM φ α b k v L j)
      (b := fun j => z * lamP φ α v L j) (n := fun j => (lm.2.2 j : ℕ) / 2 ^ J)
    simp only [estTorus] at hT ⊢
    rw [hT]
    have hsum : (∑ j, (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℂ)
          * (z * ellM φ α b k v L j - z * lamP φ α v L j))
        = ∑ j, (((lm.2.2 j : ℕ) / 2 ^ J : ℕ) : ℂ)
          * (z * (ellM φ α b k v L j - lamP φ α v L j)) :=
      Finset.sum_congr rfl (fun j _ => by ring)
    simp only [estSig]
    rw [hsum]
    ring
  · rw [if_neg hc, if_neg hc, if_neg hc]
    ring

end Diff

end Work.BW

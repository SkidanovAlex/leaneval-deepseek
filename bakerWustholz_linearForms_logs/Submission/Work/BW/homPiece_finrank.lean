import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-! ## The multihomogeneous piece of the coordinate ring of `(P¹)^{N+1}`

We compute the `ℂ`-dimension of `homPiece N d = (weightedHomogeneousSubmodule ℂ (mdeg N) d)`,
the piece of `ℂ[X_{i,0}, X_{i,1} : i]` where both variables of the `i`-th factor have weight `eᵢ`.

`homPiece N d` is `restrictSupport ℂ S` for the set `S` of exponent vectors `D` whose weighted
degree is `d`; the monomials indexed by `S` form a basis. The weighted degree of `D` at the `i`-th
coordinate is `D (i,0) + D (i,1)` (`weight_mdeg_apply` below), so `S` is in bijection with
`∏ i, Fin (d i + 1)` (`homPieceIndexEquiv`), whose cardinality is `∏ i, (d i + 1)`.
-/

/-- The coefficient at `i` of the weighted degree of an exponent vector: the two variables of the
`i`-th factor both have weight `eᵢ`, so they contribute `D (i,0)` and `D (i,1)`. -/
lemma weight_mdeg_apply {N : ℕ} (D : (Fin (N + 1) × Fin 2) →₀ ℕ) (i : Fin (N + 1)) :
    (Finsupp.weight (mdeg N) D) i = D (i, 0) + D (i, 1) := by
  rw [Finsupp.weight_eq_sum, Finsupp.finsetSum_apply]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  simp only [mdeg, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/-- Exponent vectors of monomials of weighted degree `d`: the monomials they index form a basis
of `homPiece N d`. -/
noncomputable def homIndexSet {N : ℕ} (d : Fin (N + 1) →₀ ℕ) :
    Set ((Fin (N + 1) × Fin 2) →₀ ℕ) :=
  {D | Finsupp.weight (mdeg N) D = d}

/-- The monomials of `homPiece N d` are `∏ i, X_{i,0}^{a_i} X_{i,1}^{d i - a_i}` with
`a_i ∈ {0, …, d i}`; this is the corresponding bijection of exponent vectors. -/
noncomputable def homPieceIndexEquiv {N : ℕ} (d : Fin (N + 1) →₀ ℕ) :
    homIndexSet d ≃ ((i : Fin (N + 1)) → Fin (d i + 1)) where
  toFun D := fun i => ⟨D.1 (i, 0), by
    have hD : Finsupp.weight (mdeg N) D.1 = d := D.2
    have h := DFunLike.congr_fun hD i
    rw [weight_mdeg_apply] at h
    omega⟩
  invFun a := ⟨Finsupp.equivFunOnFinite.symm (fun v : Fin (N + 1) × Fin 2 =>
      if v.2 = 0 then (a v.1 : ℕ) else d v.1 - a v.1), by
    ext i
    rw [weight_mdeg_apply, Finsupp.equivFunOnFinite_symm_apply_apply,
      Finsupp.equivFunOnFinite_symm_apply_apply]
    have ha : (a i : ℕ) ≤ d i := by have := (a i).isLt; omega
    simp only [Fin.isValue, Fin.reduceEq, reduceIte]
    omega⟩
  left_inv D := by
    apply Subtype.ext
    ext v
    rw [Finsupp.equivFunOnFinite_symm_apply_apply]
    obtain ⟨i, j⟩ := v
    fin_cases j
    · simp
    · simp
      have hD : Finsupp.weight (mdeg N) D.1 = d := D.2
      have h := DFunLike.congr_fun hD i
      rw [weight_mdeg_apply] at h
      omega
  right_inv a := by
    funext i
    apply Fin.ext
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
    simp

/-- The multihomogeneous piece `homPiece N d` of the coordinate ring of `(P¹)^{N+1}` (variables
`X_{i,0}, X_{i,1}` for `i : Fin (N+1)`, both of weight `eᵢ`) has `ℂ`-dimension `∏ i, (d i + 1)`:
its monomial basis consists of `∏ i, X_{i,0}^{a_i} X_{i,1}^{b_i}` with `a_i + b_i = d i`.
This is the Hilbert-function computation behind `Work.BW.rayDeg_bot` (`H(⊥; D) = (N+1)! ∏ D_i`). -/
theorem homPiece_finrank {N : ℕ} (d : Fin (N + 1) →₀ ℕ) :
    Module.finrank ℂ (homPiece N d) = ∏ i, (d i + 1) := by
  have hEq : homPiece N d = MvPolynomial.restrictSupport ℂ (homIndexSet d) := by
    change MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N) d
      = MvPolynomial.restrictSupport ℂ (homIndexSet d)
    rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported]
    rfl
  have hfin : Fintype ↥(homIndexSet d) :=
    Fintype.ofEquiv ((i : Fin (N + 1)) → Fin (d i + 1)) (homPieceIndexEquiv d).symm
  rw [hEq, Module.finrank_eq_card_basis
    (MvPolynomial.basisRestrictSupport ℂ (homIndexSet d))]
  rw [Fintype.card_congr (homPieceIndexEquiv d), Fintype.card_pi]
  simp

end Work.BW

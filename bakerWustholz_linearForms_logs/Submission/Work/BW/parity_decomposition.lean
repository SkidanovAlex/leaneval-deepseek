import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MvPolynomial

/-! Machinery for the parity (Kummer descent) decomposition of `ℂ[Y₀,…,Y_r]` with respect
to the substitution `σ : Y_{j+1} ↦ Y_{j+1}²` (fixing `Y₀`). -/
namespace ParityDecomp

variable {r : ℕ}

/-- Weight of coordinate `i` under the substitution: `1` for `Y₀`, `2` for `Y_{j+1}`. -/
def pw (i : Fin (r + 1)) : ℕ := if i = 0 then 1 else 2

/-- Exponent vector of `σ(X^v)`: coordinates are scaled by `pw`. -/
noncomputable def dbl (v : Fin (r + 1) →₀ ℕ) : Fin (r + 1) →₀ ℕ :=
  v.sum (fun i k => Finsupp.single i (k * pw i))

lemma dbl_apply (v : Fin (r + 1) →₀ ℕ) (i : Fin (r + 1)) : dbl v i = pw i * v i := by
  unfold dbl
  rw [Finsupp.sum_apply, Finsupp.sum_eq_single i]
  · rw [Finsupp.single_eq_same]; ring
  · intro b _ hne; rw [Finsupp.single_apply, if_neg hne]
  · intro h0; simp

lemma pw_succ (j : Fin r) : pw (j.succ : Fin (r + 1)) = 2 := by simp [pw]

/-- Halved exponent vector (coordinates `≠ 0` divided by `2`). -/
noncomputable def hw (u : Fin (r + 1) →₀ ℕ) : Fin (r + 1) →₀ ℕ :=
  Finsupp.cons (u 0) (Finsupp.equivFunOnFinite.symm (fun j : Fin r => u j.succ / 2))

lemma hw_zero (u : Fin (r + 1) →₀ ℕ) : hw u 0 = u 0 := by simp [hw, Finsupp.cons_zero]

lemma hw_succ (u : Fin (r + 1) →₀ ℕ) (j : Fin r) : hw u j.succ = u j.succ / 2 := by
  simp [hw, Finsupp.cons_succ]

/-- Parity-residue exponent vector: coordinate `j.succ` is `u j.succ % 2`, coordinate `0` is `0`. -/
noncomputable def epsv (u : Fin (r + 1) →₀ ℕ) : Fin (r + 1) →₀ ℕ :=
  Finsupp.cons 0 (Finsupp.equivFunOnFinite.symm (fun j : Fin r => u j.succ % 2))

lemma epsv_zero (u : Fin (r + 1) →₀ ℕ) : epsv u 0 = 0 := by simp [epsv, Finsupp.cons_zero]

lemma epsv_succ (u : Fin (r + 1) →₀ ℕ) (j : Fin r) : epsv u j.succ = u j.succ % 2 := by
  simp [epsv, Finsupp.cons_succ]

/-- The parity type of an exponent vector. -/
def epsOf (u : Fin (r + 1) →₀ ℕ) : Fin r → Fin 2 :=
  fun j => ⟨u j.succ % 2, Nat.mod_lt _ (by norm_num)⟩

/-- Exponent vector of the monomial `∏_j Y_{j+1}^{ε_j}`. -/
noncomputable def epsExp (ε : Fin r → Fin 2) : Fin (r + 1) →₀ ℕ :=
  Finsupp.cons 0 (Finsupp.equivFunOnFinite.symm (fun j : Fin r => (ε j : ℕ)))

/-- `eps + 2·(half)` recovers the exponent vector. -/
lemma sum_id (u : Fin (r + 1) →₀ ℕ) : epsv u + dbl (hw u) = u := by
  ext i
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
  · rw [Finsupp.add_apply, dbl_apply, hw_zero, epsv_zero, pw]; simp
  · rw [Finsupp.add_apply, dbl_apply, hw_succ, epsv_succ, pw_succ]
    exact Nat.mod_add_div (u j.succ) 2

lemma epsExp_epsOf (u : Fin (r + 1) →₀ ℕ) : epsExp (epsOf u) = epsv u := by
  simp [epsExp, epsv, epsOf]

/-- The substitution `σ : Y₀ ↦ Y₀`, `Y_{j+1} ↦ Y_{j+1}²` as a `ℂ`-algebra endomorphism. -/
noncomputable def psigma : MvPolynomial (Fin (r + 1)) ℂ →ₐ[ℂ] MvPolynomial (Fin (r + 1)) ℂ :=
  MvPolynomial.aeval (fun i : Fin (r + 1) =>
    if i = 0 then MvPolynomial.X 0 else (MvPolynomial.X i) ^ 2)

lemma X_pw (i : Fin (r + 1)) :
    (if i = 0 then (MvPolynomial.X 0 : MvPolynomial (Fin (r + 1)) ℂ)
      else (MvPolynomial.X i) ^ 2) = (MvPolynomial.X i) ^ pw i := by
  unfold pw; split_ifs with h
  · subst h; simp
  · simp

/-- `σ` acts on monomials by scaling the exponent vector. -/
lemma psigma_monomial (v : Fin (r + 1) →₀ ℕ) (a : ℂ) :
    psigma (MvPolynomial.monomial v a) = MvPolynomial.monomial (dbl v) a := by
  conv_lhs => rw [psigma, MvPolynomial.aeval_monomial]
  conv_rhs => rw [dbl, MvPolynomial.monomial_finsupp_sum_index]
  rw [MvPolynomial.algebraMap_eq]
  congr 1
  apply Finsupp.prod_congr
  intro i _
  rw [X_pw i, ← pow_mul, mul_comm (v i)]
  rw [MvPolynomial.X_pow_eq_monomial]

/-- The monomial `∏_j Y_{j+1}^{ε_j}` attached to a parity vector `ε`. -/
noncomputable def Me (ε : Fin r → Fin 2) : MvPolynomial (Fin (r + 1)) ℂ :=
  ∏ j : Fin r, (MvPolynomial.X j.succ) ^ ((ε j : ℕ))

lemma cons_zero_eq_sum (y : Fin r →₀ ℕ) :
    Finsupp.cons (0 : ℕ) y = ∑ j : Fin r, Finsupp.single j.succ (y j) := by
  ext i
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_zero_or_eq_succ i
  · simp [Finsupp.cons_zero]
  · rw [Finsupp.cons_succ, Finset.sum_apply', Finset.sum_eq_single j]
    · rw [Finsupp.single_eq_same]
    · intro b _ hb; rw [Finsupp.single_apply, if_neg]
      intro h; exact hb (Fin.succ_injective _ h)
    · intro h; simp at h

lemma Me_eq (ε : Fin r → Fin 2) : Me ε = MvPolynomial.monomial (epsExp ε) 1 := by
  have h : epsExp ε = ∑ j : Fin r, Finsupp.single j.succ ((ε j : ℕ)) := cons_zero_eq_sum _
  rw [h, MvPolynomial.monomial_sum_one, Me]
  apply Finset.prod_congr rfl
  intro j _; rw [MvPolynomial.X_pow_eq_monomial]

/-- The candidate parity components of `P`: for each `ε`, the `ε`-component of `P` with
the `Y_{j+1}`-exponents halved. -/
noncomputable def Rfun (P : MvPolynomial (Fin (r + 1)) ℂ) :
    (Fin r → Fin 2) → MvPolynomial (Fin (r + 1)) ℂ :=
  fun ε => ∑ s ∈ P.support,
    if epsOf s = ε then MvPolynomial.monomial (hw s) (P.coeff s) else 0

lemma term (P : MvPolynomial (Fin (r + 1)) ℂ) (ε : Fin r → Fin 2) (s : Fin (r + 1) →₀ ℕ) :
    Me ε * psigma (if epsOf s = ε then MvPolynomial.monomial (hw s) (P.coeff s) else 0)
      = if epsOf s = ε then MvPolynomial.monomial s (P.coeff s) else 0 := by
  by_cases h : epsOf s = ε
  · rw [if_pos h, if_pos h, ← h, psigma_monomial, Me_eq, epsExp_epsOf, monomial_mul_monomial,
        sum_id, one_mul]
  · rw [if_neg h, if_neg h, map_zero, mul_zero]

/-- The parity decomposition identity. -/
lemma key (P : MvPolynomial (Fin (r + 1)) ℂ) :
    (∑ ε : Fin r → Fin 2, Me ε * psigma (Rfun P ε)) = P := by
  have h1 : ∀ ε : Fin r → Fin 2,
      Me ε * psigma (Rfun P ε)
        = ∑ s ∈ P.support, (if epsOf s = ε then MvPolynomial.monomial s (P.coeff s) else 0) := by
    intro ε
    rw [show Rfun P ε = ∑ s ∈ P.support,
        (if epsOf s = ε then MvPolynomial.monomial (hw s) (P.coeff s) else 0) from rfl]
    rw [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun s _ => term P ε s)
  calc (∑ ε : Fin r → Fin 2, Me ε * psigma (Rfun P ε))
      = ∑ ε : Fin r → Fin 2, ∑ s ∈ P.support,
          (if epsOf s = ε then MvPolynomial.monomial s (P.coeff s) else 0) :=
        Finset.sum_congr rfl (fun ε _ => h1 ε)
    _ = ∑ s ∈ P.support, ∑ ε : Fin r → Fin 2,
          (if epsOf s = ε then MvPolynomial.monomial s (P.coeff s) else 0) := Finset.sum_comm
    _ = ∑ s ∈ P.support, MvPolynomial.monomial s (P.coeff s) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.sum_ite_eq]; simp
    _ = P := (MvPolynomial.as_sum P).symm

/-- The halved `Y_{j+1}`-degree bound. -/
lemma deg_le (P : MvPolynomial (Fin (r + 1)) ℂ) (ε : Fin r → Fin 2) (j : Fin r) :
    2 * (Rfun P ε).degreeOf j.succ ≤ P.degreeOf j.succ := by
  have hM : (Rfun P ε).degreeOf j.succ ≤ P.degreeOf j.succ / 2 := by
    rw [show Rfun P ε = ∑ s ∈ P.support,
        (if epsOf s = ε then MvPolynomial.monomial (hw s) (P.coeff s) else 0) from rfl]
    refine le_trans (MvPolynomial.degreeOf_sum_le _ _ _) ?_
    rw [Finset.sup_le_iff]
    intro s hs
    by_cases h : epsOf s = ε
    · rw [if_pos h]
      by_cases hc : P.coeff s = 0
      · rw [MvPolynomial.monomial_eq_zero.mpr hc, MvPolynomial.degreeOf_zero]; exact Nat.zero_le _
      · rw [MvPolynomial.degreeOf_monomial_eq _ _ hc, hw_succ]
        exact Nat.div_le_div_right (MvPolynomial.le_degreeOf_of_mem_support _ hs)
    · rw [if_neg h]; exact Nat.zero_le _
  calc 2 * (Rfun P ε).degreeOf j.succ ≤ 2 * (P.degreeOf j.succ / 2) := Nat.mul_le_mul_left 2 hM
    _ ≤ P.degreeOf j.succ := by rw [mul_comm]; exact Nat.div_mul_le_self _ 2

end ParityDecomp

open ParityDecomp in
/-- **Parity decomposition (BW §20, first step of the Kummer descent).** Every
`P ∈ ℂ[Y₀,…,Y_r]` decomposes as
`P = ∑_{ε : Fin r → Fin 2} (∏_j Y_{j+1}^{ε_j}) · σ(R_ε)`, where `σ` is the substitution
`Y_{j+1} ↦ Y_{j+1}²` (fixing `Y₀`), such that the substituted `Y_{j+1}`-degree is at least
halved: `2 · deg_{Y_{j+1}} R_ε ≤ deg_{Y_{j+1}} P`; and the components are independent:
`P = 0 ↔ ∀ ε, R_ε = 0`. (This is what the substitution `Y_{j+1}² ↦ Y_{j+1}` of the descent
consumes: the descended polynomial `R_ε` has halved `Y_{j+1}`-degrees.) -/
theorem parity_decomposition {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ) :
    ∃ R : (Fin r → Fin 2) → MvPolynomial (Fin (r + 1)) ℂ,
      P = ∑ ε : Fin r → Fin 2, (∏ j : Fin r, (MvPolynomial.X j.succ) ^ ((ε j : ℕ))) *
            (MvPolynomial.aeval (fun i : Fin (r + 1) =>
              if i = 0 then MvPolynomial.X 0 else (MvPolynomial.X i) ^ 2) (R ε)) ∧
      (∀ (ε : Fin r → Fin 2) (j : Fin r), 2 * (R ε).degreeOf j.succ ≤ P.degreeOf j.succ) ∧
      (P = 0 ↔ ∀ ε, R ε = 0) := by
  refine ⟨Rfun P, ?_, ?_, ?_⟩
  · simpa only [Me, psigma] using (key P).symm
  · intro ε j; exact deg_le P ε j
  · constructor
    · intro h ε
      rw [Rfun, h]; simp
    · intro h
      rw [← key P]; simp [h]

end Work.BW

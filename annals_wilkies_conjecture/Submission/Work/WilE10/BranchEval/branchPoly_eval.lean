import Mathlib
import Submission.Work.WilE10.Branch

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE10.BranchEval

open WilkiesDesign

/-! ## Elementary facts about the restricted exponential `rexp` -/

/-- On the "small" branch, `rexp` agrees with `exp`. -/
lemma rexp_of_abs_le_one (x : ℝ) (h : |x| ≤ 1) : rexp x = Real.exp x := by
  simp [WilkiesDesign.rexp, h]

/-- On the "large" branch, `rexp` is `0`. -/
lemma rexp_of_one_lt_abs (x : ℝ) (h : 1 < |x|) : rexp x = 0 := by
  simp [WilkiesDesign.rexp, not_le.mpr h]

/-! ## The arithmetic core of the large branch -/

/-- If `S * T = 1` then `S ^ D * T ^ k = S ^ (D - k)` for `k ≤ D`: multiplying by the
reciprocal `T = S⁻¹` clears powers of the exponent. -/
lemma pow_mul_inv_pow (S T : ℝ) (hST : S * T = 1) (D k : ℕ) (hk : k ≤ D) :
    S ^ D * T ^ k = S ^ (D - k) := by
  have hS : S ≠ 0 := by rintro rfl; simp at hST
  have hT : T = S⁻¹ := (inv_eq_of_mul_eq_one_right hST).symm
  have hD : S ^ D = S ^ (D - k) * S ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  rw [hT, inv_pow, hD, mul_assoc, mul_inv_cancel₀ (pow_ne_zero k hS), mul_one]

/-! ## Expanding the two sides over the support of `P` -/

/-- Evaluating the branch polynomial at `Sum.elim v E` distributes over the support of `P`:
each monomial `m` contributes the coefficient times the product of the per-index factors. -/
lemma eval_branchPoly {ι : Type*} [Fintype ι] (D : ℕ) (ε : ι → Bool) {K r : ℕ}
    (tv sv : ι → Fin K) (ev : ι → Fin r) (P : MvPolynomial (ι ⊕ ι) ℝ)
    (E : Fin r → ℝ) (v : Fin K → ℝ) :
    MvPolynomial.eval (Sum.elim v E) (Work.WilE10.branchPoly D ε tv sv ev P)
      = ∑ m ∈ P.support, P.coeff m *
          ∏ i, (if ε i then (v (tv i)) ^ (m (Sum.inl i)) * (E (ev i)) ^ (m (Sum.inr i))
                else (v (sv i)) ^ (D - m (Sum.inl i)) * (0 : ℝ) ^ (m (Sum.inr i))) := by
  unfold Work.WilE10.branchPoly
  simp only [map_sum, map_mul, map_prod, map_pow, map_zero, MvPolynomial.eval_C,
    MvPolynomial.eval_X, apply_ite, Sum.elim_inl, Sum.elim_inr]

/-- Evaluating `P` at `(T, rexp ∘ T)` distributes over the support of `P`, and each monomial
factors into its `T`-part and its `rexp`-part. -/
lemma eval_rexpPolyEval {ι : Type*} [Fintype ι]
    (P : MvPolynomial (ι ⊕ ι) ℝ) (T : ι → ℝ) :
    MvPolynomial.eval (Sum.elim T (fun i => rexp (T i))) P
      = ∑ m ∈ P.support, P.coeff m *
          ∏ i, ((T i) ^ (m (Sum.inl i)) * (rexp (T i)) ^ (m (Sum.inr i))) := by
  rw [MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [Finset.prod_mul_distrib]

/-! ## The per-monomial comparison -/

/-- The heart of the identity: for a single monomial `m`, the product of the branch-polynomial
factors equals the product of the `S ^ D`-weights over the large indices times the product of
the `(T, rexp T)`-factors.  Each index is either small (`ε i = true`), where the two factors
coincide because `rexp (T i) = exp (T i)`, or large (`ε i = false`), where the reciprocal
relation `S i * T i = 1` converts `S i ^ (D - m inl i)` into `S i ^ D * T i ^ (m inl i)` and
`rexp (T i) = 0` kills the `inr` powers. -/
lemma monomial_factor {ι : Type*} [Fintype ι] (D : ℕ) (ε : ι → Bool) {K r : ℕ}
    (tv sv : ι → Fin K) (ev : ι → Fin r) (m : ι ⊕ ι →₀ ℕ)
    (T S : ι → ℝ) (E : Fin r → ℝ) (v : Fin K → ℝ)
    (htv : ∀ i, ε i = true → v (tv i) = T i)
    (hev : ∀ i, ε i = true → E (ev i) = Real.exp (T i))
    (hsm : ∀ i, ε i = true → |T i| ≤ 1)
    (hsv : ∀ i, ε i = false → v (sv i) = S i)
    (hst : ∀ i, ε i = false → S i * T i = 1)
    (hlg : ∀ i, ε i = false → 1 < |T i|)
    (hD : ∀ i, m (Sum.inl i) ≤ D) :
    (∏ i, (if ε i then (v (tv i)) ^ (m (Sum.inl i)) * (E (ev i)) ^ (m (Sum.inr i))
            else (v (sv i)) ^ (D - m (Sum.inl i)) * (0 : ℝ) ^ (m (Sum.inr i))))
      = (∏ i ∈ Finset.univ.filter (fun i => ε i = false), S i ^ D)
        * ∏ i, ((T i) ^ (m (Sum.inl i)) * (rexp (T i)) ^ (m (Sum.inr i))) := by
  rw [Finset.prod_filter (s := Finset.univ) (p := fun i => ε i = false)
        (f := fun i => S i ^ D),
      ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : ε i = true
  · rw [ite_eq_left h, ite_eq_right (by simp [h]), one_mul, htv i h, hev i h,
      rexp_of_abs_le_one _ (hsm i h)]
  · have hf : ε i = false := by cases hv : ε i <;> simp_all
    rw [ite_eq_right h, ite_eq_left hf, hsv i hf, rexp_of_one_lt_abs _ (hlg i hf),
        ← mul_assoc, pow_mul_inv_pow (S i) (T i) (hst i hf) D (m (Sum.inl i)) (hD i)]

/-! ## The main identity -/

theorem branchPoly_eval {ι : Type*} [Fintype ι] (D : ℕ) (ε : ι → Bool) {K r : ℕ}
    (tv sv : ι → Fin K) (ev : ι → Fin r) (P : MvPolynomial (ι ⊕ ι) ℝ)
    (T S : ι → ℝ) (E : Fin r → ℝ) (v : Fin K → ℝ)
    (htv : ∀ i, ε i = true → v (tv i) = T i)
    (hev : ∀ i, ε i = true → E (ev i) = Real.exp (T i))
    (hsm : ∀ i, ε i = true → |T i| ≤ 1)
    (hsv : ∀ i, ε i = false → v (sv i) = S i)
    (hst : ∀ i, ε i = false → S i * T i = 1)
    (hlg : ∀ i, ε i = false → 1 < |T i|)
    (hD : ∀ i, ∀ m ∈ P.support, m (Sum.inl i) ≤ D) :
    MvPolynomial.eval (Sum.elim v E) (Work.WilE10.branchPoly D ε tv sv ev P) =
      (∏ i ∈ Finset.univ.filter (fun i => ε i = false), S i ^ D) *
        MvPolynomial.eval (Sum.elim T (fun i => WilkiesDesign.rexp (T i))) P := by
  rw [eval_branchPoly, eval_rexpPolyEval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [monomial_factor D ε tv sv ev m T S E v htv hev hsm hsv hst hlg (fun i => hD i m hm)]
  ring

end Work.WilE10.BranchEval

import Submission.Powers

noncomputable section
open scoped Complex Polynomial
open Polynomial

namespace Submission.RootProd

open Submission.Powers

/-- `expand 2` on the square-root-product: `∏(X - C z²)` becomes `∏(X² - C z²)`. -/
lemma expand_prod_sub_sq (S : Finset ℂ) :
    expand ℂ 2 (S.prod (fun z : ℂ => X - C (z ^ 2)))
      = S.prod (fun z : ℂ => X ^ 2 - C (z ^ 2)) := by
  rw [Polynomial.expand_eq_comp_X_pow 2]
  rw [Polynomial.prod_comp]
  apply Finset.prod_congr rfl
  intro z hz
  rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]

/-- Splitting `∏(X² - z²) = ∏(X - z) · ∏(X + z)`. -/
lemma prod_sq_eq_prod_sub_mul_prod_add (S : Finset ℂ) :
    S.prod (fun z : ℂ => X ^ 2 - C (z ^ 2))
      = S.prod (fun z : ℂ => X - C z) * S.prod (fun z : ℂ => X + C z) := by
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro z hz
  calc
    X ^ 2 - C (z ^ 2) = X ^ 2 - C (z * z) := by
      rw [show z ^ 2 = z * z by ring]
    _ = X ^ 2 - C z * C z := by rw [Polynomial.C_mul]
    _ = (X - C z) * (X + C z) := by ring

/-- `∏_{z∈S}(X + z) = (-1)^|S| · ∏_{z∈S}(X - z) ∘ (-X)`. -/
lemma prod_add_eq (S : Finset ℂ) (P : ℂ[X]) (hP : P = S.prod fun z : ℂ => X - C z) :
    S.prod (fun z : ℂ => X + C z) = (-1 : ℂ) ^ S.card • P.comp (-X) := by
  calc
    S.prod (fun z : ℂ => X + C z)
        = S.prod (fun z : ℂ => (-1 : ℂ) • (-X - C z)) := by
          apply Finset.prod_congr rfl
          intro z hz
          rw [neg_one_smul]
          ring
    _ = S.prod (fun _z : ℂ => (-1 : ℂ)) • S.prod (fun z : ℂ => -X - C z) := by
          rw [Finset.prod_smul]
    _ = (-1 : ℂ) ^ S.card • S.prod (fun z : ℂ => -X - C z) := by simp
    _ = (-1 : ℂ) ^ S.card • (S.prod (fun z : ℂ => X - C z)).comp (-X) := by
          congr 1
          rw [Polynomial.prod_comp]
          apply Finset.prod_congr rfl
          intro z hz
          rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    _ = (-1 : ℂ) ^ S.card • P.comp (-X) := by rw [hP]

/-- The degree of `∏_{z∈S}(X - z)` is `|S|`. -/
lemma natDegree_prod_X_sub_C (S : Finset ℂ) :
    (S.prod fun z : ℂ => X - C z).natDegree = S.card := by
  rw [Polynomial.natDegree_prod S (fun z : ℂ => X - C z)]
  · simp
  · intro z hz
    exact (Polynomial.monic_X_sub_C z).ne_zero

/-- For a monic polynomial with root set `S` (i.e. `P = ∏ z∈S (X - z)`), the
polynomial `pow2 P` equals `∏ z∈S (X - z²)`.  Sketch: apply `expand 2` to
both sides; the left gives `(-1)^|S| P(X) P(-X)` by `pow2_expand`, the right
gives `∏(X² - z²) = ∏(X - z)(X + z) = (-1)^|S| P(X) P(-X)`, then use
`expand_injective`. -/
lemma pow2_eq_prod_sub_sq (S : Finset ℂ) (P : ℂ[X])
    (hP : P = S.prod fun z : ℂ => X - C z) :
    pow2 P = S.prod fun z : ℂ => X - C (z ^ 2) := by
  classical
  have hdeg : P.natDegree = S.card := by
    rw [hP]
    exact natDegree_prod_X_sub_C S
  have hL : expand ℂ 2 (pow2 P) = (-1 : ℂ) ^ S.card • (P * P.comp (-X)) := by
    rw [pow2_expand P]
    rw [hdeg]
  have hR : expand ℂ 2 (S.prod (fun z : ℂ => X - C (z ^ 2)))
      = (-1 : ℂ) ^ S.card • (P * P.comp (-X)) := by
    calc
      expand ℂ 2 (S.prod (fun z : ℂ => X - C (z ^ 2)))
          = S.prod (fun z : ℂ => X ^ 2 - C (z ^ 2)) := expand_prod_sub_sq S
      _ = S.prod (fun z : ℂ => X - C z) * S.prod (fun z : ℂ => X + C z) :=
            prod_sq_eq_prod_sub_mul_prod_add S
      _ = P * S.prod (fun z : ℂ => X + C z) := by rw [hP]
      _ = P * ((-1 : ℂ) ^ S.card • P.comp (-X)) := by
            rw [prod_add_eq S P hP]
      _ = (-1 : ℂ) ^ S.card • (P * P.comp (-X)) := by
            rw [mul_smul_comm]
  exact (Polynomial.expand_injective (R := ℂ) (n := 2) (by norm_num : 0 < 2))
    (hL.trans hR.symm)

end Submission.RootProd
end

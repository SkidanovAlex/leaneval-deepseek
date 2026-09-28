import Mathlib
import Submission.Work.HP.Vero.MulDefs

namespace Work.HP.Vero

/-- The exponent-equality condition used in `mulVec` characterises `addMon`: for monomials
`p` of degree `a`, `q` of degree `b` and `M` of degree `a+b`, the components of `M` are the
componentwise sums of those of `p` and `q` exactly when `M = addMon p q`. -/
lemma mulVec_cond_iff {a b n : ℕ} (p : Mon a n) (q : Mon b n) (M : Mon (a+b) n) :
    (∀ i, (p.1 i : ℕ) + (q.1 i : ℕ) = (M.1 i : ℕ)) ↔ addMon p q = M := by
  constructor
  · intro h
    apply Subtype.ext
    funext i
    apply Fin.ext
    show ((addMon p q).1 i : ℕ) = (M.1 i : ℕ)
    rw [addMon_val]; exact h i
  · intro h i
    have := congrArg (fun X : Mon (a+b) n => ((X.1 i : ℕ))) h
    rwa [addMon_val] at this

/-- The coefficient of `M` in the product form `mulVec a b (a+b) A B`, written as a sum over
monomial pairs `(p,q)` of degrees `(a,b)` with `addMon p q = M`. -/
lemma mulVec_apply_eq {a b n : ℕ} (A : Mon a n → ℝ) (B : Mon b n → ℝ) (M : Mon (a+b) n) :
    mulVec a b (a+b) A B M
      = ∑ p : Mon a n, ∑ q : Mon b n, if addMon p q = M then A p * B q else 0 := by
  simp only [mulVec]
  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
  by_cases h : addMon p q = M
  · rw [ite_eq_left h, ite_eq_left ((mulVec_cond_iff p q M).mpr h)]
  · rw [ite_eq_right h, ite_eq_right (fun hc => h ((mulVec_cond_iff p q M).mp hc))]

/-- The Veronese monomial of a product is the product of the Veronese monomials. -/
lemma veronese_addMonR {n : ℕ} (z : Fin (n+1) → ℝ) {a b : ℕ} (p : Mon a n) (q : Mon b n) :
    veronese (a+b) n z (addMon p q) = veronese a n z p * veronese b n z q := by
  simp only [veronese, addMon_val, pow_add, Finset.prod_mul_distrib]

theorem mulVec_formEvalR {a b n : ℕ} (A : Mon a n → ℝ) (B : Mon b n → ℝ)
    (z : Fin (n + 1) → ℝ) :
    formEvalR (a + b) n (mulVec a b (a + b) A B) z
      = formEvalR a n A z * formEvalR b n B z := by
  simp only [formEvalR]
  rw [Finset.sum_mul_sum]
  trans ∑ p : Mon a n, ∑ q : Mon b n, A p * B q * veronese (a+b) n z (addMon p q)
  · simp only [mulVec_apply_eq]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.sum_eq_single (addMon p q)]
    · simp
    · intro M _ hM
      rw [ite_eq_right (fun h => hM h.symm)]
      simp
    · intro h; exact absurd (Finset.mem_univ _) h
  · refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    rw [veronese_addMonR]
    ring

end Work.HP.Vero

import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.ConvR.negaLin

namespace Work.Transform

open HvdH

/-- The `(j-k)`-th slice of `v`, zero-padded outside the index range: this is the second factor
of the `k`-th term of `convR`. -/
noncomputable def sliceV (r : ℕ) (ts : List ℕ) (v : Fin ts.prod → Fin r → ℂ)
    (j k : Fin ts.prod) : Fin r → ℂ :=
  fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0

/-- Pointwise form of the normalised synthetic convolution. -/
theorem convR_apply' (r : ℕ) (ts : List ℕ) (u v : Fin ts.prod → Fin r → ℂ)
    (j : Fin ts.prod) (c : Fin r) :
    HvdH.convR r ts u v j c = 1 / ((ts.prod * r : ℕ) : ℂ) * ∑ k : Fin ts.prod,
      HvdH.negaMul r (u k) (sliceV r ts v j k) c := rfl

/-- The slice map is additive in `v`. -/
lemma sliceV_sub (r : ℕ) (ts : List ℕ) (v v' : Fin ts.prod → Fin r → ℂ) (j k : Fin ts.prod) :
    sliceV r ts v j k - sliceV r ts v' j k = sliceV r ts (v - v') j k := by
  funext c'
  rw [Pi.sub_apply]
  simp only [sliceV]
  by_cases h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod
  · simp only [dite_eq_left h, Pi.sub_apply]
  · simp only [dite_eq_right h, sub_zero]

/-- Applied form of left additivity of `negaMul`. -/
lemma negaMul_sub_left_apply (r : ℕ) (a a' b : Fin r → ℂ) (c : Fin r) :
    HvdH.negaMul r (a - a') b c = HvdH.negaMul r a b c - HvdH.negaMul r a' b c := by
  have h := congrFun ((Work.ConvR.negaLin r).1 a a' b) c
  simpa [Pi.sub_apply] using h

/-- Applied form of right additivity of `negaMul`. -/
lemma negaMul_sub_right_apply (r : ℕ) (a b b' : Fin r → ℂ) (c : Fin r) :
    HvdH.negaMul r a (b - b') c = HvdH.negaMul r a b c - HvdH.negaMul r a b' c := by
  have h := congrFun ((Work.ConvR.negaLin r).2 a b b') c
  simpa [Pi.sub_apply] using h

/-- `convR` is additive in its first argument. -/
theorem convR_sub_left (r : ℕ) (ts : List ℕ) (u u' v : Fin ts.prod → Fin r → ℂ) :
    HvdH.convR r ts u v - HvdH.convR r ts u' v = HvdH.convR r ts (u - u') v := by
  funext j c
  simp only [Pi.sub_apply, convR_apply']
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [negaMul_sub_left_apply]

/-- `convR` is additive in its second argument. -/
theorem convR_sub_right (r : ℕ) (ts : List ℕ) (u v v' : Fin ts.prod → Fin r → ℂ) :
    HvdH.convR r ts u v - HvdH.convR r ts u v' = HvdH.convR r ts u (v - v') := by
  funext j c
  simp only [Pi.sub_apply, convR_apply']
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [← sliceV_sub, negaMul_sub_right_apply]

/-- `M_R` is bilinear, hence additive in each variable.  Used to propagate the errors of the
two input arrays through `convR`. -/
theorem convR_sub (r : ℕ) (ts : List ℕ) (u u' v v' : Fin ts.prod → Fin r → ℂ) :
    HvdH.convR r ts u v - HvdH.convR r ts u' v'
      = HvdH.convR r ts (u - u') v + HvdH.convR r ts u' (v - v') := by
  rw [← convR_sub_left r ts u u' v, ← convR_sub_right r ts u' v v']
  abel

end Work.Transform

import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.eNorm_veronese_bounds

set_option autoImplicit false
noncomputable section

open Filter Finset MeasureTheory
open scoped RealInnerProductSpace

namespace Work.HP

section veronese
variable (d n : ℕ)

/-- The Veronese map is homogeneous of degree `d`. -/
lemma veronese_mul_left {R : Type*} [CommSemiring R] (c : R) (x : Fin (n + 1) → R)
    (m : Mon d n) : veronese d n (fun i => c * x i) m = c ^ d * veronese d n x m := by
  simp only [veronese]
  rw [Finset.prod_congr rfl fun i _ => mul_pow c (x i) (m.1 i : ℕ)]
  rw [Finset.prod_mul_distrib]
  have h1 : (∏ i : Fin (n + 1), c ^ (m.1 i : ℕ)) = c ^ (∑ i, (m.1 i : ℕ)) := by
    simpa using Finset.prod_pow_eq_pow_sum (Finset.univ) (fun i : Fin (n + 1) => (m.1 i : ℕ)) c
  rw [h1, m.2]

/-- `veronese` of the negation. -/
lemma veronese_neg {R : Type*} [CommRing R] (x : Fin (n + 1) → R) (m : Mon d n) :
    veronese d n (-x) m = (-1) ^ d * veronese d n x m := by
  have h := veronese_mul_left (R := R) d n (-1 : R) x m
  have h2 : (fun i => (-1 : R) * x i) = -x := by funext i; simp
  rw [h2] at h
  simpa using h

lemma eNorm_veronese_neg (x : Fin (n + 1) → ℤ) :
    eNorm (veronese d n (-x)) = eNorm (veronese d n x) := by
  have h : ∀ m : Mon d n,
      ((veronese d n (-x) m : ℤ) : ℝ) ^ 2 = ((veronese d n x m : ℤ) : ℝ) ^ 2 := by
    intro m
    rw [veronese_neg (R := ℤ) d n x m]
    push_cast
    rw [mul_pow]
    have hodd : ((-1 : ℝ) ^ d) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [hodd, one_mul]
  simp only [eNorm]
  congr 1
  exact Finset.sum_congr rfl fun m _ => by
    simpa [toR] using h m

end veronese

section bridge
variable {ι : Type*} [Fintype ι]

lemma norm_toE (v : ι → ℝ) : ‖toE v‖ = rNorm v := by
  rw [toE, EuclideanSpace.norm_eq, rNorm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs, sq]

lemma inner_toE (v w : ι → ℝ) : inner ℝ (toE v) (toE w) = dotR v w := by
  rw [toE, toE, PiLp.inner_apply, dotR]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RCLike.inner_apply, conj_trivial]
  ring

lemma toEr_eq (v : ι → ℤ) : toEr v = toE (toR v) := rfl

end bridge

end Work.HP

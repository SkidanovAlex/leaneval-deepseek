import Mathlib
import Submission.Work.LinnikBurgess.frame_count_prov_defs
import Submission.Work.LinnikBurgess.DLd_perm

/-!
# Small helpers for the frame count (`frame_count_prov`)

* `contAB_dvd_prod_del`: `contAB a b` divides `∏_k |a i - b k|` (the content divides
  `f_b(-a_i)`);
* `wg_sq`: `(wg m x y)^2 = gcd m |x-y|`;
* `wtAB_caseS`, `wtAB_caseT`: the weight of a pair in the collapsed case (`a 1 = a 2`) and in
  the two-distinct-shared-values case.
-/

open scoped BigOperators

namespace Work.LinnikBurgess

open Classical

lemma eval_cubicZ_neg (a b : Fin 3 → ℕ) (i : Fin 3) :
    (cubicZ b).eval (-(((a i : ℕ) : ℤ))) = ∏ k : Fin 3, ((b k : ℤ) - (a i : ℤ)) := by
  rw [cubicZ, Polynomial.eval_prod]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  ring

lemma natAbs_del (x y : ℕ) : (((y : ℤ) - (x : ℤ))).natAbs = del x y := by
  rw [del_comm, del]

lemma prod_natAbs_eq (f : Fin 3 → ℤ) :
    (∏ k : Fin 3, (f k).natAbs) = (∏ k : Fin 3, f k).natAbs :=
  (map_prod Int.natAbsHom f Finset.univ).symm

/-- The content `contAB a b` divides `∏_k |a i - b k| = f_b(-a_i)`. -/
lemma contAB_dvd_prod_del (a b : Fin 3 → ℕ) (i : Fin 3) :
    contAB a b ∣ ∏ k : Fin 3, del (a i) (b k) := by
  have h := contAB_dvd_cubicZ_eval_neg a b i
  rw [eval_cubicZ_neg] at h
  have h2 : (contAB a b : ℕ) ∣ (∏ k : Fin 3, ((b k : ℤ) - (a i : ℤ))).natAbs :=
    Int.natAbs_dvd_natAbs.mpr (by simpa using h)
  rw [← prod_natAbs_eq (fun k => ((b k : ℤ) - (a i : ℤ)))] at h2
  have h3 : (∏ k : Fin 3, (((b k : ℤ) - (a i : ℤ)).natAbs)) = ∏ k : Fin 3, del (a i) (b k) :=
    Finset.prod_congr rfl (fun k _ => natAbs_del (a i) (b k))
  rw [h3] at h2
  exact h2

/-- The square of a weight factor is the corresponding `gcd`. -/
lemma wg_sq (m x y : ℕ) : (wg m x y) ^ 2 = ((Nat.gcd m (del x y) : ℕ) : ℝ) := by
  rw [wg, pow_two, Real.mul_self_sqrt (Nat.cast_nonneg _)]

/-- In the collapsed case (`a 1 = a 2 = s`) the weight is `(wg m α s)^2 * ∏_k wg m α (b k)`. -/
lemma wtAB_caseS (m α s : ℕ) (b : Fin 3 → ℕ) :
    wtAB m ![α, s, s] b = (wg m α s) ^ 2 * (wg m α (b 0) * wg m α (b 1) * wg m α (b 2)) := by
  simp only [wtAB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  ring

end Work.LinnikBurgess

import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman

open Polynomial in
/-- If `(f - 1) ^ k = 0` then the Jordan index of `f` (the degree of its minimal polynomial) is at
most `k`: the minimal polynomial divides `(X - 1) ^ k`. -/
theorem natDegree_minpoly_le_of_pow_sub_one_eq_zero {K M : Type*} [Field K] [AddCommGroup M]
    [Module K M] {f : Module.End K M} {k : ℕ} (h : (f - 1) ^ k = 0) :
    (minpoly K f).natDegree ≤ k := by
  have hX1 : (aeval f) (X - 1 : Polynomial K) = f - 1 := by
    simp [map_sub, aeval_X]
  have hpoly : (aeval f) ((X - 1 : Polynomial K) ^ k) = 0 := by
    rw [map_pow, hX1, h]
  have hdvd : minpoly K f ∣ (X - 1 : Polynomial K) ^ k := minpoly.dvd K f hpoly
  have hne : (X - 1 : Polynomial K) ^ k ≠ 0 :=
    pow_ne_zero _ (X_sub_C_ne_zero 1)
  calc (minpoly K f).natDegree ≤ ((X - 1 : Polynomial K) ^ k).natDegree :=
        natDegree_le_of_dvd hdvd hne
    _ = k := by rw [natDegree_pow, ← Polynomial.C_1, natDegree_X_sub_C, mul_one]

end Work.HallHigman

import Mathlib.Analysis.InnerProductSpace.PiL2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

/-- Helper: the `ℓ²`-norm to the `80`-th power is the `40`-th power of the sum of
squared coordinates. -/
private lemma norm_sq_eq_sum (p : EuclideanSpace ℝ (Fin 3)) :
    ‖p‖ ^ 2 = ∑ k : Fin 3, |p k| ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  exact Finset.sum_congr rfl fun k _ => by rw [Real.norm_eq_abs, sq_abs]

theorem hp_norm_pow_coord (p : EuclideanSpace ℝ (Fin 3)) :
    ‖p‖ ^ 80 ≤ 3 ^ 39 * ∑ k : Fin 3, |p k| ^ 80 := by
  have h2 := norm_sq_eq_sum p
  -- Power-mean (Hölder) inequality with conjugate exponents `40` and `40/39`,
  -- applied to `f k = |p k| ^ 2` and `g ≡ 1`.
  have key : (∑ k : Fin 3, |p k| ^ 2) ^ 40 ≤ 3 ^ 39 * ∑ k : Fin 3, |p k| ^ 80 := by
    have h3 := Real.rpow_sum_le_const_mul_sum_rpow (s := Finset.univ)
      (f := fun k : Fin 3 => |p k| ^ 2) (p := (40:ℝ)) (by norm_num)
    simp only [Finset.card_univ, Fintype.card_fin, abs_sq] at h3
    have e1 : (∑ k : Fin 3, |p k| ^ 2) ^ (40:ℝ) = (∑ k : Fin 3, |p k| ^ 2) ^ 40 :=
      Real.rpow_natCast _ 40
    have e2 : ((3:ℕ) : ℝ) ^ ((40:ℝ) - 1) = (3:ℝ) ^ 39 := by norm_num
    have e3 : (∑ k : Fin 3, (|p k| ^ 2) ^ (40:ℝ)) = ∑ k : Fin 3, |p k| ^ 80 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 : (|p k| ^ 2) ^ (40:ℝ) = (|p k| ^ 2) ^ 40 := Real.rpow_natCast _ 40
      rw [h1, ← pow_mul]
    rw [e1, e2, e3] at h3
    exact h3
  calc ‖p‖ ^ 80 = (‖p‖ ^ 2) ^ 40 := by
        rw [show (80:ℕ) = 2 * 40 by norm_num, pow_mul]
    _ = (∑ k : Fin 3, |p k| ^ 2) ^ 40 := by rw [h2]
    _ ≤ 3 ^ 39 * ∑ k : Fin 3, |p k| ^ 80 := key

end Work.BoseFixB3.CS.Pieces

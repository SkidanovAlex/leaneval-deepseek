import Mathlib
import Submission.Work.BW.basisRed_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The weighted `ℓ¹`-norm of the image under `A` vanishes exactly at the origin, provided
`det A ≠ 0` and all weights `c i` are strictly positive. -/
theorem wNorm_eq_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (hA : A.det ≠ 0) (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) (x : Fin n → ℝ) : Work.BW.wNorm A c x = 0 ↔ x = 0 := by
  have hdet : (A.map (Int.castRingHom ℝ)).det ≠ 0 := by
    change (A.map (fun x : ℤ => (x : ℝ))).det ≠ 0
    rw [← Int.cast_det (R := ℝ) A]
    exact_mod_cast hA
  constructor
  · intro h
    -- every summand of the nonnegative sum is zero
    have hterm : ∀ i, c i * |(A.map (Int.castRingHom ℝ)).mulVec x i| = 0 := by
      intro i
      have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          0 ≤ c i * |(A.map (Int.castRingHom ℝ)).mulVec x i| :=
        fun i _ => mul_nonneg (le_of_lt (hc i)) (abs_nonneg _)
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp ?_ i (Finset.mem_univ i)
      · exact this
      · simpa only [wNorm] using h
    -- hence each coordinate of `A x` vanishes
    have hz : (A.map (Int.castRingHom ℝ)).mulVec x = 0 := by
      funext i
      have hi := hterm i
      rcases mul_eq_zero.mp hi with h1 | h1
      · exact absurd h1 (ne_of_gt (hc i))
      · simpa using h1
    -- and `A` is injective since its determinant is nonzero
    have hinj : Function.Injective (A.map (Int.castRingHom ℝ)).mulVec :=
      Matrix.mulVec_injective_of_det_ne_zero hdet
    have : (A.map (Int.castRingHom ℝ)).mulVec x = (A.map (Int.castRingHom ℝ)).mulVec 0 := by
      rw [hz]; simp
    exact hinj this
  · intro h
    subst h
    simp [wNorm]

end Work.BW

import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension.rank_ge_const_coeff
import Submission.Work.ORHughesFree.RankAPI.rk_mul_add_le
import Submission.Work.ORHughesFree.SylvesterRank

universe u

namespace Work.ORHughesFree.NaturalExtension

/-- The `1 × 1` zero matrix is `oneByOne 0`. -/
theorem oneByOne_zero_eq {U : Type u} [Zero U] :
    oneByOne (0 : U) = (0 : Matrix (Fin 1) (Fin 1) U) := by
  ext i j
  simp [oneByOne]

/-- The rank of the `1 × 1` matrix of a vanishing element is zero. -/
theorem rk_oneByOne_eq_zero_of_eq_zero {U : Type u} [Ring U] (rk : SylvesterRank U) {a : U}
    (ha : a = 0) : rk.rk 1 1 (oneByOne a) = 0 := by
  rw [ha, oneByOne_zero_eq, rk.rk_zero]

/-- **Sylvester's law of nullity for `1 × 1` matrices (annihilator form).**  If `q * p = 0` in a
ring carrying a Sylvester rank function `rk`, then `rk p + rk q ≤ 1`. -/
theorem rk_oneByOne_add_le_one_of_mul_eq_zero {U : Type u} [Ring U] (rk : SylvesterRank U)
    {p q : U} (h0 : q * p = 0) :
    rk.rk 1 1 (oneByOne p) + rk.rk 1 1 (oneByOne q) ≤ 1 := by
  have hSyl := Work.ORHughesFree.RankAPI.rk_mul_add_le rk (oneByOne q) (oneByOne p)
  rw [oneByOne_mul_eq] at hSyl
  have hz : rk.rk 1 1 (oneByOne (q * p)) = 0 := rk_oneByOne_eq_zero_of_eq_zero rk h0
  rw [hz, zero_add, Nat.cast_one] at hSyl
  linarith

theorem rank_le_one_sub_const_ann {R : Type u} [Ring R] [VonNeumannRegularRing R] [MulSemiringAction (Multiplicative ℤ) R] (rk' : SylvesterRank (SkewL R)) (hb : ∀ (n : ℕ) (B : Matrix (Fin n) (Fin n) (SkewL R)), (∀ i j, ∀ k : ℤ, k < 0 → coeffElt (B i j) k = 0) → rk'.rk n n ((1 : Matrix (Fin n) (Fin n) (SkewL R)) + B * Matrix.diagonal (fun _ => skewLaurentT)) = (n : ℝ)) {p q' : SkewL R} (hq' : ∀ k : ℤ, k < 0 → coeffElt q' k = 0) (h0 : q' * p = 0) : rk'.rk 1 1 (oneByOne p) ≤ 1 - rk'.rk 1 1 (oneByOne (SkewMonoidAlgebra.single 1 (coeffElt q' 0))) := by
  -- Sylvester's law of nullity: `rk p + rk q' ≤ rk (q' * p) + 1 = 1`.
  have hSyl := rk_oneByOne_add_le_one_of_mul_eq_zero rk' h0
  -- the constant term of the polynomial `q'` has rank at most the rank of `q'`
  have hc := rank_ge_const_coeff rk' hb q' hq'
  linarith

end Work.ORHughesFree.NaturalExtension

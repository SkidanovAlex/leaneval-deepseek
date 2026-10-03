import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.RankAPI.rk_mul_add_le
import Submission.Work.ORHughesFree.RankAPI.rk_le_left
import Submission.Work.ORHughesFree.RankAPI.rk_one_fin

namespace Work.RankAPI

open Work.ORHughesFree

/-- An invertible `n × n` matrix has rank `n` for any Sylvester matrix rank function.

Indeed, writing `X = ↑u` for a unit `u`, `(SMat2)` applied to the product
`u * ↑u⁻¹ = 1` gives `rk X ≥ rk 1 = n`, while `rk_le_left` gives `rk X ≤ n`. -/
theorem rk_eq_of_isUnit {R : Type} [Ring R] (rk : Work.ORHughesFree.SylvesterRank R) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) R) (hX : IsUnit X) : rk.rk n n X = n := by
  obtain ⟨Y, rfl⟩ := hX
  have hle : (n : ℝ) ≤ rk.rk n n (↑Y : Matrix (Fin n) (Fin n) R) := by
    have h := rk.rk_mul_le_left (↑Y : Matrix (Fin n) (Fin n) R)
      (↑(Y⁻¹) : Matrix (Fin n) (Fin n) R)
    rw [Units.mul_inv, Work.ORHughesFree.RankAPI.rk_identity_eq rk n] at h
    exact h
  have hge : rk.rk n n (↑Y : Matrix (Fin n) (Fin n) R) ≤ n :=
    Work.ORHughesFree.RankAPI.rk_le_left rk _
  exact le_antisymm hge hle

end Work.RankAPI

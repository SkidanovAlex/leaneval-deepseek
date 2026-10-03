import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension.EltDeg
import Submission.Work.ORHughesFree.NaturalExtension.supConstDefs
import Submission.Work.ORHughesFree.NaturalExtension.supConstMain
import Submission.Work.ORHughesFree.NaturalExtension.assembly
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.RankAPI.rk_mul_add_le
import Submission.Work.ORHughesFree.RankAPI.rk_reindex
import Submission.Work.ORHughesFree.RankAPI.rk_submatrix
import Submission.Work.ORHughesFree.RankAPI.rk_add_le
import Submission.Work.ORHughesFree.RankAPI.rk_le_left
import Submission.Work.ORHughesFree.RankAPI.rk_le_right
import Submission.Work.ORHughesFree.DivisionRank.regular_leftIdeal_idempotent

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree

/-! ## Idempotent complement ranks -/

/-- For an idempotent `e` in a ring with a Sylvester rank function, the ranks of `e` and
`1 - e` add up to at least `1`. -/
theorem rk_idem_add_compl {R : Type*} [Ring R] (rk : SylvesterRank R) (e : R) :
    1 ≤ rk.rk 1 1 (oneByOne e) + rk.rk 1 1 (oneByOne (1 - e)) := by
  have h : oneByOne e + oneByOne (1 - e) = oneByOne (1 : R) := by
    ext i j; fin_cases i; fin_cases j; simp [oneByOne]
  have h1 : oneByOne (1 : R) = (1 : Matrix (Fin 1) (Fin 1) R) := by
    ext i j; fin_cases i; fin_cases j; simp [oneByOne]
  have h2 := RankAPI.rk_add_le rk (oneByOne e) (oneByOne (1 - e))
  rw [h, h1, rk.rk_one] at h2
  linarith

theorem sup_const_mul_add_sup_const_ann {R : Type u} [Ring R] [VonNeumannRegularRing R] [MulSemiringAction (Multiplicative ℤ) R] (rk : SylvesterRank R) (hτ : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R), rk.rk n m (A.map (fun a => (Multiplicative.ofAdd (1 : ℤ)) • a)) = rk.rk n m A) (p : SkewL R) (hp : ∀ k : ℤ, k < 0 → coeffElt p k = 0) : ∀ ε : ℝ, 0 < ε → ∃ (c₀ c₁ : R), (∃ q q' : SkewL R, q = q' * p ∧ (∀ k : ℤ, k < 0 → coeffElt q k = 0) ∧ coeffElt q 0 = c₀) ∧ (∃ q'' : SkewL R, q'' * p = 0 ∧ (∀ k : ℤ, k < 0 → coeffElt q'' k = 0) ∧ coeffElt q'' 0 = c₁) ∧ rk.rk 1 1 (oneByOne c₀) + rk.rk 1 1 (oneByOne c₁) ≥ 1 - ε := by
  exact assembly_of_sup rk p (supConstMain rk hτ p hp)

end Work.ORHughesFree.NaturalExtension

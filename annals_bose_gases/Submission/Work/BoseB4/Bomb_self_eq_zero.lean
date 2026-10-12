import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Analysis.Normed.Field.Basic
import Submission.Work.BoseB4.RealFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Bomb_self_eq_zero` — positive-definiteness of the Bombieri form

The Bombieri (Fock) form `bomb m p q = Σ_α p_α q_α α!` is *positive definite*:
`bomb m p p = 0` forces `p = 0`.  This is the statement that the normalised
monomials `x^α/√(α!)` are orthonormal, and it is what makes `RealFock m` a
(pre-)Hilbert space in the sense of node B7's `FockData`.

The proof is the elementary one.  Expand the quadratic form into the finite sum

    bomb m p p = Σ_{α ∈ p.support} (p α)^2 · α! ,

observe that every summand is non-negative because the multi-index factorial
`α! = ∏_l (α_l)!` is strictly positive (it is a product of factorials of
naturals, each `≥ 1`; the empty product is `1`), and conclude that a vanishing
sum of non-negative terms forces every summand — hence every coefficient
`p α` — to vanish.

The two auxiliary lemmas are kept in the auxiliary namespace `Work.BoseB4.BombSelf`
so that they can never collide with a same-named lemma about `bomb` proved
elsewhere in node B4.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB4

set_option autoImplicit false

namespace BombSelf

/-! ## 1. The Bombieri form as an explicit finite sum -/

/-- The Bombieri form evaluated on a pair of states is the finite sum
`Σ_α p_α q_α α!` over the support of `p`. -/
lemma bomb_eq_sum {m : ℕ} (p q : RealFock m) :
    bomb m p q = p.sum (fun α c => c * (mfac α * q α)) := by
  simp only [bomb, Finsupp.lsum_apply, Finsupp.sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  simp only [LinearMap.smul_apply, LinearMap.toSpanSingleton_apply, Finsupp.lapply_apply,
    smul_eq_mul]

/-- The quadratic form of the Bombieri form is the sum of squares
`Σ_α (p α)^2 α!` over the support of `p`. -/
lemma bomb_self_eq_sum {m : ℕ} (p : RealFock m) :
    bomb m p p = ∑ α ∈ p.support, (p α) ^ 2 * mfac α := by
  rw [bomb_eq_sum, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro α _
  ring

/-! ## 2. Positivity of the weight `α!` -/

/-- The multi-index factorial `α! = ∏_l (α_l)!` is strictly positive: it is a
product of factorials of naturals, each `≥ 1`, and the empty product is `1`. -/
lemma mfac_pos {m : ℕ} (α : Fin m →₀ ℕ) : 0 < mfac α := by
  rw [mfac, Finsupp.prod]
  exact Finset.prod_pos fun i _ => by positivity

end BombSelf

/-! ## 3. Positive definiteness -/

theorem Bomb_self_eq_zero {m : ℕ} {p : Work.BoseB4.RealFock m}
    (h : Work.BoseB4.bomb m p p = 0) : p = 0 := by
  have hsum : ∑ α ∈ p.support, (p α) ^ 2 * mfac α = 0 := by
    rw [← BombSelf.bomb_self_eq_sum]
    exact h
  have hterm : ∀ α ∈ p.support, (p α) ^ 2 * mfac α = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun α _ => by have := BombSelf.mfac_pos α; positivity)).mp hsum
  refine Finsupp.ext fun α => ?_
  by_cases hα : α ∈ p.support
  · have h2 := hterm α hα
    have hm := BombSelf.mfac_pos α
    have h3 : (p α) ^ 2 = 0 := (mul_eq_zero.mp h2).resolve_right (ne_of_gt hm)
    simpa using sq_eq_zero_iff.mp h3
  · simp only [Finsupp.mem_support_iff, not_not] at hα
    simpa using hα

end Work.BoseB4

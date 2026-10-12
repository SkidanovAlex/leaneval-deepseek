import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseB4.RealFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Ann_ann_comm` — annihilation operators commute

`ann m l` is the formal derivative `∂/∂x_l` on the monomial-coefficient model
`RealFock m = (Fin m →₀ ℕ) →₀ ℝ` of the bosonic Fock space (see
`Work.BoseB4.RealFock`). Annihilation operators of a commutative polynomial
algebra commute; here that is proved by evaluating the two composites on the
basis `Finsupp.basisSingleOne` of `RealFock m` and comparing the resulting
multiplied shifts.

The helpers below are `private` so that they cannot clash with declarations of
other modules of the workspace.
-/

namespace Work.BoseB4

/-- `ann m l` on a basis monomial: `(∂_l (c · x^α)) = c · (α_l) · x^(α - e_l)`. -/
private lemma ann_single {m : ℕ} (l : Fin m) (α : Fin m →₀ ℕ) (c : ℝ) :
    ann m l (Finsupp.single α c) = c • ((α l : ℝ) • Finsupp.single (α - e m l) 1) := by
  rw [ann, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

/-- The arithmetic heart of the commutation: shifting down in `l'` and then reading
the `l`-coordinate multiplied by the `l'`-coordinate does not depend on the order
of `l` and `l'` (the `l = l'` case gives `α_l · (α_l - 1)` on both sides). -/
private lemma key {m : ℕ} (α : Fin m →₀ ℕ) (l l' : Fin m) :
    ((α - e m l') l) * (α l') = ((α - e m l) l') * (α l) := by
  by_cases h : l = l'
  · subst h; rfl
  · rw [Finsupp.tsub_apply, Finsupp.tsub_apply, e, e,
      Finsupp.single_eq_of_ne h, Finsupp.single_eq_of_ne (Ne.symm h), tsub_zero, tsub_zero]
    exact Nat.mul_comm _ _

/-- `key`, cast to `ℝ` and with the two factors in the order produced by the
composition of the two annihilations. -/
private lemma keyR {m : ℕ} (α : Fin m →₀ ℕ) (l l' : Fin m) :
    (α l') * ((α - e m l') l : ℝ) = (α l) * ((α - e m l) l') := by
  have h : ((α - e m l') l : ℝ) * (α l') = ((α - e m l) l' : ℝ) * (α l) := by
    exact_mod_cast key α l l'
  rw [mul_comm (α l' : ℝ) ((α - e m l') l : ℝ), h]
  exact mul_comm _ _

/-- The two-fold annihilation on a basis monomial, in closed form. -/
private lemma ann_ann_single {m : ℕ} (l l' : Fin m) (α : Fin m →₀ ℕ) :
    ann m l (ann m l' (Finsupp.single α 1)) =
      ((α l') * ((α - e m l') l : ℝ)) • Finsupp.single ((α - e m l') - e m l) 1 := by
  rw [show ann m l' (Finsupp.single α 1)
      = (α l' : ℝ) • Finsupp.single (α - e m l') 1 by
        rw [ann_single]; simp]
  rw [map_smul, ann_single]
  simp

theorem Ann_ann_comm {m : ℕ} (l l' : Fin m) :
    (Work.BoseB4.ann m l).comp (Work.BoseB4.ann m l')
      = (Work.BoseB4.ann m l').comp (Work.BoseB4.ann m l) := by
  apply (Finsupp.basisSingleOne (R := ℝ) (ι := Fin m →₀ ℕ)).ext
  intro α
  change (ann m l) ((ann m l') (Finsupp.single α 1))
      = (ann m l') ((ann m l) (Finsupp.single α 1))
  rw [ann_ann_single, ann_ann_single, keyR, tsub_right_comm]

end Work.BoseB4

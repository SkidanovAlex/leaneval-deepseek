import Mathlib
import Submission.Work.ORLyndon.powDefs

/-!
# The base case of the Cohen--Lyndon induction: `relatorNorm u ≤ 1`

Let `X` be a type, `K` a field, and `r = u ^ l` with `1 ≤ l`, where `u` is *not* a proper power and
`relatorNorm u ≤ 1`.  By `Work.OROneRel.eq_one_or_exists_letterPow_of_relatorNorm_le_one` a word of
norm at most one is trivial or a single letter `letterPow a s = of a` (`s = true`) or `(of a)⁻¹`
(`s = false`); the trivial case is excluded by `¬ IsProperPower u`.

The conclusion `Work.ORLyndon.LyndonIndependence K r u` is the base case of the Cohen--Lyndon /
Lyndon identity theorem, and this file proves it *unconditionally* (no Karrass--Magnus--Solitar
input for a general root, only its terminal case):

* the `a`-component of the Fox vector of `u` is `1` for `u = of a` and `-of (ū⁻¹)` for
  `u = (of a)⁻¹` — a unit of `K[⟨X | u ^ l⟩]` in both cases;
* hence `Work.ORLyndon.lyndon_independence_of_rootVec_isUnit'` applies, and it only asks for the
  order of the *class of a single generator*, which is `Work.OROneRel.kmsRoot_of_letterPow`, proved
  in the workspace for the terminal presentation and axiom-clean (`propext`, `Classical.choice`,
  `Quot.sound`).

Note that this avoids the general KMS chain `Work.ORLyndon.orderOf_presentRho`, whose proof goes
through the Magnus hierarchy (`Submission/Work/OROneRel/magnus_step_root.lean`) and hence through
unproved steps; the single-letter case needs none of that.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

/-- **The Fox vector of a single generator.**  The `a`-component of `(∂ (of a) / ∂ x)_x` is `1`. -/
theorem rootVec_of_letter {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    (r : FreeGroup X) (a : X) :
    rootVec K r (FreeGroup.of a) a = 1 := by
  rw [rootVec_apply, foxD_of, if_pos rfl, map_one]

/-- **The Fox vector of an inverse generator.**  `(∂ (of a)⁻¹ / ∂ x)_a = - of (ā⁻¹)`, where
`ā = presentRho r (of a)` is the class of the generator in the presented group. -/
theorem rootVec_inv_letter {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    (r : FreeGroup X) (a : X) :
    rootVec K r ((FreeGroup.of a)⁻¹) a =
      -(MonoidAlgebra.of K (OneRelatorGroup r) (presentRho r (FreeGroup.of a)⁻¹)) := by
  rw [rootVec_apply, foxD_inv_of, if_pos rfl, map_neg, presentAlg_of]

/-- The `a`-component of the Fox vector of a single generator is a unit. -/
theorem isUnit_rootVec_letter {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    (r : FreeGroup X) (a : X) : IsUnit (rootVec K r (FreeGroup.of a) a) := by
  rw [rootVec_of_letter]
  exact isUnit_one

/-- The `a`-component of the Fox vector of an inverse generator is a unit (up to sign, it is a
single group element of `K[⟨X | r⟩]`). -/
theorem isUnit_rootVec_inv_letter {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    (r : FreeGroup X) (a : X) : IsUnit (rootVec K r ((FreeGroup.of a)⁻¹) a) := by
  rw [rootVec_inv_letter]
  refine IsUnit.neg (IsUnit.map (MonoidAlgebra.of K (OneRelatorGroup r)) ?_)
  exact ⟨Units.mk (presentRho r (FreeGroup.of a)⁻¹) (presentRho r (FreeGroup.of a)⁻¹)⁻¹
    (mul_inv_cancel _) (inv_mul_cancel _), rfl⟩

/-- A one-letter root: the `a`-component of its Fox vector is a unit. -/
theorem isUnit_rootVec_letterPow {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    (r : FreeGroup X) (a : X) (s : Bool) :
    IsUnit (rootVec K r (Work.OROneRel.letterPow a s) a) := by
  cases s
  · rw [Work.OROneRel.letterPow_false]
    exact isUnit_rootVec_inv_letter r a
  · rw [Work.OROneRel.letterPow_true]
    exact isUnit_rootVec_letter r a

theorem lyndonIndependence_of_relatorNorm_le_one {X : Type*} [DecidableEq X] {K : Type*} [Field K]
    (r u : FreeGroup X) (l : ℕ) (hpos : 1 ≤ l) (hpow : r = u ^ l)
    (hpp : ¬ Work.OROneRel.IsProperPower u) (hn : Work.OROneRel.relatorNorm u ≤ 1) :
    Work.ORLyndon.LyndonIndependence K r u := by
  rcases Work.OROneRel.eq_one_or_exists_letterPow_of_relatorNorm_le_one hn with h1 | ⟨a, s, rfl⟩
  · exact absurd (h1.symm ▸ Work.OROneRel.isProperPower_one) hpp
  · subst hpow
    have hord : orderOf (presentRho (Work.OROneRel.letterPow a s ^ l)
        (Work.OROneRel.letterPow a s)) = l := by
      simpa using (Work.OROneRel.kmsRoot_of_letterPow a s l hpos).1
    exact lyndon_independence_of_rootVec_isUnit' _ _ l hpos rfl hord a
      (isUnit_rootVec_letterPow _ a s)

end Work.ORLyndon

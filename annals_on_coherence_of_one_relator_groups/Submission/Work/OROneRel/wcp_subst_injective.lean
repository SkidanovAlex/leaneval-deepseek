/-
# Injectivity of the Case-2 substitution `t ↦ t ^ p`, `x ↦ x * t ^ (-q)`

The substitution `Work.OROneRel.subst t x p q` of `HNNStep` sends the generator `t` to `t ^ p`,
the generator `x` to `x * t ^ (-q)` and fixes every other generator.  This file proves that it is
injective whenever `x ≠ t` and `p ≠ 0` (`wcp_subst_injective`), the statement needed to transport a
counterexample along the Case-2 substitution of the Freiheitssatz.

The argument is a factorisation: the substitution is the composite

  `subst t x p q = wcpTransvect t x (-q) ∘ powSubst t p`

of the Nielsen substitution `t ↦ t ^ p` (which is injective for `p ≠ 0`,
`Work.OROneRel.powSubst_injective`) with the elementary *transvection*
`wcpTransvect t x q : x ↦ x * t ^ q`, fixing every other generator.  For `x ≠ t` the transvection
is an automorphism of `F α` -- its inverse is `wcpTransvect t x (-q)` (`wcpTransvect_comp`) -- hence
injective, and a composite of injective maps is injective.
-/
import Mathlib
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.powSubst_injective

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The elementary Nielsen transvection `x ↦ x * t ^ q`, fixing every other generator. -/
noncomputable def wcpTransvect (t x : α) (q : ℤ) : FreeGroup α →* FreeGroup α := by
  classical
  exact FreeGroup.lift fun a =>
    if a = x then FreeGroup.of x * (FreeGroup.of t) ^ q else FreeGroup.of a

theorem wcpTransvect_of_eq {t x : α} (q : ℤ) :
    wcpTransvect t x q (FreeGroup.of x) = FreeGroup.of x * (FreeGroup.of t) ^ q := by
  classical
  rw [wcpTransvect, FreeGroup.lift_apply_of]
  simp

theorem wcpTransvect_of_ne {t x a : α} (q : ℤ) (h : a ≠ x) :
    wcpTransvect t x q (FreeGroup.of a) = FreeGroup.of a := by
  classical
  rw [wcpTransvect, FreeGroup.lift_apply_of]
  simp [h]

/-- For `x ≠ t` the transvection `x ↦ x * t ^ q` is an automorphism: `wcpTransvect t x (-q)` is a
two-sided inverse of it. -/
theorem wcpTransvect_comp {t x : α} (hxt : x ≠ t) (q : ℤ) :
    (wcpTransvect t x (-q)).comp (wcpTransvect t x q) = MonoidHom.id (FreeGroup α) := by
  apply FreeGroup.ext_hom
  intro a
  show wcpTransvect t x (-q) (wcpTransvect t x q (FreeGroup.of a)) = FreeGroup.of a
  by_cases ha : a = x
  · subst ha
    rw [wcpTransvect_of_eq q, map_mul, map_zpow, wcpTransvect_of_eq (-q),
      wcpTransvect_of_ne (-q) (Ne.symm hxt)]
    group
  · rw [wcpTransvect_of_ne q ha, wcpTransvect_of_ne (-q) ha]

/-- For `x ≠ t` the transvection `x ↦ x * t ^ q` is injective. -/
theorem wcpTransvect_injective {t x : α} (hxt : x ≠ t) (q : ℤ) :
    Function.Injective (wcpTransvect t x q) := by
  intro a b hab
  have h := congrArg (wcpTransvect t x (-q)) hab
  rw [show wcpTransvect t x (-q) (wcpTransvect t x q a) = a from
      DFunLike.congr_fun (wcpTransvect_comp hxt q) a,
    show wcpTransvect t x (-q) (wcpTransvect t x q b) = b from
      DFunLike.congr_fun (wcpTransvect_comp hxt q) b] at h
  exact h

/-- The Case-2 substitution is the Nielsen substitution `t ↦ t ^ p` followed by the transvection
`x ↦ x * t ^ (-q)`. -/
theorem wcp_subst_factor {t x : α} (hxt : x ≠ t) (p q : ℤ) :
    Work.OROneRel.subst t x p q = (wcpTransvect t x (-q)).comp (powSubst t p) := by
  apply FreeGroup.ext_hom
  intro a
  rcases eq_or_ne a t with rfl | hat
  · rw [MonoidHom.comp_apply, powSubst_of_eq, map_zpow, wcpTransvect_of_ne (-q) (Ne.symm hxt)]
    rw [Work.OROneRel.subst, FreeGroup.lift_apply_of]
    simp [substFun]
  · rcases eq_or_ne a x with rfl | hax
    · rw [MonoidHom.comp_apply, powSubst_of_ne hxt, wcpTransvect_of_eq (-q)]
      rw [Work.OROneRel.subst, FreeGroup.lift_apply_of]
      simp [substFun, hxt]
    · rw [MonoidHom.comp_apply, powSubst_of_ne hat, wcpTransvect_of_ne (-q) hax]
      rw [Work.OROneRel.subst, FreeGroup.lift_apply_of]
      simp [substFun, hat, hax]

theorem wcp_subst_injective {α : Type u} (t x : α) (p q : ℤ) (hxt : x ≠ t) (hp : p ≠ 0) :
    Function.Injective (Work.OROneRel.subst t x p q) := by
  rw [wcp_subst_factor hxt p q]
  exact fun a b hab => powSubst_injective t p hp (wcpTransvect_injective hxt (-q) hab)

end Work.OROneRel

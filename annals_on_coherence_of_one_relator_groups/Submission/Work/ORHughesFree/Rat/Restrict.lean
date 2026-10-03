/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Restriction of scalars for rational semirings, and the complexity of `Rat(V) ⊆ Rat(U)`

A rational `Γ`-semiring structure on a ring `R` restricts along a subgroup `V ≤ Γ` to a rational
`V`-semiring structure with the same rational operation (`RationalUSemiring.restrict`).  This is
the tool that makes the *diagram* of [JZLA20, §4.3] (the commutativity of

`Rat(E^×H) → Rat(E^×G) → D_{G,A}` with `Rat(E^×H) → D_{H,A}`)

a formal consequence of the universal property of `Rat`: by `RatU.lift_unique` a morphism of
rational `V`-semirings out of `Rat(V)` is unique, so `RatU.lift R r` composed with the canonical
map `Rat(V) → Rat(U)` (`RatU.ofSubgroup`) is `RatU.lift R (restrict V r)`.

As an application we obtain that the *complexity* `Tree` of [JZLA20, §4.2] is preserved by the
inclusions: `Tree_V(β) = Tree_U(RatU.ofSubgroup V β)` for `β : Rat(V)`.  This is the statement
"DHS04, Theorem 5.7" in the form in which [JZLA20, Theorem 6.1] uses it: the complexity of an
element of `Rat(U)` is computed inside `Rat(source(α))`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Rat.Source
import Submission.Work.ORHughesFree.Rat.ratComplexity_model
import Submission.Work.ORHughesFree.Rat.TreeModel

set_option autoImplicit false

namespace Work.ORHughesFree

namespace RationalUSemiring

/-- Two rational `Γ`-semiring structures with the same rational operation and the same two
`Γ`-actions are equal (the remaining fields are propositions). -/
@[ext]
theorem ext {U : Type} [Group U] {R : Type} [Semiring R] {r s : RationalUSemiring U R}
    (hrat : r.ratOp = s.ratOp) (hsl : r.smul = s.smul) (hsr : r.smulRight = s.smulRight) :
    r = s := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := r
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := s
  dsimp only at hrat hsl hsr
  subst hrat; subst hsl; subst hsr
  rfl

/-- **Restriction of scalars**: a rational `Γ`-semiring structure on `R` restricts to a rational
`V`-semiring structure on `R` along an inclusion `V ≤ Γ`. -/
noncomputable def restrict {Γ : Type} [Group Γ] {R : Type} [Semiring R]
    (V : Subgroup Γ) (r : RationalUSemiring Γ R) : RationalUSemiring ↥V R where
  ratOp := r.ratOp
  ratOp_zero := r.ratOp_zero
  smul v x := r.smul (v : Γ) x
  smulRight x v := r.smulRight x (v : Γ)
  smul_eq_mul v x := r.smul_eq_mul (v : Γ) x
  smulRight_eq_mul x v := r.smulRight_eq_mul x (v : Γ)
  smul_mul u v := by simpa using r.smul_mul (u : Γ) (v : Γ)
  smul_one_one := by simpa using r.smul_one_one
  smulRight_one_one := by simpa using r.smulRight_one_one
  smulRight_one v := by simpa using r.smulRight_one (v : Γ)
  rat_smul u v x := by simpa using r.rat_smul (u : Γ) (v : Γ) x

@[simp]
theorem restrict_ratOp {Γ : Type} [Group Γ] {R : Type} [Semiring R] (V : Subgroup Γ)
    (r : RationalUSemiring Γ R) : (restrict V r).ratOp = r.ratOp := rfl

@[simp]
theorem restrict_smul {Γ : Type} [Group Γ] {R : Type} [Semiring R] (V : Subgroup Γ)
    (r : RationalUSemiring Γ R) (v : ↥V) (x : R) :
    (restrict V r).smul v x = r.smul (v : Γ) x := rfl

@[simp]
theorem restrict_smulRight {Γ : Type} [Group Γ] {R : Type} [Semiring R] (V : Subgroup Γ)
    (r : RationalUSemiring Γ R) (x : R) (v : ↥V) :
    (restrict V r).smulRight x v = r.smulRight x (v : Γ) := rfl

theorem restrict_map_smul {Γ : Type} [Group Γ] {V : Subgroup Γ} {R : Type} [Semiring R]
    {r : RationalUSemiring Γ R} {v : ↥V} {x : R} :
    (restrict V r).smul v x = r.smul (v : Γ) x := rfl

end RationalUSemiring

/-- The rational `V`-semiring structure of the finite rooted trees does not depend on `V`. -/
theorem RationalUSemiring.restrict_treeRational {U : Type} [Group U] (V : Subgroup U) :
    RationalUSemiring.restrict V (treeRational U) = treeRational ↥V := by
  apply RationalUSemiring.ext
  · rfl
  · funext v x; rfl
  · funext x v; rfl

namespace RatU

/-- The canonical map `Rat(V) →+* Rat(U)` of `Rat/Source.lean` is the universal morphism of
rational `V`-semirings attached to the restriction of scalars of `Rat(U)`. -/
theorem ofSubgroup_eq {U : Type} [Group U] (V : Subgroup U) :
    ofSubgroup V = lift (RatU U) (RationalUSemiring.restrict V (rational (U := U))) := by
  refine lift_unique (RatU U) (restrictScalars V) _ ⟨?_, ?_, ?_⟩
  · intro x; exact (lift_isHom (RatU U) (RationalUSemiring.restrict V (rational (U := U)))).map_rat x
  · intro v x;
    exact (lift_isHom (RatU U) (RationalUSemiring.restrict V (rational (U := U)))).map_smul v x
  · intro x v;
    exact (lift_isHom (RatU U) (RationalUSemiring.restrict V (rational (U := U)))).map_smulRight x v

/-- **The diagram of [JZLA20, §4.3]**, abstractly: the universal morphism `Rat(Γ) → R` composed
with the canonical map `Rat(V) → Rat(Γ)` is the universal morphism `Rat(V) → R` for the restricted
rational `V`-semiring structure on `R`. -/
theorem lift_comp_ofSubgroup {Γ : Type} [Group Γ] (V : Subgroup Γ) (R : Type) [Semiring R]
    (r : RationalUSemiring Γ R) :
    (lift R r).comp (ofSubgroup V) = lift R (RationalUSemiring.restrict V r) := by
  rw [ofSubgroup_eq]
  refine lift_unique (U := ↥V) R (RationalUSemiring.restrict V r) _ ⟨?_, ?_, ?_⟩
  · intro x
    show (lift R r) ((lift (RatU Γ) (RationalUSemiring.restrict V (rational (U := Γ))))
        (rational.ratOp x)) = r.ratOp ((lift R r) ((lift (RatU Γ)
        (RationalUSemiring.restrict V (rational (U := Γ)))) x))
    rw [(lift_isHom (RatU Γ) (RationalUSemiring.restrict V (rational (U := Γ)))).map_rat x]
    exact (lift_isHom R r).map_rat _
  · intro v x
    show (lift R r) ((lift (RatU Γ) (RationalUSemiring.restrict V (rational (U := Γ))))
        (rational.smul v x)) = r.smul (v : Γ) ((lift R r) ((lift (RatU Γ)
        (RationalUSemiring.restrict V (rational (U := Γ)))) x))
    rw [(lift_isHom (RatU Γ) (RationalUSemiring.restrict V (rational (U := Γ)))).map_smul v x]
    exact (lift_isHom R r).map_smul (v : Γ) _
  · intro x v
    show (lift R r) ((lift (RatU Γ) (RationalUSemiring.restrict V (rational (U := Γ))))
        (rational.smulRight x v)) = r.smulRight ((lift R r) ((lift (RatU Γ)
        (RationalUSemiring.restrict V (rational (U := Γ)))) x)) (v : Γ)
    rw [(lift_isHom (RatU Γ) (RationalUSemiring.restrict V (rational (U := Γ)))).map_smulRight x v]
    exact (lift_isHom R r).map_smulRight _ (v : Γ)

end RatU

namespace Rat

/-- **The complexity is preserved by the inclusion `Rat(V) ⊆ Rat(U)`** ([DHS04, Theorem 5.7] in
the form used by [JZLA20, §4.3]): for `β : Rat(V)`, the complexity of `β` inside `Rat(V)` equals
the complexity of its image in `Rat(U)`. -/
theorem treeOfRat_ofSubgroup {U : Type} [Group U] (V : Subgroup U) (β : RatU ↥V) :
    treeOfRat U (RatU.ofSubgroup V β) = treeOfRat ↥V β := by
  have h := congrFun (congrArg DFunLike.coe
    (RatU.lift_comp_ofSubgroup V Tree (treeRational U))) β
  rw [RationalUSemiring.restrict_treeRational] at h
  exact h

end Rat

end Work.ORHughesFree

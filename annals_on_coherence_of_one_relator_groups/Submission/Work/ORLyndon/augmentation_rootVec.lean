import Mathlib
import Submission.Work.ORLyndon.powDefs
import Submission.Work.ORLyndon.Augmentation
import Submission.Work.OROneRel.eps_rightPow

/-!
# The augmentation of the Fox vector of the root

Let `α` be a set of generators, `K` a field, `r : F(α)` a relator, `u : F(α)` a root of `r`, and
`x : α` a letter.  The `x`-component `(∂u/∂x)_x` of the Fox vector of the root is an element of the
group algebra `K[⟨α | r⟩]` (`Work.ORLyndon.rootVec`), obtained by pushing the Fox derivative
`∂u/∂x ∈ K[F(α)]` along the algebra map `K[F(α)] → K[⟨α | r⟩]` induced by the presentation.

The classical identity of the Fox calculus

`ε(∂u/∂x) = σ_x(u)`,

"the augmentation of the Fox derivative is the exponent sum of the letter", lifts to the one-relator
group because the presentation map preserves the augmentation (both augmentations are simply "sum of
the coefficients").  This file proves

`Work.ORLyndon.augmentation_rootVec : ε_{K[⟨α | r⟩]}(rootVec K r u x) = ((eps x u : ℤ) : K)`,

where `Work.OROneRel.eps x u` is the exponent sum of `x` in `u`.

## Structure of the proof

* `augmentation_mapDomainRingHom_aux`: the augmentation is natural, `ε_H (mapDomain K f a) = ε_G a`,
  because both sides sum the coefficients of `a`, which the map merely permutes along the fibers of
  `f`.  Hence `augmentation_presentAlg`, the same statement for the presentation map `presentAlg K r`;
* `augmentation_foxD_aux`: the Fox calculus identity `ε(∂u/∂x) = σ_x(u)` in the free group algebra,
  by `FreeGroup.induction_on`: the Fox derivative is a derivation (`foxD_mul`, `foxD_inv`) and the
  augmentation kills the group elements (`augmentation_of`), so `ε ∘ ∂_x` is additive in `u`, as is
  `eps x` (`Work.OROneRel.epsc_mul`, `epsc_inv`); the two agree on the generators, by `foxD_of`
  versus `Work.OROneRel.epsc_of_eq` / `epsc_of_ne`;
* `augmentation_rootVec`: the two ingredients, using `rootVec_apply` and
  `presentAlg = MonoidAlgebra.mapDomainRingHom K (presentRho r)`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

universe u v w

variable {X : Type u} {K : Type v}

/-- **Naturality of the augmentation.**  The augmentation of a group algebra is unchanged by the
algebra map `K[G] →+* K[H]` induced by a monoid homomorphism `G →* H`: both augmentations sum the
coefficients of an element of `K[G]`, which `mapDomainRingHom` merely permutes along the fibers of
`f`. -/
theorem augmentation_mapDomainRingHom_aux {K : Type v} [CommSemiring K] {G : Type u} {H : Type w}
    [Monoid G] [Monoid H] (f : G →* H) (a : MonoidAlgebra K G) :
    augmentation K H (MonoidAlgebra.mapDomainRingHom K f a) = augmentation K G a := by
  rw [augmentation_apply, augmentation_apply, MonoidAlgebra.mapDomainRingHom_apply,
    MonoidAlgebra.coeff_mapDomain]
  exact Finsupp.sum_mapDomain_index (h := fun _ m => m) (f := ⇑f) (s := a.coeff)
    (fun _ => rfl) (fun _ _ _ => rfl)

section

variable [Field K] [DecidableEq X]

/-- The augmentation of the group algebra is preserved by the algebra map induced by the
presentation `F(α) →* ⟨α | r⟩`. -/
theorem augmentation_presentAlg (r : FreeGroup X) (a : MonoidAlgebra K (FreeGroup X)) :
    augmentation K (OneRelatorGroup r) (presentAlg K r a) =
      augmentation K (FreeGroup X) a :=
  augmentation_mapDomainRingHom_aux (presentRho r) a

/-- **The Fox calculus identity `ε(∂u/∂x) = σ_x(u)` in the free group algebra.**  The augmentation of
the Fox derivative of an element `u` of the free group with respect to the letter `x` is the exponent
sum of `x` in `u`.

Both sides are additive in `u` — on the left because the Fox derivative is a derivation (`foxD_mul`,
`foxD_inv`) and the augmentation kills every group element (`augmentation_of`), on the right by
additivity of the exponent sum (`Work.OROneRel.epsc_mul`, `epsc_inv`) — so it suffices to check the
identity on the generators, where `foxD_of` gives `δ_{xy}` and `Work.OROneRel.epsc_of_eq` /
`epsc_of_ne` give the same value. -/
theorem augmentation_foxD_aux (x : X) (u : FreeGroup X) :
    augmentation K (FreeGroup X) (foxD (K := K) x u) =
      ((Work.OROneRel.eps x u : ℤ) : K) := by
  classical
  refine FreeGroup.induction_on u ?_ ?_ ?_ ?_
  · rw [foxD_one, map_zero, Work.OROneRel.epsc_one]
    simp
  · intro y
    rw [foxD_of]
    by_cases hy : y = x
    · rw [if_pos hy, map_one, ← hy, Work.OROneRel.epsc_of_eq]
      simp
    · rw [if_neg hy, map_zero, Work.OROneRel.epsc_of_ne (fun h' : x = y => hy h'.symm)]
      simp
  · intro y ih
    rw [foxD_inv, map_neg, augmentation_mul, augmentation_of, one_mul, ih,
      Work.OROneRel.epsc_inv, Int.cast_neg]
  · intro a b iha ihb
    rw [foxD_mul, augmentation_add, augmentation_mul, augmentation_of, one_mul, iha, ihb,
      Work.OROneRel.epsc_mul, Int.cast_add]

/-- **The augmentation of the root Fox vector.**  The `x`-component of the Fox vector of a root `u`,
pushed into the group algebra of the one-relator group `⟨α | r⟩`, has augmentation the exponent sum
of `x` in `u`. -/
theorem augmentation_rootVec {K : Type v} [Field K] {α : Type u} [DecidableEq α]
    (r u : FreeGroup α) (x : α) :
    Work.ORLyndon.augmentation K (OneRelatorGroup r) (rootVec K r u x) =
      ((Work.OROneRel.eps x u : ℤ) : K) := by
  rw [rootVec_apply, augmentation_presentAlg, augmentation_foxD_aux]

end

end Work.ORLyndon

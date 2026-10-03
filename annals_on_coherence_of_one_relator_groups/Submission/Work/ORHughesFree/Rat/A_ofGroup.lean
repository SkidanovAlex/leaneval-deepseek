import Mathlib
import Submission.Work.ORHughesFree.Rat.exists_source_subgroup_weak
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Rat.Restrict
import Submission.Work.ORHughesFree.Rat.OfGroup

/-!
# The elements of complexity one in `A V` are group elements of `V`

`Rat.A V` is the image of the canonical map `Rat(V) → Rat(U)`
(`RatU.ofSubgroup V`), where `V ≤ U`.  The group `U` embeds in `Rat(U)` through
`RatU.ofGroup`, and this file shows that this embedding meets `A V` exactly in `V`:
`RatU.ofGroup u ∈ Rat.A V` forces `u ∈ V`.

The two ingredients are

* the compatibility of the complexity map with the inclusion `Rat(V) ⊆ Rat(U)`
  (`Rat.treeOfRat_ofSubgroup`), which together with `treeOfRat_eq_one_iff` shows that an element of
  `Rat(V)` mapping to a group element of `Rat(U)` is itself a group element of `Rat(V)`;
* the injectivity of `RatU.ofGroup : U → Rat(U)`, proved by evaluating the universal morphism in
  the monoid algebra `ℕ[U]` carrying the rational `U`-semiring structure with trivial `⋄` and the
  two actions given by multiplication by `single u 1`.
-/

set_option autoImplicit false

namespace Work.ORHughesFree

namespace RatU

/-- The monoid algebra `ℕ[U]` carries a rational `U`-semiring structure for which the rational
operation is trivial (`x ⋄ = 0`) and both `U`-actions are multiplication by the image of `U`.  In
this model the group `U` embeds faithfully, with `u` mapping to `single u 1`. -/
noncomputable def monoidAlgebraRational (U : Type) [Group U] :
    RationalUSemiring U (MonoidAlgebra ℕ U) where
  ratOp := 0
  ratOp_zero := rfl
  smul u x := MonoidAlgebra.single u 1 * x
  smulRight x u := x * MonoidAlgebra.single u 1
  smul_eq_mul u x := by simp
  smulRight_eq_mul x u := by simp
  smul_mul u v := by simp [MonoidAlgebra.single_mul_single]
  smul_one_one := by rw [mul_one, MonoidAlgebra.one_def]
  smulRight_one_one := by rw [one_mul, MonoidAlgebra.one_def]
  smulRight_one u := by rw [one_mul, mul_one]
  rat_smul u v r := by simp

variable {U : Type} [Group U]

/-- The universal morphism `Rat(U) → ℕ[U]` sends `ofGroup u` to `single u 1`. -/
theorem lift_monoidAlgebra_ofGroup (u : U) :
    RatU.lift (MonoidAlgebra ℕ U) (monoidAlgebraRational U) (ofGroup u)
      = MonoidAlgebra.single u 1 := by
  rw [ofGroup_eq_rational]
  have h := (lift_isHom (MonoidAlgebra ℕ U) (monoidAlgebraRational U)).map_smul u (1 : RatU U)
  rw [h, map_one]
  simp [monoidAlgebraRational]

/-- **The group `U` embeds in `Rat(U)`**: the map `u ↦ ofGroup u` is injective. -/
theorem ofGroup_injective : Function.Injective (ofGroup : U → RatU U) := by
  intro u v h
  have h' := congrArg (RatU.lift (MonoidAlgebra ℕ U) (monoidAlgebraRational U)) h
  rw [lift_monoidAlgebra_ofGroup u, lift_monoidAlgebra_ofGroup v] at h'
  exact MonoidAlgebra.single_left_injective (r := 1) one_ne_zero h'

end RatU

namespace Rat

/-- An element of `Rat(V)` whose image in `Rat(U)` is the image of a group element `u : U` is
itself the image of a group element `v : V`, and `u = v`. -/
theorem A_ofGroup {U : Type} [Group U] {V : Subgroup U} {u : U} :
    Work.ORHughesFree.RatU.ofGroup u ∈ Work.ORHughesFree.Rat.A V → u ∈ V := by
  rintro ⟨β, hβ⟩
  have h1 : treeOfRat ↥V β = 1 := by
    rw [← treeOfRat_ofSubgroup V β, hβ, treeOfRat_ofGroup]
  obtain ⟨v, hv⟩ := (treeOfRat_eq_one_iff β).mp h1
  have h2 : RatU.ofGroup u = RatU.ofGroup (v : U) := by
    rw [← hβ, hv, ofSubgroup_ofGroup]
  have h3 : u = (v : U) := RatU.ofGroup_injective h2
  rw [h3]
  exact v.2

end Rat

end Work.ORHughesFree

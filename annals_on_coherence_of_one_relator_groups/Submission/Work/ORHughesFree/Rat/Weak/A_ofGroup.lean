import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Rat.Restrict
import Submission.Work.ORHughesFree.Rat.OfGroup
import Submission.Work.ORHughesFree.Rat.ratComplexity_model

/-!
# The elements of complexity one in `Rat.A V` are group elements of `V`

`Rat.A V` is the image of the canonical map `Rat(V) → Rat(U)` (`RatU.ofSubgroup V`), where
`V ≤ U`.  The group `U` embeds in `Rat(U)` through `RatU.ofGroup`, and this file shows that this
embedding meets `A V` exactly in `V`: `RatU.ofGroup u ∈ Rat.A V` forces `u ∈ V`.

The two ingredients are

* the compatibility of the complexity map with the inclusion `Rat(V) ⊆ Rat(U)`
  (`Rat.treeOfRat_ofSubgroup`, `Rat/Restrict.lean`), which together with `Rat.treeOfRat_eq_one_iff`
  (`Rat/OfGroup.lean`) shows that an element of `Rat(V)` mapping to a group element of `Rat(U)` is
  itself a group element of `Rat(V)`;
* the injectivity of `RatU.ofGroup : U → Rat(U)`, proved by evaluating the universal morphism in
  the monoid algebra `ℕ[U]` carrying the rational `U`-semiring structure with trivial `⋄` and the
  two actions given by multiplication by `single u 1`.

This is a self-contained copy of `Rat.A_ofGroup`
(`Submission/Work/ORHughesFree/Rat/A_ofGroup.lean`) in the namespace
`Work.ORHughesFree.Rat.Weak`: the original file imports
`Rat/exists_source_subgroup_weak.lean`, a cycle for the intended consumer, so the injectivity of
`RatU.ofGroup` is re-derived here from `Rat/SourceFrame.lean`, `Rat/Restrict.lean`,
`Rat/OfGroup.lean` and `Rat/ratComplexity_model.lean` alone.

The auxiliary declarations are `private`, so that this module can be imported together with the
other `Weak` ports (in particular `Rat/Weak/ofGroup_injective.lean`, which contains the same
monoid-algebra argument under its own name) without a name clash.
-/

namespace Work.ORHughesFree.Rat.Weak

open Work.ORHughesFree

/-- The monoid algebra `ℕ[U]` carries a rational `U`-semiring structure for which the rational
operation is trivial (`x ⋄ = 0`) and both `U`-actions are multiplication by the image of `U`.  In
this model the group `U` embeds faithfully, with `u` mapping to `single u 1`. -/
private noncomputable def monoidAlgebraRational (U : Type) [Group U] :
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

/-- The universal morphism `Rat(U) → ℕ[U]` sends `ofGroup u` to `single u 1`. -/
private theorem lift_monoidAlgebra_ofGroup {U : Type} [Group U] (u : U) :
    RatU.lift (MonoidAlgebra ℕ U) (monoidAlgebraRational U) (RatU.ofGroup u)
      = MonoidAlgebra.single u 1 := by
  rw [RatU.ofGroup_eq_rational]
  have h := (RatU.lift_isHom (MonoidAlgebra ℕ U) (monoidAlgebraRational U)).map_smul u (1 : RatU U)
  rw [h, map_one]
  simp [monoidAlgebraRational]

/-- **The group `U` embeds in `Rat(U)`**: the map `u ↦ ofGroup u` is injective. -/
private theorem ofGroup_injective {U : Type} [Group U] :
    Function.Injective (fun u : U => RatU.ofGroup u) := by
  intro u v h
  have h' := congrArg (RatU.lift (MonoidAlgebra ℕ U) (monoidAlgebraRational U)) h
  rw [lift_monoidAlgebra_ofGroup u, lift_monoidAlgebra_ofGroup v] at h'
  exact MonoidAlgebra.single_left_injective (r := 1) one_ne_zero h'

/-- Port of `Rat.A_ofGroup` (file `Submission/Work/ORHughesFree/Rat/A_ofGroup.lean`) into the namespace `Work.ORHughesFree.Rat.Weak`. The original file imports `Rat/exists_source_subgroup_weak.lean`, a cycle for the intended consumer, so the proof has to be reproduced using only `Rat/SourceFrame.lean`, `Rat/Restrict.lean` (for `Rat.treeOfRat_ofSubgroup`), `Rat/OfGroup.lean` and `Rat/ratComplexity_model.lean`; the original proof may be read for guidance. In particular the injectivity of `RatU.ofGroup : U → RatU U` (proved in the same original file by evaluating in `MonoidAlgebra ℕ U`) has to be re-derived here. -/
theorem A_ofGroup {U : Type} [Group U] {V : Subgroup U} {u : U} :
    Work.ORHughesFree.RatU.ofGroup u ∈ Work.ORHughesFree.Rat.A V → u ∈ V := by
  rintro ⟨β, hβ⟩
  -- `treeOfRat_ofSubgroup` identifies the complexity of `β : Rat(V)` with that of its image in
  -- `Rat(U)`, which here is the complexity `1` of the group element `u`.
  have h1 : Rat.treeOfRat ↥V β = 1 := by
    have h := Rat.treeOfRat_ofSubgroup V β
    rw [hβ, Rat.treeOfRat_ofGroup] at h
    exact h.symm
  -- hence `β` is itself a group element of `V`
  obtain ⟨v, hv⟩ := (Rat.treeOfRat_eq_one_iff β).mp h1
  have h2 : Work.ORHughesFree.RatU.ofGroup u
      = Work.ORHughesFree.RatU.ofGroup (v : U) := by
    rw [← hβ, hv, Rat.ofSubgroup_ofGroup]
  -- and the embedding of `U` in `Rat(U)` is injective
  have h3 : u = (v : U) := ofGroup_injective h2
  rw [h3]
  exact v.2

end Work.ORHughesFree.Rat.Weak

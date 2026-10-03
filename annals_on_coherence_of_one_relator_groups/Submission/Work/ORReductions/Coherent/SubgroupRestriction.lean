/-
The "restriction to a subgroup" map on group algebras.

For a subgroup `H ≤ G` and a semiring `K`, the group algebra `K[G]` maps additively onto
`K[H]` by keeping the coefficients of an element on `H` and discarding those outside `H`.
This is an additive retraction of the canonical inclusion
`subgroupAlgMap H K : K[H] →+* K[G]`, and it is right `K[H]`-linear.
-/
import Mathlib
import Submission.Work.ORReductions.SubgroupAlg

namespace Work.ORReductions.Coherent

open MonoidAlgebra

variable {G : Type*} [Group G]

/-- The additive map `K[G] → K[H]` keeping the coefficients of `x : K[G]` on `H`:
it sends `single g c` to `single g c` (viewed in `K[H]`) when `g ∈ H`, and to `0` otherwise. -/
noncomputable def restrictToSubgroup (H : Subgroup G) (K : Type*) [Semiring K] :
    MonoidAlgebra K G →+ MonoidAlgebra K H := by
  classical
  refine (Finsupp.liftAddHom (fun g : G =>
    (if hg : g ∈ H then
      ({ toFun := fun c : K => MonoidAlgebra.single (⟨g, hg⟩ : H) c
         map_zero' := by simp
         map_add' := fun a b => by simp [MonoidAlgebra.single_add] } : K →+ MonoidAlgebra K H)
     else 0))).comp
    { toFun := MonoidAlgebra.coeff
      map_zero' := rfl
      map_add' := fun a b => MonoidAlgebra.coeff_add a b }

lemma restrictToSubgroup_single_of_mem (H : Subgroup G) (K : Type*) [Semiring K]
    (g : G) (c : K) (hg : g ∈ H) :
    restrictToSubgroup H K (MonoidAlgebra.single g c) = MonoidAlgebra.single (⟨g, hg⟩ : H) c := by
  classical
  rw [restrictToSubgroup, AddMonoidHom.comp_apply]
  change (Finsupp.liftAddHom (fun g : G =>
    (if hg : g ∈ H then
      ({ toFun := fun c : K => MonoidAlgebra.single (⟨g, hg⟩ : H) c
         map_zero' := by simp
         map_add' := fun a b => by simp [MonoidAlgebra.single_add] } : K →+ MonoidAlgebra K H)
     else 0))) (Finsupp.single g c) = _
  rw [Finsupp.liftAddHom_apply_single]
  rw [dif_pos hg]
  rfl

lemma restrictToSubgroup_single_of_notMem (H : Subgroup G) (K : Type*) [Semiring K]
    (g : G) (c : K) (hg : g ∉ H) :
    restrictToSubgroup H K (MonoidAlgebra.single g c) = 0 := by
  classical
  rw [restrictToSubgroup, AddMonoidHom.comp_apply]
  change (Finsupp.liftAddHom (fun g : G =>
    (if hg : g ∈ H then
      ({ toFun := fun c : K => MonoidAlgebra.single (⟨g, hg⟩ : H) c
         map_zero' := by simp
         map_add' := fun a b => by simp [MonoidAlgebra.single_add] } : K →+ MonoidAlgebra K H)
     else 0))) (Finsupp.single g c) = _
  rw [Finsupp.liftAddHom_apply_single]
  rw [dif_neg hg]
  rfl

end Work.ORReductions.Coherent

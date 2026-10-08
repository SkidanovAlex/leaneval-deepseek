import Mathlib
import Submission.Work.ThompsonFrobenius.BlueprintZJ
import Submission.Work.GlaubermanZJ.ZJ_eq
import Submission.Work.PGroup.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Z(J(P))` is natural under homomorphisms injective on `P` (blueprint vocabulary)

`Submission.Blueprint.ZJ P = J(P) ⊓ C_G(J(P))` is the `ZJ` of the blueprint.  Via
`Work.GlaubermanZJ.ZJ_eq`, on a finite subgroup `P` it coincides with the `Work.PGroup`
version `Work.PGroup.ZJ P = Z(J(P))`, the centre of Thompson's subgroup `J(P)` viewed inside
the ambient group.  The transport statement for the latter is already available as
`Work.PGroup.ZJ_map_of_ker_inf_eq_bot` (proved there with no finiteness assumption, for a
homomorphism whose kernel meets `P` trivially), so the blueprint statement follows by
rewriting along `ZJ_eq` on both sides.

The only extra point is that the hypothesis `f.ker ⊓ P = ⊥` is stated with the factors in the
other order than `Work.PGroup.ZJ_map_of_ker_inf_eq_bot` expects; this is handled by
`inf_comm`.  Note that `P.map f` need not live in a finite group, so its finiteness (needed to
apply `ZJ_eq`) is established from the surjection `P → P.map f` induced by `f`.
-/

set_option linter.style.haveILetI false

namespace Work.ThompsonFrobenius

theorem ZJ_map_of_ker_inf_eq_bot {G G' : Type*} [Group G] [Group G'] [Finite G] (f : G →* G') (P : Subgroup G) (hf : f.ker ⊓ P = ⊥) : (Submission.Blueprint.ZJ P).map f = Submission.Blueprint.ZJ (P.map f) := by
  haveI : Finite ↥P := inferInstance
  -- `P.map f` is the image of the finite group `P`, hence finite as a type, even though `G'`
  -- itself need not be finite.
  haveI : Finite ↥(P.map f) := by
    refine Finite.of_surjective
      (fun x : P => (⟨f x, Subgroup.mem_map_of_mem f x.2⟩ : P.map f)) ?_
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : P ⊓ f.ker = ⊥ := by rw [inf_comm]; exact hf
  rw [Work.GlaubermanZJ.ZJ_eq P, Work.GlaubermanZJ.ZJ_eq (P.map f)]
  exact (Work.PGroup.ZJ_map_of_ker_inf_eq_bot f P hker).symm

end Work.ThompsonFrobenius

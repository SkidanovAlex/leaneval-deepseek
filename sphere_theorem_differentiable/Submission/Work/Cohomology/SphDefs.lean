import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

/-!
# The sphere `S^(m-1)`, its caps, and the `ModuleCat` kernel of a functional

This file collects the elementary definitions shared by the Mayer–Vietoris computation of the
singular homology of the sphere (`Submission/Work/Cohomology/sphereHomologyTop.lean`), in a form
that is independent of the rest of the development:

* `sphSet m`, `sphTop m` — the unit sphere in `ℝ^m`, as a set and as a topological space;
* `capA m`, `capB m` — the two contractible caps of `S^(m+1)`, whose intersection `band m` is the
  equatorial band;
* `kerMod f` — the kernel of a `ℤ`-linear map `f`, as a `ModuleCat ℤ`.
-/

open CategoryTheory

namespace Work.Cohomology

noncomputable section

/-- The unit sphere `S^(m-1) = {x : ℝ^m | ‖x‖ = 1}`, as a set. -/
abbrev sphSet (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) := {x | ‖x‖ = 1}

/-- The unit sphere in `ℝ^m`, as a topological space. -/
abbrev sphTop (m : ℕ) : TopCat := TopCat.of ↥(sphSet m)

/-- The cap `{x ∈ S^(m+1) : x (last m) > -1/2}` (it contains the "north pole"). -/
def capA (m : ℕ) : Set (sphTop (m+1)) := {x | x.1 (Fin.last m) > -(1/2)}

/-- The cap `{x ∈ S^(m+1) : x (last m) < 1/2}` (it contains the "south pole"). -/
def capB (m : ℕ) : Set (sphTop (m+1)) := {x | x.1 (Fin.last m) < 1/2}

/-- The equatorial band `{-1/2 < x (last m) < 1/2} ⊆ S^(m+1)`, the intersection of the two caps. -/
def band (m : ℕ) : Set (sphTop (m+1)) := capA m ∩ capB m

/-- The kernel of a `ℤ`-linear map, as a `ModuleCat ℤ`.

The module structure on `↥(ker g)` is pinned to `Submodule.module` (the restriction of the
ambient structure) rather than to the canonical `AddCommGroup.toIntModule`, because it is the
former that Mathlib's constructions for submodules (`Submodule.subtype`, `LinearMap.codRestrict`,
`LinearEquiv.ofEq`, ...) use.  Over `ℤ` the two structures are equal, so this involves no loss of
generality (`Subsingleton (Module ℤ M)` for an abelian group `M`). -/
abbrev kerMod {M N : Type} [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (g : M →ₗ[ℤ] N) : ModuleCat ℤ :=
  @ModuleCat.of ℤ _ ↥(LinearMap.ker g) _ (Submodule.module (LinearMap.ker g))

/-- Flattening a nested subtype: `{z : {x // q x} // P z.1}` is homeomorphic to
`{x // q x ∧ P x}`. -/
def flatHomeo {α : Type*} [TopologicalSpace α] {q P : α → Prop} :
    {z : {x // q x} // P z.1} ≃ₜ {x : α // q x ∧ P x} :=
  { toFun := fun z => ⟨z.1.1, z.1.2, z.2⟩
    invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val) (fun z => ⟨z.1.2, z.2⟩)
    continuous_invFun := Continuous.subtype_mk
      (Continuous.subtype_mk continuous_subtype_val (fun x => x.2.1)) (fun x => x.2.2) }

end

end Work.Cohomology

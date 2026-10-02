import Mathlib
import Submission.Work.Thom.IsoPunct
import Submission.Work.Thom.ThomClass

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Tubular

open Work.TangentClasses

/-!
# Thom classes are invariant under a bundle isomorphism

An isomorphism of real bundles `e : Z ≅ Z'` over a common base `B` — with possibly *different* model
fibres `F`, `F'` and different gluing-data covers — induces a homeomorphism of the total spaces
`e.toHomeomorph : Z.TotalSpace ≃ₜ Z'.TotalSpace` which carries the zero section to the zero section,
hence the complement `E∖0` of the zero section of `Z` onto the complement `E'∖0` of the zero section
of `Z'`.  Passing to relative cohomology this is a bijection (a homeomorphism of *pairs*,
`Work.Thom.bijective_relCohMap_of_homeomorphA`), and it is compatible with the projections to `B`
(`π'∘e^{-1} = π`, since a bundle isomorphism lies over the base).

The Thom map of `Z'` therefore transports back to the Thom map of `Z`:

  `(e⁻¹)^*(π'^*(x) ⌣ τ') = π^*(x) ⌣ (e⁻¹)^*(τ')`

by naturality of the mixed cup product (`Work.Thom.mixedCupC_pairNatural`), which is precisely the
abstract transport theorem `Work.Thom.cupMap_transfer_fwdA`.  So if `τ` is a Thom class of `Z`, then
its image `(e⁻¹)^*τ` under the isomorphism of Thom pairs is a Thom class of `Z'`, and taking
`e = id` recovers the identity.  No orientability input is needed: an integral Thom class *is* the
orientation, and a bundle isomorphism transports it.

This is the tool that lets a Thom class — hence the Euler class, the Chern and Pontryagin classes
built from it — be moved between two presentations of the same bundle, in particular between gluing
data over different covers and different model fibres.  The statement is closed under the "same
fibre, different cover" case; the different-fibre case is exactly what a change of model fibre
(`Work.Thom.BundleIso` with `F ≠ F'`) needs.
-/

/-- **Existence of a Thom class is invariant under a bundle isomorphism.**  A Thom class of `Z`
transports along `e : Z ≅ Z'` to a Thom class of `Z'`, for bundles over the same base with
arbitrary model fibres and arbitrary covers. -/
theorem nonempty_thomClass_of_bundleIso {B : Type} [TopologicalSpace B] {F F' : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {ι ι' : Type} {Z : Work.TangentClasses.RealBundle B F ι}
    {Z' : Work.TangentClasses.RealBundle B F' ι'} (e : Work.Thom.BundleIso Z Z') {n : ℕ}
    (T : Work.Thom.ThomClass Z n) : Nonempty (Work.Thom.ThomClass Z' n) := by
  classical
  -- The inverse homeomorphism carries the punctured total space of `Z'` into that of `Z`.
  have hiff : ∀ x : Z'.TotalSpace, x ∈ Work.Thom.zeroComplement Z' ↔
      (e.toHomeomorph.symm x) ∈ Work.Thom.zeroComplement Z := by
    intro x
    constructor
    · intro hx
      exact e.symm.hom_ne_zero hx
    · intro hx
      have h2 : e.toHomeomorph (e.toHomeomorph.symm x) ∈ Work.Thom.zeroComplement Z' :=
        e.hom_ne_zero hx
      rwa [e.toHomeomorph.apply_symm_apply] at h2
  have hf : ∀ y ∈ Work.Thom.zeroComplement Z',
      (e.toHomeomorph.symm : C(Z'.TotalSpace, Z.TotalSpace)) y ∈ Work.Thom.zeroComplement Z :=
    fun y hy => (hiff y).mp hy
  -- A homeomorphism of pairs induces a bijection on relative cohomology, in every degree.
  have hbij : ∀ m, Function.Bijective (Work.Thom.relCohMap
      (e.toHomeomorph.symm : C(Z'.TotalSpace, Z.TotalSpace)) (Work.Thom.zeroComplement Z')
      (Work.Thom.zeroComplement Z) hf ℤ m).hom :=
    fun m => Work.Thom.bijective_relCohMap_of_homeomorphA (Work.Thom.zeroComplement Z')
      (Work.Thom.zeroComplement Z) e.toHomeomorph.symm hiff ℤ m
  -- A bundle isomorphism lies over the base: `π ∘ e⁻¹ = π'`.
  have hπ : (Work.Thom.bundleProj Z).comp (e.toHomeomorph.symm : C(Z'.TotalSpace, Z.TotalSpace))
      = Work.Thom.bundleProj Z' := by
    ext p; rfl
  refine ⟨⟨(Work.Thom.relCohMap (e.toHomeomorph.symm : C(Z'.TotalSpace, Z.TotalSpace))
      (Work.Thom.zeroComplement Z') (Work.Thom.zeroComplement Z) hf ℤ n).hom T.τ, ?_⟩⟩
  -- The transport of the Thom map along the map of pairs.
  exact Work.Thom.cupMap_transfer_fwdA (e.toHomeomorph.symm : C(Z'.TotalSpace, Z.TotalSpace))
    (Work.Thom.zeroComplement Z) (Work.Thom.zeroComplement Z') hf hbij
    (Work.Thom.bundleProj Z) (Work.Thom.bundleProj Z') hπ n T.τ T.isThom

end Work.Tubular

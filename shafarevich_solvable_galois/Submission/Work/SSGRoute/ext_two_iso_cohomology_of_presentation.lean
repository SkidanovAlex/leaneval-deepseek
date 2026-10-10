import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ext_one_iso_lattice_cohomology
import Submission.Work.SSGRoute.local_ext_h1_bridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The landing dictionary of `E1a`: `Ext²_G(X₃,Y) ≅ H¹(G, Hom_ℤ(X₁,Y))` for a presentation

For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` in `Rep Coeff G` with `X₂` projective and whose
*syzygy* `X₁` is a `ℤ`-lattice (free and finitely generated over `ℤ`), the composition of

* the degree shift `Work.SSGRoute.ext_shift_of_projective_presentation`
  (`Ext¹_G(X₁,Y) ≅ Ext²_G(X₃,Y)`), and
* the degree-one lattice dictionary `Work.SSGRoute.ext_one_iso_lattice_cohomology`
  (`Ext¹_G(X₁,Y) ≅ H¹(G, Hom_ℤ(X₁,Y))`)

identifies the *second* `Ext`-group of the finite module `X₃` with the *first* group cohomology of
the lattice `X₁`.  This is the arithmetic dictionary that the node `Work.SSGRoute.ext_sha2_bridge`
(`E1a`: `Ш²(k,E) → Ext²_{Gal(K/k)}(E^∨(1), Kˣ)`) uses with `X₃ = DualMod p (E ⊗ T)` and `Y = Kˣ`:
the two pieces are on disk, and this file only records their composite under a name, so that the
`E1a` assembly does not have to re-derive the chain.

Note that the *finite*-`X₃`/lattice-`X₁` shape is exactly the one needed: `X₃ = E^∨(1)` is finite
(the "finite `M`" form of the dictionary is false, see `ext2_iso_cohomology`), while the syzygy
`X₁` of a free presentation of `X₃` is a lattice, and it is *there* that the dictionary applies.
-/

namespace Work.SSGRoute

open CategoryTheory

noncomputable section

/-- **The landing dictionary of `E1a`.**  For a short exact sequence `0 → X₁ → X₂ → X₃ → 0` of
`Rep Coeff G` with projective middle term and a syzygy `X₁` that is a `ℤ`-lattice, and any
`Rep Coeff G` `Y`,
`Ext²_{ℤ[G]}(X₃,Y) ≅ H¹(G, Hom_ℤ(X₁,Y))`, the right-hand side being the explicit inhomogeneous
group cohomology of the internal `Hom` with the conjugation action. -/
theorem ext_two_iso_cohomology_of_presentation (G : Type) [Group G]
    (S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G)) (hS : S.ShortExact) [Projective S.X₂]
    (Y : Rep.{0} SSGRoute.PTExt.Coeff G)
    [Module.Free ℤ S.X₁.V] [Module.Finite ℤ S.X₁.V] :
    Nonempty (CategoryTheory.Abelian.Ext S.X₃ Y 2 ≃+
      Work.GroupCohomology.H1 G (S.X₁.V →ₗ[SSGRoute.PTExt.Coeff] Y.V)) := by
  obtain ⟨e₁⟩ := ext_shift_of_projective_presentation G S hS Y 1 le_rfl
  obtain ⟨e₂⟩ := ext_one_iso_lattice_cohomology G S.X₁ Y
  exact ⟨e₁.symm.trans e₂⟩

end

end Work.SSGRoute

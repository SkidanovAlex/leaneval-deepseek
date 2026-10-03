/-
# Homological coherence is invariant under group isomorphism

`Work.ORDunwoody.HomologicallyCoherent k G` says that every finitely generated subgroup of `G`
is of type `FP₂` over `k`.  This file proves that the property is invariant under a group
isomorphism `e : G ≃* H`.

The mathematical content is the isomorphism invariance of `IsFP2`:
a multiplicative equivalence `e : G ≃* H` induces the `k`-algebra isomorphism
`MonoidAlgebra.domCongr k k e : k[G] ≃ₐ[k] k[H]`, which carries the augmentation ideal of `k[G]`
onto the augmentation ideal of `k[H]`; transporting a finite presentation of the augmentation
ideal across a ring isomorphism (`finitePresentation_of_ringEquiv`) gives the result.

The two ingredients are proved in parallel files:

* `Submission.Work.ORAssembly.FP2.finitePresentation_of_ringEquiv` --
  `Module.FinitePresentation` is invariant under a ring equivalence;
* `Submission.Work.ORAssembly.FP2.map_augmentationIdeal_domCongr` --
  `domCongr` maps the augmentation ideal onto the augmentation ideal;
* `Submission.Work.ORAssembly.FP2.fg_comap_of_mulEquiv` -- bookkeeping for finitely generated
  subgroups under an isomorphism.
-/
import Mathlib
import Submission.Work.ORDunwoody.Bridge
import Submission.Work.ORAssembly.FP2.finitePresentation_of_ringEquiv
import Submission.Work.ORAssembly.FP2.map_augmentationIdeal_domCongr
import Submission.Work.ORAssembly.FP2.fg_comap_of_mulEquiv

namespace Work.ORAssembly.FP2

open Work.ORDunwoody

universe u v w

set_option linter.style.haveILetI false

/-- `IsFP2 k G` is invariant under a group isomorphism `G ≃* H`: a finite presentation of the
augmentation ideal of `k[G]` is transported to one for `k[H]` along the induced ring
isomorphism `k[G] ≃+* k[H]`. -/
theorem isFP2_of_mulEquiv {k : Type u} [CommRing k] {G : Type v} [Group G] {H : Type w} [Group H]
    (e : G ≃* H) : IsFP2 k G → IsFP2 k H := by
  intro h
  let φ : MonoidAlgebra k G ≃+* MonoidAlgebra k H := (MonoidAlgebra.domCongr k k e).toRingEquiv
  have hmap : (augmentationIdeal k G).map φ = augmentationIdeal k H :=
    map_augmentationIdeal_domCongr e
  -- Put the `k[H]`-module structure on the augmentation ideal of `k[G]` induced by `φ`.
  letI : Module (MonoidAlgebra k H) (augmentationIdeal k G) :=
    Module.compHom _ (φ.symm : MonoidAlgebra k H →+* MonoidAlgebra k G)
  haveI hfp : Module.FinitePresentation (MonoidAlgebra k H) (augmentationIdeal k G) :=
    finitePresentation_of_ringEquiv φ h
  -- The `k[H]`-linear isomorphism of ideals induced by `φ`.
  have hle : (augmentationIdeal k G) ≃ₗ[MonoidAlgebra k H] (augmentationIdeal k H) :=
    { toFun := fun x => ⟨φ x.1, by rw [← hmap]; exact Ideal.mem_map_of_mem φ x.2⟩
      invFun := fun y => ⟨φ.symm y.1, by
        have hy : ↑y ∈ Ideal.map φ (augmentationIdeal k G) := by rw [hmap]; exact y.2
        obtain ⟨x, hx, hxy⟩ := (Ideal.mem_map_iff_of_surjective φ φ.surjective).mp hy
        rw [← hxy]
        simpa using hx⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun m x => Subtype.ext (by
        change φ (φ.symm m * ↑x) = m * φ ↑x
        rw [map_mul, φ.apply_symm_apply])
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp) }
  exact Module.FinitePresentation.of_equiv hle

theorem homologicallyCoherent_of_mulEquiv {k : Type u} [CommRing k] {G H : Type u} [Group G] [Group H] (e : G ≃* H) : Work.ORDunwoody.HomologicallyCoherent k G → Work.ORDunwoody.HomologicallyCoherent k H := by
  intro h K hK
  obtain ⟨hfg, ⟨eK⟩⟩ := fg_comap_of_mulEquiv e K hK
  exact isFP2_of_mulEquiv eK (h (Subgroup.comap e.toMonoidHom K) hfg)

end Work.ORAssembly.FP2

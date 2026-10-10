import Mathlib.RepresentationTheory.Coinduced
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Iso
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ext_level_lift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The canonical free cover of a representation (E1a infrastructure)

Module extracted from `Submission/Work/SSGRoute/ext_sha2_bridge.lean` so that the lemmas *about*
the canonical cover (which live in `Submission/Work/SSGRoute/ExtChain/*` and therefore have to
import the node `E1a`) can be imported by the node itself without a build cycle.

`freeCover X : Rep.free Coeff G X.V ⟶ X` is the *choice-free* free cover of a representation `X`:
the free representation on the underlying set of `X` with the canonical surjection, together with
the canonical map `freeMap h` of covers induced by a morphism `h : X ⟶ Y` and the naturality square
`freeMap h ≫ freeCover Y = freeCover X ≫ h`.  Every earlier statement of the workspace obtains a
free cover by `Classical.choose` (`ext_level_lift.repFG_free_cover`), which is fatal for the
*naturality* clause of `ext_sha2_bridge`: two different coefficients `E₁`, `E₂` get two unrelated
covers, so no comparison map between the syzygies is available.  For a finite `X` (the case of
`E' = DualMod p (E ⊗ T)`) the free module `Rep.free Coeff G X.V` is finitely generated over `ℤ`, so
its kernel is a `ℤ`-lattice, exactly the syzygy `R` that the `Ext`-side dictionary needs. -/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

noncomputable section

section FreeCover

variable {G : Type} [Group G]

/-- **The canonical free cover.**  The free `ℤ[G]`-module on the underlying set of `X`, with the
canonical surjection `single x (single 1 1) ↦ x`.  Unlike `repFG_free_cover` this involves no
`Classical.choose`, which is what makes it functorial (see `freeMap`, `freeMap_freeCover`). -/
noncomputable def freeCover (X : Rep.{0} Coeff G) : Rep.free Coeff G X.V ⟶ X :=
  Rep.freeLift (k := Coeff) (G := G) X (id : X.V → X.V)

/-- The value of the canonical cover on a generator: `single x (single 1 1) ↦ x`. -/
theorem freeCover_apply_single [Fintype G] (X : Rep.{0} Coeff G) (x : X.V) :
    ConcreteCategory.hom (freeCover X) (Finsupp.single x (MonoidAlgebra.single 1 1)) = x :=
  rep_freeLift_apply_single (G := G) X X.V (id : X.V → X.V) x

/-- The canonical cover is surjective. -/
theorem freeCover_surjective [Fintype G] (X : Rep.{0} Coeff G) :
    Function.Surjective (ConcreteCategory.hom (freeCover X)) :=
  fun y => ⟨Finsupp.single y (MonoidAlgebra.single 1 1), freeCover_apply_single X y⟩

/-- The canonical cover is an epimorphism. -/
theorem freeCover_epi [Fintype G] (X : Rep.{0} Coeff G) : Epi (freeCover X) :=
  (Rep.epi_iff_surjective _).mpr (freeCover_surjective X)

/-- **The canonical map of covers** induced by `h : X ⟶ Y` on the free representations on the
underlying sets.  On generators it is `single x (single 1 1) ↦ single (h x) (single 1 1)`. -/
noncomputable def freeMap {X Y : Rep.{0} Coeff G} (h : X ⟶ Y) :
    Rep.free Coeff G X.V ⟶ Rep.free Coeff G Y.V :=
  Rep.freeLift (k := Coeff) (G := G) (Rep.free Coeff G Y.V)
    (fun x => Finsupp.single (h.hom x) (MonoidAlgebra.single 1 1))

/-- The value of `freeMap` on a generator. -/
theorem freeMap_generator [Fintype G] {X Y : Rep.{0} Coeff G} (h : X ⟶ Y) (x : X.V) :
    ConcreteCategory.hom (freeMap h) (Finsupp.single x (MonoidAlgebra.single 1 1)) =
      Finsupp.single (ConcreteCategory.hom h x) (MonoidAlgebra.single 1 1) :=
  rep_freeLift_apply_single (G := G) (Rep.free Coeff G Y.V) X.V
    (fun x => Finsupp.single (ConcreteCategory.hom h x) (MonoidAlgebra.single 1 1)) x

/-- **Functoriality of the canonical cover**: the covers of `X` and of `Y` are related by
`freeMap h`.  This is the square whose commutative analogue for the `Classical.choose`d covers of
`repFG_free_cover` does not exist, and which is the first ingredient of the naturality clause of
`ext_sha2_bridge`. -/
theorem freeMap_freeCover [Fintype G] {X Y : Rep.{0} Coeff G} (h : X ⟶ Y) :
    freeMap h ≫ freeCover Y = freeCover X ≫ h := by
  refine Rep.free_ext (k := Coeff) (G := G) (α := X.V) (A := Y) _ _ ?_
  intro x
  rw [Rep.comp_apply, Rep.comp_apply, freeMap_generator, freeCover_apply_single,
    freeCover_apply_single]

/-- `freeMap` of the identity is the identity. -/
theorem freeMap_id [Fintype G] (X : Rep.{0} Coeff G) :
    freeMap (𝟙 X) = 𝟙 (Rep.free Coeff G X.V) := by
  refine Rep.free_ext (k := Coeff) (G := G) (α := X.V) (A := Rep.free Coeff G X.V) _ _ ?_
  intro x
  show ConcreteCategory.hom (freeMap (𝟙 X)) (Finsupp.single x (MonoidAlgebra.single 1 1))
      = ConcreteCategory.hom (𝟙 (Rep.free Coeff G X.V))
          (Finsupp.single x (MonoidAlgebra.single 1 1))
  rw [freeMap_generator]
  rfl

/-- `freeMap` is compatible with composition. -/
theorem freeMap_comp [Fintype G] {X Y Z : Rep.{0} Coeff G} (h : X ⟶ Y) (k : Y ⟶ Z) :
    freeMap (h ≫ k) = freeMap h ≫ freeMap k := by
  refine Rep.free_ext (k := Coeff) (G := G) (α := X.V) (A := Rep.free Coeff G Z.V) _ _ ?_
  intro x
  show ConcreteCategory.hom (freeMap (h ≫ k)) (Finsupp.single x (MonoidAlgebra.single 1 1))
      = ConcreteCategory.hom (freeMap h ≫ freeMap k)
          (Finsupp.single x (MonoidAlgebra.single 1 1))
  rw [Rep.comp_apply]
  rw [freeMap_generator, freeMap_generator, freeMap_generator]
  rfl

end FreeCover

section FreeCoverSES

variable {G : Type} [Group G] [Fintype G]

/-- **The canonical presentation** `0 → R → F → X → 0` of a representation `X`, with `F` the free
representation on the underlying set of `X` and `R` its canonical syzygy.  Being built from
`freeCover` (and not from a `Classical.choose`d cover) this presentation is functorial in `X`, which
is what the naturality clause of `ext_sha2_bridge` needs. -/
@[reducible] noncomputable def freeCoverSES (X : Rep.{0} Coeff G) :
    ShortComplex (Rep.{0} Coeff G) :=
  ShortComplex.mk (Limits.kernel.ι (freeCover X)) (freeCover X)
    (Limits.kernel.condition (freeCover X))

/-- The canonical presentation is short exact. -/
theorem freeCoverSES_shortExact (X : Rep.{0} Coeff G) : (freeCoverSES X).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel (freeCover X)) inferInstance
    (freeCover_epi X)

/-- The syzygy `R` of the canonical presentation is finitely generated over `ℤ` as soon as `X` is
finite (the case `X = DualMod p (E ⊗ T)` of `E1a`): it is the kernel of a map from a finitely
generated free `ℤ`-module, and `ℤ` is Noetherian. -/
theorem freeCoverSES_finite (X : Rep.{0} Coeff G) [Finite X.V] :
    Module.Finite ℤ (Limits.kernel (freeCover X)).V :=
  repFG_kernel (G := G) X (freeCover X)

/-- **The canonical syzygy map** `R_X → R_Y` induced by `h : X ⟶ Y`: the restriction of
`freeMap h` to the kernels of the canonical covers.  It is the comparison of the two canonical
resolutions that the naturality clause of `ext_sha2_bridge` needs (there is no such map for the
`Classical.choose`d covers of `repFG_free_cover`). -/
noncomputable def freeMapKernel {X Y : Rep.{0} Coeff G} (h : X ⟶ Y) :
    Limits.kernel (freeCover X) ⟶ Limits.kernel (freeCover Y) :=
  Limits.kernel.lift (freeCover Y) (Limits.kernel.ι (freeCover X) ≫ freeMap h) (by
    rw [Category.assoc, freeMap_freeCover, ← Category.assoc, Limits.kernel.condition,
      Limits.zero_comp])

/-- The defining square of `freeMapKernel`. -/
theorem freeMapKernel_ι {X Y : Rep.{0} Coeff G} (h : X ⟶ Y) :
    freeMapKernel h ≫ Limits.kernel.ι (freeCover Y) =
      Limits.kernel.ι (freeCover X) ≫ freeMap h :=
  Limits.kernel.lift_ι _ _ _

/-- The lower square of the comparison of the two canonical resolutions: the syzygy map followed by
the canonical cover of `Y` is the canonical cover of `X` followed by `h`. -/
theorem freeMapKernel_freeCover {X Y : Rep.{0} Coeff G} (h : X ⟶ Y) :
    freeMapKernel h ≫ Limits.kernel.ι (freeCover Y) ≫ freeCover Y =
      Limits.kernel.ι (freeCover X) ≫ freeCover X ≫ h := by
  rw [← Category.assoc, freeMapKernel_ι, Category.assoc, freeMap_freeCover]

end FreeCoverSES

section ResFreeRep

variable {G : Type} [Group G] (D : Subgroup G) (ι : Type)

/-- **Restriction of a free representation is projective** (indeed free of rank `|ι| · [G : D]`,
but only projectivity is asserted here).  This is what makes the syzygy shift
(`Work.SSGRoute.ext_shift_of_projective_presentation`) applicable to the restriction to `D` of a
short exact sequence with free middle term — the first step of the "restriction of the canonical
chain" that the coherence clause of `ext_sha2_bridge` needs. -/
theorem res_free_rep_projective :
    CategoryTheory.Projective (Rep.res D.subtype (Rep.free Coeff G ι)) :=
  Functor.projective_obj_of_projective (Rep.resFunctor D.subtype)
    (Rep.free_projective (k := Coeff) (G := G) (α := ι))

end ResFreeRep
end

end Work.SSGRoute

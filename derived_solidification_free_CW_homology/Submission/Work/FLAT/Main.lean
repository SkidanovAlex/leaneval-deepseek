import Submission.Work.FLAT.Setup
import Submission.Work.FLAT.TensorProd
import Submission.Work.FLAT.SheafifyTensor
import Submission.Work.FLAT.PresheafFlat.tensorLeft_preservesFiniteLimits_of_flat

/-!
# AREA FLAT — free light condensed abelian groups are flat

This is the deliverable module of the area.  It contains

* `flat_prop : Submission.Blueprint.FlatProp`, i.e. for every light condensed set `T` the functor
  `ℤ[T] ⊗ -` on light condensed abelian groups preserves finite limits;
* the isomorphism `ℤ[A × B] ≅ ℤ[A] ⊗ ℤ[B]`, natural in the light condensed sets `A`, `B`
  (`freeTensorNatIso`, `freeTensorIso`, `freeProdIso` with naturality lemmas), stating that the
  free light condensed abelian group functor `ℤ[-]` is strong monoidal.  The light profinite form
  `ℤ[S × T] ≅ ℤ[S] ⊗ ℤ[T]` (`freeProfiniteProdIso`) together with `S.toCondensed ⊗ T.toCondensed
  ≅ (S ⨯ T).toCondensed` (`toCondensedTensorIso`, `FLAT/TensorProd.lean`) is the form in which the
  isomorphism is used to compute `P ⊗ ℤ[S]`.

## How `flat_prop` is proved

`ℤ[T] = L(F_T)` where `F_T = S ↦ ℤ[T(S)]` is the *sectionwise free presheaf* and `L` is
sheafification (`free_eq_sheafify_sectionwiseFree`, `FLAT/Setup.lean`).

1. `tensorLeft (L F) ≅ S ⋙ tensorLeft F ⋙ L` for every presheaf `F` (`tensorLeftSheafifyIso`,
   `FLAT/SheafifyTensor.lean`): for a light condensed abelian group `Z` one has
   `L F ⊗ Z ≅ L (F ⊗ S Z)`, using `Z ≅ L (S Z)` (the counit of the sheafification adjunction) and
   the tensorator of the monoidal functor `L`.
2. Each of the three factors preserves finite limits: `S = sheafToPresheaf` is a right adjoint,
   `L = presheafToSheaf` preserves finite limits, and `tensorLeft F` preserves finite limits when
   all the sections `F.obj T` are flat `ℤ`-modules
   (`tensorLeft_preservesFiniteLimits_of_flat`, `FLAT/PresheafFlat`), which is the case for the
   sectionwise free presheaf (`sectionwiseFree_flat`).

Since limits in a presheaf category are computed sectionwise, step 2 is exactly the statement that
a free `ℤ`-module is flat, and step 1 reduces the general statement to it; sheafification is exact
and monoidal, and the sheafified free presheaf is its own sectionwise free presheaf.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

namespace Work.FLAT

set_option linter.style.haveILetI false

noncomputable section

/-! ## `ℤ[A × B] ≅ ℤ[A] ⊗ ℤ[B]` -/

/-- `free ℤ` is a strong monoidal functor: the isomorphism of bifunctors
`ℤ[A] ⊗ ℤ[B] ≅ ℤ[A ⊗ B]`, natural in the light condensed sets `A` and `B`. -/
noncomputable def freeTensorNatIso :
    (LightCondensed.free (R := ℤ)).prod (LightCondensed.free (R := ℤ)) ⋙ tensor (LightCondAb) ≅
      tensor (LightCondSet.{0}) ⋙ LightCondensed.free (R := ℤ) :=
  Functor.Monoidal.μNatIso (LightCondensed.free (R := ℤ))

/-- `ℤ[A ⊗ B] ≅ ℤ[A] ⊗ ℤ[B]`. -/
noncomputable def freeTensorIso (A B : LightCondSet.{0}) :
    (LightCondensed.free (R := ℤ)).obj (A ⊗ B) ≅
      (LightCondensed.free (R := ℤ)).obj A ⊗ (LightCondensed.free (R := ℤ)).obj B :=
  (freeTensorNatIso).symm.app (A, B)

lemma freeTensorIso_hom (A B : LightCondSet.{0}) :
    (freeTensorIso A B).hom =
      (Functor.Monoidal.μIso (LightCondensed.free (R := ℤ)) A B).inv := rfl

/-- Naturality of `ℤ[A ⊗ B] ≅ ℤ[A] ⊗ ℤ[B]` in the first variable. -/
lemma freeTensorIso_natural_left {A A' : LightCondSet.{0}} (f : A ⟶ A') (B : LightCondSet.{0}) :
    (freeTensorIso A B).hom ≫ ((LightCondensed.free (R := ℤ)).map f ▷ _) =
      (LightCondensed.free (R := ℤ)).map (f ▷ B) ≫ (freeTensorIso A' B).hom := by
  have := (freeTensorNatIso).symm.hom.naturality ((f, 𝟙 B) : (A, B) ⟶ (A', B))
  simpa [freeTensorIso, tensorHom_id] using this.symm

/-- Naturality of `ℤ[A ⊗ B] ≅ ℤ[A] ⊗ ℤ[B]` in the second variable. -/
lemma freeTensorIso_natural_right (A : LightCondSet.{0}) {B B' : LightCondSet.{0}}
    (g : B ⟶ B') :
    (freeTensorIso A B).hom ≫ (_ ◁ (LightCondensed.free (R := ℤ)).map g) =
      (LightCondensed.free (R := ℤ)).map (A ◁ g) ≫ (freeTensorIso A B').hom := by
  have := (freeTensorNatIso).symm.hom.naturality ((𝟙 A, g) : (A, B) ⟶ (A, B'))
  simpa [freeTensorIso, id_tensorHom] using this.symm

/-- `ℤ[A × B] ≅ ℤ[A] ⊗ ℤ[B]` for the categorical product of light condensed sets. -/
noncomputable def freeProdIso (A B : LightCondSet.{0}) :
    (LightCondensed.free (R := ℤ)).obj (A ⨯ B) ≅
      (LightCondensed.free (R := ℤ)).obj A ⊗ (LightCondensed.free (R := ℤ)).obj B :=
  (LightCondensed.free (R := ℤ)).mapIso (tensorIsoProd A B).symm ≪≫ freeTensorIso A B

/-- **`ℤ[S × T] ≅ ℤ[S] ⊗ ℤ[T]`** for light profinite sets `S`, `T`: this is the form of the
strong monoidality of `ℤ[-]` used to identify `P ⊗ ℤ[S]` with `ℤ[(ℕ∪∞) × S] / ℤ[{∞} × S]`. -/
noncomputable def freeProfiniteProdIso (S T : LightProfinite.{0}) :
    (LightCondensed.free (R := ℤ)).obj ((S ⨯ T).toCondensed) ≅
      (LightCondensed.free (R := ℤ)).obj S.toCondensed ⊗
        (LightCondensed.free (R := ℤ)).obj T.toCondensed :=
  (LightCondensed.free (R := ℤ)).mapIso (toCondensedTensorIso S T).symm ≪≫
    freeTensorIso S.toCondensed T.toCondensed

/-! ## Flatness -/

/-- The sectionwise tensor product with the sectionwise free presheaf on `T` preserves finite
limits. -/
theorem tensorLeft_sectionwiseFree_preservesFiniteLimits (T : LightCondSet.{0}) :
    PreservesFiniteLimits (tensorLeft (sectionwiseFree T)) :=
  Work.FLAT.PresheafFlat.tensorLeft_preservesFiniteLimits_of_flat (sectionwiseFree T)
    (sectionwiseFree_flat T)

/-- **`ℤ[T]` is flat**: tensoring with the free light condensed abelian group on a light condensed
set `T` preserves finite limits. -/
theorem tensorLeft_free_preservesFiniteLimits (T : LightCondSet.{0}) :
    PreservesFiniteLimits (tensorLeft ((LightCondensed.free (R := ℤ)).obj T)) := by
  rw [free_eq_sheafify_sectionwiseFree T]
  haveI := tensorLeft_sectionwiseFree_preservesFiniteLimits T
  exact preservesFiniteLimits_tensorLeft_sheafify (sectionwiseFree T)

/-- In particular `ℤ[T] ⊗ -` preserves monomorphisms, i.e. `Tor₁(ℤ[T], -) = 0`. -/
theorem tensorLeft_free_preservesMonomorphisms (T : LightCondSet.{0}) :
    Functor.PreservesMonomorphisms (tensorLeft ((LightCondensed.free (R := ℤ)).obj T)) := by
  haveI := tensorLeft_free_preservesFiniteLimits T
  infer_instance

/-- **AREA FLAT.** Free light condensed abelian groups are flat. -/
theorem flat_prop : Submission.Blueprint.FlatProp :=
  fun T => tensorLeft_free_preservesFiniteLimits T

/-- Flatness of `ℤ[S]` for a light profinite set `S`, in the form used for the atoms. -/
theorem tensorLeft_free_lightProfinite_preservesFiniteLimits (S : LightProfinite.{0}) :
    PreservesFiniteLimits (tensorLeft ((LightCondensed.free (R := ℤ)).obj S.toCondensed)) :=
  tensorLeft_free_preservesFiniteLimits S.toCondensed

/-- `- ⊗ ℤ[T]` also preserves finite limits: `ℤ[T]` is flat on either side. -/
theorem tensorRight_free_preservesFiniteLimits (T : LightCondSet.{0}) :
    PreservesFiniteLimits (tensorRight ((LightCondensed.free (R := ℤ)).obj T)) := by
  haveI := tensorLeft_free_preservesFiniteLimits T
  exact preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)

end

end Work.FLAT

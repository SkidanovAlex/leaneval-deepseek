import Submission.Blueprint.Interfaces

/-!
# AREA ATOM — `ℤ[S]` is solid-cofibrant (basic interface)

This file fixes the conventions and definitions used by the rest of the `ATOM` area.

Notation (all inherited from `ChallengeDeps` and `Submission.Blueprint.Interfaces`):

* `LightCondAb` — light condensed abelian groups; `P = ℤ[ℕ∪∞]/ℤ[∞]` (`LightCondensed.P`);
* `oneMinusShift : P ⟶ P`; `isSolid : ObjectProperty LightCondAb`, `Solid = isSolid.FullSubcategory`;
* `ιC = LightCondensed.Solid.ιC` — the degreewise inclusion of complexes of solid objects;
* `atom S n = (HomologicalComplex.single LightCondAb (up ℤ) n).obj (ℤ[S])`.

The main theorem of the area is `Work.ATOM.atom_prop : Submission.Blueprint.AtomProp`, which is
assembled in `Submission/Work/ATOM/Main.lean`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

namespace Work.ATOM

/-- The cochain complex concentrated in degree `n`, as a functor in the object. -/
abbrev singleC (n : ℤ) : LightCondAb ⥤ CochainComplex LightCondAb ℤ :=
  HomologicalComplex.single LightCondAb (ComplexShape.up ℤ) n

/-- The quotient functor from complexes to the homotopy category. -/
abbrev hq : CochainComplex LightCondAb ℤ ⥤ HomotopyCategory LightCondAb (ComplexShape.up ℤ) :=
  HomotopyCategory.quotient _ _

/-- `Hom_{K(LCA)}(singleC n A, K)`, as a contravariant functor in `A`. -/
noncomputable def homK (n : ℤ) (K : CochainComplex LightCondAb ℤ) : LightCondAbᵒᵖ ⥤ Type _ :=
  (singleC n).op ⋙ hq.op ⋙ CategoryTheory.yoneda.obj (hq.obj K)

/-- `Hom_{D(LCA)}(Q (singleC n A), Q K)`, as a contravariant functor in `A`. -/
noncomputable def homD (n : ℤ) (K : CochainComplex LightCondAb ℤ) : LightCondAbᵒᵖ ⥤ Type _ :=
  (singleC n).op ⋙ DerivedCategory.Q.op ⋙
    CategoryTheory.yoneda.obj (DerivedCategory.Q.obj K)

/-- Notation for `ℤ[S]`, the free light condensed abelian group on a light profinite set. -/
abbrev zfree (S : LightProfinite.{0}) : LightCondAb := (free ℤ).obj S.toCondensed

/-- The "single complex" form of an atom: `Submission.Blueprint.atom S n`. -/
abbrev atomC (S : LightProfinite.{0}) (n : ℤ) : CochainComplex LightCondAb ℤ :=
  (singleC n).obj (zfree S)

/-! ### Notation-free aliases

Statements delegated to colleagues are written without the `⊗` notation (which is
`MonoidalCategory`-scoped), so these aliases are used instead. -/

/-- Alias for the tensor product in `LightCondAb` (definitionally `A ⊗ B`). -/
abbrev tmul (A B : LightCondAb) : LightCondAb := A ⊗ B

/-- `(1 - S) ⊗ id_A : P ⊗ A ⟶ P ⊗ A`. -/
abbrev preShift (A : LightCondAb) : tmul P A ⟶ tmul P A :=
  MonoidalCategory.whiskerRight oneMinusShift A

/-- `id_P ⊗ g : P ⊗ P ⟶ P ⊗ W`. -/
abbrev idTensorHom {W : LightCondAb} (g : P ⟶ W) : tmul P P ⟶ tmul P W :=
  MonoidalCategory.whiskerLeft P g

/-- The composite `(1 - S) ⊗ id_P` on `P ⊗ P`, notation-free. -/
abbrev preShiftP : tmul P P ⟶ tmul P P := preShift P

/-! ### Tools for maps out of free light condensed abelian groups

These are the two comparison isomorphisms that make it possible to write down morphisms out of
`ℤ[S]` and out of tensor products of such: `homFreeEquiv` describes a morphism out of `ℤ[S]` as a
section of the target over `S`, and `zfreeTensorIso` is `ℤ[S] ⊗ ℤ[T] ≅ ℤ[S × T]`. -/

/-- `Hom(ℤ[S], A) ≅ A(S)`: a morphism out of the free light condensed abelian group on `S` is
a section of `A` over `S` (free-forget adjunction followed by Yoneda). -/
noncomputable def homFreeEquiv (S : LightProfinite.{0}) (A : LightCondAb) :
    (zfree S ⟶ A) ≃ ↥(A.obj.obj (Opposite.op S)) :=
  ((freeForgetAdjunction ℤ).homEquiv S.toCondensed A).trans
    ((coherentTopology LightProfinite).yonedaEquiv)

/-- `ℤ[f]` for a map of light profinite sets: the induced map of free light condensed abelian
groups.  (Following `NOTES_LEAD_solid_gaps1.md` §3.2, this is called `zmap`.) -/
abbrev zmap {S T : LightProfinite.{0}} (f : S ⟶ T) : zfree S ⟶ zfree T :=
  (lightProfiniteToLightCondSet ⋙ free ℤ).map f

/-- The point, as a light profinite set. -/
abbrev pt : LightProfinite.{0} := LightProfinite.of PUnit.{1}

/-- The map `* ⟶ S` picking out a point of `S`. -/
def ptAt {S : LightProfinite.{0}} (s : ↥S) : pt ⟶ S :=
  ConcreteCategory.ofHom ⟨fun _ => s, continuous_const⟩

/-- The point map `* ⟶ S` is the constant map at `s`. -/
@[simp] lemma ptAt_apply {S : LightProfinite.{0}} (s : ↥S) (x : ↥pt) : ptAt s x = s := rfl

/-- The point map `* ⟶ S`, in the form `ConcreteCategory.hom`. -/
@[simp] lemma hom_ptAt_apply {S : LightProfinite.{0}} (s : ↥S) (x : ↥pt) :
    (ConcreteCategory.hom (ptAt s)) x = s := rfl

/-- The (unique) map `S ⟶ *`. -/
def toPt (S : LightProfinite.{0}) : S ⟶ pt :=
  ConcreteCategory.ofHom ⟨fun _ => PUnit.unit, continuous_const⟩

/-- The *reduced* free object `ℤ̃[S] = ℤ[S]/ℤ[s₀]` of `NOTES_LEAD_solid_gaps1.md` §3.2. -/
abbrev zred (S : LightProfinite.{0}) (s₀ : ↥S) : LightCondAb := cokernel (zmap (ptAt s₀))

/-- The quotient map `ℤ[S] ⟶ ℤ̃[S]`. -/
abbrev qred (S : LightProfinite.{0}) (s₀ : ↥S) : zfree S ⟶ zred S s₀ := cokernel.π _

/-- The augmentation `ℤ[S] ⟶ ℤ[*]`. -/
abbrev aug (S : LightProfinite.{0}) : zfree S ⟶ zfree pt := zmap (toPt S)

/-- `ℤ[S] ⊗ ℤ[T] ≅ ℤ[S × T]`: the free functor is monoidal. -/
noncomputable def zfreeTensorIso (S T : LightProfinite.{0}) :
    tmul (zfree S) (zfree T) ≅ zfree (S ⊗ T) :=
  Functor.Monoidal.μIso (free ℤ) S.toCondensed T.toCondensed ≪≫
    (free ℤ).mapIso (Functor.Monoidal.μIso lightProfiniteToLightCondSet S T)

end Work.ATOM

import Mathlib
import Submission.Work.ATOM.Defs
import Submission.Work.ATOM.Assembly
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.solidCofibrantH_of_iso

namespace Work.ATOM

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

set_option linter.style.haveILetI false

/-- The localization functor `K(LightCondAb) ⥤ D(LightCondAb)` (the `C`-instance is fixed to
`LightCondAb` so that it can be used without further elaboration arguments). -/
abbrev qhD : HomotopyCategory LightCondAb (ComplexShape.up ℤ) ⥤ DerivedCategory LightCondAb :=
  DerivedCategory.Qh

/-!
# AREA ATOM — solid-cofibrancy is closed under binary biproducts

`Submission.Blueprint.SolidCofibrant K` says that the localization `DerivedCategory.Qh` induces a
bijection
`Hom_K(hq K, hq (ιC N)) ≃ Hom_D(Qh (hq K), Qh (hq (ιC N)))`
for every complex `N` of solid objects; i.e. that `K` is a cofibrant object of the "solid" model
structure on `K(LightCondAb)`.  Cofibrant objects are closed under coproducts, in particular under
binary biproducts, which is what `BiprodAux.solidCofibrant_biprod` proves:

* `hq` and `Qh` are additive, hence preserve binary biproducts
  (`BiprodAux.preservesBinaryBiproducts_of_additive`);
* `Hom(X ⊞ Y, Z) ≃ Hom(X, Z) × Hom(Y, Z)` (`BiprodAux.bijective_biprod_map`);
* under these two identifications (on the `K`-side and on the `D`-side) the map `Qh` becomes the
  product of the maps for the two summands, so it is bijective iff each of them is.

The final statement `solidCofibrant_singleC_biprod` combines this with the fact that `singleC n`
is additive, hence sends the biproduct `A ⊞ B` of light condensed abelian groups to the biproduct
of the single complexes, and with the invariance of `SolidCofibrant` under isomorphism
(`Work.RESOL.solidCofibrantH_of_iso`).
-/

namespace BiprodAux

/-- An additive functor preserves binary biproducts.  Mathlib registers
`preservesFiniteBiproductsOfAdditive` as an instance, but not the equivalent statement
`PreservesBinaryBiproducts`; this bridge supplies it (as a theorem, so that the instance is only
in scope where it is needed). -/
theorem preservesBinaryBiproducts_of_additive {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive] : PreservesBinaryBiproducts F :=
  preservesBinaryBiproducts_of_preservesBiproducts F

/-- `Hom(X ⊞ Y, Z) ≃ Hom(X, Z) × Hom(Y, Z)`: a morphism out of a binary biproduct is a pair of
morphisms out of the two summands. -/
theorem bijective_biprod_map {C : Type*} [Category C] [Preadditive C] (X Y Z : C)
    [HasBinaryBiproduct X Y] :
    Function.Bijective (fun ψ : X ⊞ Y ⟶ Z => (biprod.inl ≫ ψ, biprod.inr ≫ ψ)) := by
  refine ⟨fun f g h => biprod.hom_ext' f g (congrArg Prod.fst h) (congrArg Prod.snd h),
    fun p => ⟨biprod.desc p.1 p.2, ?_⟩⟩
  refine Prod.ext ?_ ?_
  · show biprod.inl ≫ biprod.desc p.1 p.2 = p.1
    exact biprod.inl_desc p.1 p.2
  · show biprod.inr ≫ biprod.desc p.1 p.2 = p.2
    exact biprod.inr_desc p.1 p.2

/-- Solid-cofibrancy is closed under binary biproducts. -/
theorem solidCofibrant_biprod (K L : CochainComplex LightCondAb ℤ)
    (hK : Submission.Blueprint.SolidCofibrant K)
    (hL : Submission.Blueprint.SolidCofibrant L) :
    Submission.Blueprint.SolidCofibrant (K ⊞ L) := by
  haveI := preservesBinaryBiproducts_of_additive hq
  haveI := preservesBinaryBiproducts_of_additive qhD
  intro N
  let Z := hq.obj (Submission.Blueprint.ιC.obj N)
  let Z' := qhD.obj Z
  -- the biproduct identifications: `hq` preserves the biproduct, `Qh` preserves it, and `eQ` is
  -- the composite, which is functorial in the first variable (this is what makes the square below
  -- commute).
  let eK := Functor.mapBiprod hq K L
  let eD := Functor.mapBiprod qhD (hq.obj K) (hq.obj L)
  let eQ := qhD.mapIso eK ≪≫ eD
  -- the two product decompositions of the Hom-sets, as plain functions
  let Lf : (hq.obj (K ⊞ L) ⟶ Z) → (hq.obj K ⟶ Z) × (hq.obj L ⟶ Z) :=
    fun φ => (biprod.inl ≫ eK.inv ≫ φ, biprod.inr ≫ eK.inv ≫ φ)
  let Rf : (qhD.obj (hq.obj (K ⊞ L)) ⟶ Z') →
      (qhD.obj (hq.obj K) ⟶ Z') × (qhD.obj (hq.obj L) ⟶ Z') :=
    fun ψ => (biprod.inl ≫ eQ.inv ≫ ψ, biprod.inr ≫ eQ.inv ≫ ψ)
  have hbL : Function.Bijective Lf := by
    have h₁ : Function.Bijective (fun φ : hq.obj (K ⊞ L) ⟶ Z => eK.inv ≫ φ) := by
      constructor
      · intro a b h
        have h' : eK.inv ≫ a = eK.inv ≫ b := h
        exact (cancel_epi eK.inv).mp h'
      · intro f
        exact ⟨eK.hom ≫ f, Iso.inv_hom_id_assoc eK f⟩
    exact (bijective_biprod_map (hq.obj K) (hq.obj L) Z).comp h₁
  have hbR : Function.Bijective Rf := by
    have h₁ : Function.Bijective
        (fun ψ : qhD.obj (hq.obj (K ⊞ L)) ⟶ Z' => eQ.inv ≫ ψ) := by
      constructor
      · intro a b h
        have h' : eQ.inv ≫ a = eQ.inv ≫ b := h
        exact (cancel_epi eQ.inv).mp h'
      · intro f
        exact ⟨eQ.hom ≫ f, Iso.inv_hom_id_assoc eQ f⟩
    exact (bijective_biprod_map (qhD.obj (hq.obj K)) (qhD.obj (hq.obj L)) Z').comp h₁
  have hEinv : eQ.inv = eD.inv ≫ qhD.map eK.inv := by
    show (qhD.mapIso eK ≪≫ eD).inv = eD.inv ≫ qhD.map eK.inv
    rw [Iso.trans_inv, Functor.mapIso_inv]
  have hDinv : eD.inv = biprod.desc (qhD.map (biprod.inl : hq.obj K ⟶ hq.obj K ⊞ hq.obj L))
      (qhD.map (biprod.inr : hq.obj L ⟶ hq.obj K ⊞ hq.obj L)) := by
    show (Functor.mapBiprod qhD (hq.obj K) (hq.obj L)).inv = _
    rw [Functor.mapBiprod_inv]
  -- the naturality square, componentwise
  have hcomp : ∀ φ : hq.obj (K ⊞ L) ⟶ Z,
      (biprod.inl ≫ eQ.inv ≫ qhD.map φ, biprod.inr ≫ eQ.inv ≫ qhD.map φ) =
        (qhD.map (biprod.inl ≫ eK.inv ≫ φ), qhD.map (biprod.inr ≫ eK.inv ≫ φ)) := by
    intro φ
    refine Prod.ext ?_ ?_
    · show biprod.inl ≫ eQ.inv ≫ qhD.map φ = qhD.map (biprod.inl ≫ eK.inv ≫ φ)
      rw [← Category.assoc, hEinv, ← Category.assoc, hDinv, biprod.inl_desc, Category.assoc,
        ← Functor.map_comp, ← Functor.map_comp]
    · show biprod.inr ≫ eQ.inv ≫ qhD.map φ = qhD.map (biprod.inr ≫ eK.inv ≫ φ)
      rw [← Category.assoc, hEinv, ← Category.assoc, hDinv, biprod.inr_desc, Category.assoc,
        ← Functor.map_comp, ← Functor.map_comp]
  have hLR : Rf ∘ (fun φ : hq.obj (K ⊞ L) ⟶ Z => qhD.map φ) =
      (fun p : (hq.obj K ⟶ Z) × (hq.obj L ⟶ Z) => (qhD.map p.1, qhD.map p.2)) ∘ Lf := by
    funext φ
    exact hcomp φ
  have hprod : Function.Bijective
      (fun p : (hq.obj K ⟶ Z) × (hq.obj L ⟶ Z) => (qhD.map p.1, qhD.map p.2)) :=
    (Equiv.prodCongr (Equiv.ofBijective _ (hK N)) (Equiv.ofBijective _ (hL N))).bijective
  have hsquare : Function.Bijective (Rf ∘ (fun φ : hq.obj (K ⊞ L) ⟶ Z => qhD.map φ)) := by
    rw [hLR]
    exact hprod.comp hbL
  exact (Function.Bijective.of_comp_iff' hbR (fun φ : hq.obj (K ⊞ L) ⟶ Z => qhD.map φ)).mp
    hsquare

end BiprodAux

/-- Solid-cofibrancy of atoms is closed under binary biproducts: `singleC n` preserves
biproducts and `Hom(−, ιC N)` turns a biproduct in the source into a product, compatibly with
`Qh`.  Used in `NOTES_LEAD_solid_gaps1.md` §3.5 to transfer `Z̃[S]` back to `ℤ[S]`. -/
theorem solidCofibrant_singleC_biprod {A B : LightCondAb} (n : ℤ)
    (hA : Submission.Blueprint.SolidCofibrant ((Work.ATOM.singleC n).obj A))
    (hB : Submission.Blueprint.SolidCofibrant ((Work.ATOM.singleC n).obj B)) :
    Submission.Blueprint.SolidCofibrant ((Work.ATOM.singleC n).obj (A ⊞ B)) := by
  -- `singleC n` is additive, hence sends the biproduct `A ⊞ B` to the biproduct of the pieces
  haveI : PreservesBinaryBiproducts (Work.ATOM.singleC n) :=
    BiprodAux.preservesBinaryBiproducts_of_additive (Work.ATOM.singleC n)
  obtain ⟨e⟩ : Nonempty ((Work.ATOM.singleC n).obj (A ⊞ B) ≅
      (Work.ATOM.singleC n).obj A ⊞ (Work.ATOM.singleC n).obj B) :=
    ⟨Functor.mapBiprod _ A B⟩
  -- closure under the biproduct, then invariance under the isomorphism `e`
  exact (Work.RESOL.solidCofibrant_iff _).mpr
    (Work.RESOL.solidCofibrantH_of_iso (Work.ATOM.hq.mapIso e).symm
      ((Work.RESOL.solidCofibrant_iff _).mp (BiprodAux.solidCofibrant_biprod _ _ hA hB)))

end

end Work.ATOM

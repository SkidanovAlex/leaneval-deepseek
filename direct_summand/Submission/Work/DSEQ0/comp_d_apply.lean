import Mathlib
import Submission.Work.DSEQ0.CechImageModel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

universe u

namespace Work.DSEQ0

section CechComponent

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {ι : Type u}

/-- **Component formula for the Čech differential** (morphism form).  This is the same
statement as `Work.DSF1.Cech.cechComplexFunctor_d_π` (and the same proof), re-proved here in
the universe configuration `A : Type u`, `X : Scheme.{u}`, `ι : Type u` that we need: the
original statement forces the universe of the index type `ι` to be that of the *objects* of
`ModuleCat A`. -/
theorem cech_d_pi (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ ModuleCat.{u} A) (n : ℕ)
    (a : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n + 1⦌)).I) :
    (((cechComplexFunctor U).obj P).d n (n + 1)) ≫
        (Pi.π (fun y => P.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n + 1⦌)).obj y))) a)
      = ∑ c : Fin (n + 2), (-1 : ℤ) ^ (c : ℕ) •
          ((Pi.π (fun y => P.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj y)))
              (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).f a)) ≫
            P.map (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).φ a).op) := by
  simp only [CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor_obj_d]
  rw [CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rw [Preadditive.sum_comp, Finset.sum_congr rfl (fun i _ => Preadditive.zsmul_comp _ _ _)]
  simp only [CosimplicialObject.δ, FormalCoproduct.cosimplicialObjectFunctor_obj_map,
    Pi.lift_comp_π]

/-- **Component formula for the Čech differential** (element form). -/
theorem cech_d_apply (U : ι → X.Opens) (P : X.Opensᵒᵖ ⥤ ModuleCat.{u} A) (n : ℕ)
    (y : ((cechComplexFunctor U).obj P).X n)
    (a : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n + 1⦌)).I) :
    (Pi.π (fun y => P.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n + 1⦌)).obj y))) a).hom
        ((((cechComplexFunctor U).obj P).d n (n + 1)).hom y)
      = ∑ c : Fin (n + 2), (-1 : ℤ) ^ (c : ℕ) •
          (P.map (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).φ a).op).hom
            ((Pi.π (fun y => P.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj y)))
              (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ c).op).f a)).hom y) := by
  have h := cech_d_pi U P n a
  have h2 := congrArg (fun g => (ModuleCat.Hom.hom g) y) h
  simp only [ModuleCat.hom_comp, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply] at h2
  exact h2

end CechComponent

/-- **The element-level form of `termIso_conj`**: the Čech presheaf map at the deletion
`y ∘ Fin.succAbove k`, conjugated by the identifications `termIso`, is the restriction map
`res`. -/
theorem termIso_conj_apply {A : Type u} [CommRing A] {X : Scheme.{u}}
    {f : X ⟶ Spec (.of A)} {ι : Type u} {U : ι → X.Opens}
    (n : ℕ) (y : Fin (n + 2) → ι) (k : Fin (n + 2))
    (x : (DSMap.cechPresheaf A X f).obj
      (op (∏ᶜ (fun a => U ((y ∘ Fin.succAbove k) a))))) :
    (termIso A X f U (n + 1) y).hom.hom
        (((DSMap.cechPresheaf A X f).map
          (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ k).op).φ y).op).hom x)
      = (res A X f U (Set.range (y ∘ Fin.succAbove k)) (Set.range y)
          (range_succAbove_subset y k)).hom
        ((termIso A X f U n (y ∘ Fin.succAbove k)).hom.hom x) := by
  have hz : (termIso A X f U n (y ∘ Fin.succAbove k)).inv.hom
        ((termIso A X f U n (y ∘ Fin.succAbove k)).hom.hom x) = x := by
    have h1 : (termIso A X f U n (y ∘ Fin.succAbove k)).inv.hom ∘ₗ
        (termIso A X f U n (y ∘ Fin.succAbove k)).hom.hom = LinearMap.id := by
      rw [← ModuleCat.hom_comp, Iso.hom_inv_id]
      rfl
    exact LinearMap.congr_fun h1 x
  have h := congrArg (fun g => (ModuleCat.Hom.hom g)
      ((termIso A X f U n (y ∘ Fin.succAbove k)).hom.hom x))
      (termIso_conj A X f U n y k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [hz] at h
  exact h

section MorphismForm

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {ι : Type u} {f : X ⟶ Spec (.of A)}
  {U : ι → X.Opens}

/-- **The component formula for the Čech differential** (morphism form): the `y`-th component
of the differential of `DSMap.cech A X f U`, expressed by the identification `comp`, is the
alternating sum of the components of `c` at the deletions, transported by `res`. -/
theorem comp_d_eq (n : ℕ) (y : Fin (n + 2) → ι) :
    (DSMap.cech A X f U).d n (n + 1) ≫ comp A X f U (n + 1) y
      = ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
          (comp A X f U n (y ∘ Fin.succAbove k) ≫
            res A X f U (Set.range (y ∘ Fin.succAbove k)) (Set.range y)
              (range_succAbove_subset y k)) := by
  have hkey (k : Fin (n + 2)) :
      ((Pi.π (fun x : Fin (n + 1) → ι => (DSMap.cechPresheaf A X f).obj (op (∏ᶜ fun a => U (x a))))
          (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ k).op).f y))
        ≫ (DSMap.cechPresheaf A X f).map
            (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ k).op).φ y).op)
        ≫ (termIso A X f U (n + 1) y).hom
      = comp A X f U n (y ∘ Fin.succAbove k) ≫
        res A X f U (Set.range (y ∘ Fin.succAbove k)) (Set.range y)
          (range_succAbove_subset y k) := by
    rw [show comp A X f U n (y ∘ Fin.succAbove k) =
        (Pi.π (fun x : Fin (n + 1) → ι => (DSMap.cechPresheaf A X f).obj (op (∏ᶜ fun a => U (x a))))
            (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ k).op).f y))
          ≫ (termIso A X f U n (y ∘ Fin.succAbove k)).hom from rfl]
    rw [← termIso_conj A X f U n y k]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hpi : ((DSMap.cech A X f U).d n (n+1) ≫
        Pi.π (fun x : Fin (n+2) → ι => (DSMap.cechPresheaf A X f).obj (op (∏ᶜ fun a => U (x a)))) y)
      = ∑ k : Fin (n+2), (-1:ℤ)^(k:ℕ) •
          (Pi.π (fun x : Fin (n+1) → ι => (DSMap.cechPresheaf A X f).obj (op (∏ᶜ fun a => U (x a))))
              (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ k).op).f y)
           ≫ (DSMap.cechPresheaf A X f).map
              (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ k).op).φ y).op) :=
    cech_d_pi (U := U) (P := DSMap.cechPresheaf A X f) n y
  rw [show comp A X f U (n+1) y =
      (Pi.π (fun x : Fin (n+2) → ι => (DSMap.cechPresheaf A X f).obj (op (∏ᶜ fun a => U (x a)))) y)
        ≫ (termIso A X f U (n+1) y).hom from rfl, ← Category.assoc, hpi,
      Preadditive.sum_comp, Finset.sum_congr rfl (fun i _ => Preadditive.zsmul_comp _ _ _)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hkey k]

end MorphismForm

/-- **The component formula for the Čech differential.**  For a cochain `c` of the Čech
complex `DSMap.cech A X f U` in degree `n` and a tuple `y : Fin (n+2) → ι`, the `y`-th
component of the differential `d c`, transported to the coefficient module
`coeff A X f U (Set.range y) = Γ(X, ⨅ i ∈ Set.range y, U i)` by the identification `comp`, is
the alternating sum of the components of `c` at the deletions `y ∘ Fin.succAbove k`, transported
by the restriction maps `res`.

Concretely this is the element-level form of `Work.DSF1.Cech.cechComplexFunctor_d_π`
(Mathlib's Čech complex is the alternating sum of the deletion cofaces), combined with
`Work.DSEQ0.termIso_conj`, which identifies the conjugated component maps with the maps `res`
between the coefficient modules of the *image sets*.

A possible route (all ingredients are available): apply
`Work.DSF1.Cech.cechComplexFunctor_d_π` (in `Submission/Work/DSF1/Cech/CechComponents.lean`),
then rewrite `(Pi.π _ z).hom c` for `z = y ∘ Fin.succAbove k` using `Work.DSEQ0.comp`, and
finally use `Work.DSEQ0.termIso_conj`.  Note that the source file uses
`set_option backward.isDefEq.respectTransparency false`, which helps with the conversions
between `Fin (n+1) → ι` and the Čech-nerve index types `((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).I`
(these are definitionally equal; see e.g. `Work.DSF1.Cech.cechComplexFunctor_d_π` for the
same conversions). -/
theorem comp_d_apply {A : Type u} [CommRing A] {X : AlgebraicGeometry.Scheme.{u}}
    {f : X ⟶ AlgebraicGeometry.Spec (.of A)} {ι : Type u} (U : ι → X.Opens)
    (n : ℕ) (c : (DSMap.cech A X f U).X n) (y : Fin (n + 2) → ι) :
    (Work.DSEQ0.comp A X f U (n + 1) y).hom (((DSMap.cech A X f U).d n (n + 1)).hom c) =
      ∑ k : Fin (n + 2), (-1 : ℤ) ^ (k : ℕ) •
        (Work.DSEQ0.res A X f U (Set.range (y ∘ Fin.succAbove k)) (Set.range y)
          (Work.DSEQ0.range_succAbove_subset y k)).hom
          ((Work.DSEQ0.comp A X f U n (y ∘ Fin.succAbove k)).hom c) := by
  have h1 : (Work.DSEQ0.comp A X f U (n + 1) y).hom (((DSMap.cech A X f U).d n (n + 1)).hom c)
      = ((DSMap.cech A X f U).d n (n + 1) ≫ Work.DSEQ0.comp A X f U (n + 1) y).hom c := rfl
  rw [h1, comp_d_eq, ModuleCat.hom_sum]
  simp only [ModuleCat.hom_zsmul, ModuleCat.hom_comp, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply]

end Work.DSEQ0

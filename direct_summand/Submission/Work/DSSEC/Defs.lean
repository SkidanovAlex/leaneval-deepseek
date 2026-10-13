import Mathlib
import Submission.Work.DSSEC.Basic
import Submission.Work.DSF1.Cech.CechComponents

/-! Shared definitions for the combinatorial half (`Work.DSSEC.exists_cechMap_of_secData`). -/

attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped ZeroObject Simplicial BigOperators

set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

universe u v v' w u'

namespace Work.DSSEC

section Setup

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} {N : ℕ}

/-- The `y`-th index set of the chart Čech complex (the underlying finset of the `y`-th
index object of the Čech nerve of the family `i ↦ {i}` of `Finset (Idx N)`). -/
noncomputable abbrev SIdx (N : ℕ) (n : ℕ) (y : Fin (n + 1) → Idx.{(u)} N) : Finset (Idx.{(u)} N) :=
  (∏ᶜ (DSMap.Mix2.chartIdx (Idx.{(u)} N) ∘ y)).unop

/-- The `y`-th open of the chart cover `i ↦ U_i`. -/
noncomputable abbrev ROpen (i : X ⟶ DSMap.PSpace A N) (n : ℕ) (y : Fin (n + 1) → Idx.{(u)} N) :
    X.Opens :=
  ∏ᶜ (DSMap.Mix2.chartCover i ∘ y)

/-- The intersection of the charts over the index set `SIdx`. -/
noncomputable abbrev IOpen (i : X ⟶ DSMap.PSpace A N) (n : ℕ) (y : Fin (n + 1) → Idx.{(u)} N) :
    X.Opens :=
  ⨅ m ∈ SIdx N n y, DSMap.Mix2.chartCover i m

lemma SIdx_mem (N : ℕ) (n : ℕ) (y : Fin (n + 1) → Idx.{(u)} N) (a : Fin (n + 1)) :
    y a ∈ SIdx N n y := by
  have h : ({y a} : Finset (Idx.{(u)} N)) ⊆ (∏ᶜ (DSMap.Mix2.chartIdx (Idx.{(u)} N) ∘ y)).unop :=
    leOfHom (Pi.π (fun a => DSMap.Mix2.chartIdx (Idx.{(u)} N) (y a)) a).unop
  exact h (Finset.mem_singleton_self _)

lemma SIdx_eq_image (N : ℕ) (n : ℕ) (y : Fin (n + 1) → Idx.{(u)} N) :
    SIdx N n y = Finset.univ.image y := by
  refine le_antisymm ?_ ?_
  · have h : (∏ᶜ (DSMap.Mix2.chartIdx (Idx.{(u)} N) ∘ y)).unop ⊆ Finset.univ.image y :=
      leOfHom (Pi.lift (f := fun a => DSMap.Mix2.chartIdx (Idx.{(u)} N) (y a))
        (fun a => (homOfLE (Finset.singleton_subset_iff.mpr
          (Finset.mem_image_of_mem y (Finset.mem_univ a)))).op)).unop
    exact h
  · intro m hm
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hm
    exact SIdx_mem N n y a

lemma SIdx_nonempty (N : ℕ) (n : ℕ) (y : Fin (n + 1) → Idx.{(u)} N) :
    (SIdx N n y).Nonempty :=
  ⟨y 0, SIdx_mem N n y 0⟩

lemma ROpen_eq_IOpen (i : X ⟶ DSMap.PSpace A N) (n : ℕ) (y : Fin (n + 1) → Idx.{(u)} N) :
    ROpen i n y = IOpen i n y := by
  refine le_antisymm ?_ ?_
  · refine le_iInf (fun m => le_iInf (fun hm => ?_))
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp (by rw [← SIdx_eq_image]; exact hm)
    exact leOfHom (Pi.π (fun a => DSMap.Mix2.chartCover i (y a)) a)
  · refine leOfHom (Pi.lift (f := fun a => DSMap.Mix2.chartCover i (y a)) (fun a => homOfLE ?_))
    exact iInf_le_of_le (y a) (iInf_le_of_le (SIdx_mem N n y a) le_rfl)

end Setup

section Cmp

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} {N : ℕ}
  {i : X ⟶ DSMap.PSpace A N} {W : Type u} [CommRing W] {ψ : A →+* W} {t : Idx.{(u)} N → W}

/-- The `y`-th factor of the `m`-th term of the chart Čech complex. -/
noncomputable abbrev chartTerm (t : Idx.{(u)} N → W) (m : ℕ) (y : Fin (m + 1) → Idx.{(u)} N) :
    ModuleCat.{u} W :=
  (DSMap.Mix2.chartPresheaf t).obj (op (∏ᶜ (DSMap.Mix2.chartIdx (Idx.{(u)} N) ∘ y)))

/-- The `y`-th factor of the `m`-th term of the Čech complex of the cover. -/
noncomputable abbrev coverTerm (A : Type u) [CommRing A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    (i : X ⟶ DSMap.PSpace A N) (m : ℕ) (y : Fin (m + 1) → Idx.{(u)} N) : ModuleCat.{u} A :=
  (DSMap.cechPresheaf A X f).obj (op (ROpen i m y))

/-- The comparison map at the `y`-th chart simplex: the transport `Γ(ROpen) → Γ(IOpen)`
followed by the chart comparison `D.toFun`. -/
noncomputable def cmpMap (D : SecData A X f N i W ψ t) (n : ℕ) (y : Fin (n + 1) → Idx.{(u)} N) :
    (DSMap.cechPresheaf A X f).obj (op (ROpen i n y)) ⟶
      (ModuleCat.restrictScalars ψ).obj
        ((DSMap.Mix2.chartPresheaf t).obj
          (op (∏ᶜ (DSMap.Mix2.chartIdx (Idx.{(u)} N) ∘ y)))) :=
  letI : Algebra A Γ(X, IOpen i n y) := (DSMap.phiU A X f (IOpen i n y)).toAlgebra
  letI : Module A (DSMap.Mix2.chartRing t (SIdx N n y)) :=
    Module.compHom (DSMap.Mix2.chartRing t (SIdx N n y)) ψ
  (DSMap.cechPresheaf A X f).map (eqToHom (congrArg op (ROpen_eq_IOpen i n y))) ≫
    (ModuleCat.ofHom
      { toFun := fun x => D.toFun (SIdx N n y) (SIdx_nonempty N n y) x
        map_add' := fun x y => map_add _ x y
        map_smul' := fun a x => by
          show D.toFun (SIdx N n y) (SIdx_nonempty N n y)
            ((DSMap.phiU A X f (⨅ m ∈ SIdx N n y, DSMap.Mix2.chartCover i m)) a * x) =
              ψ a • (D.toFun (SIdx N n y) (SIdx_nonempty N n y) x)
          rw [D.toFun_smul, Algebra.smul_def] } :
      ModuleCat.of A Γ(X, IOpen i n y) ⟶ ModuleCat.of A (DSMap.Mix2.chartRing t (SIdx N n y)))

end Cmp

end Work.DSSEC

section CechD

set_option backward.isDefEq.respectTransparency false

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {D : Type u'} [Category.{v'} D]
  [HasProducts.{w} D] [Preadditive D] {ι : Type w} (U : ι → C) (P : Cᵒᵖ ⥤ D)

/-- The component formula for the Čech differential, in universes where the target category
`D` has its morphisms in a possibly different universe
(`Work.DSF1.Cech.cechComplexFunctor_d_π` requires them to coincide). -/
theorem cech_d_π (n : ℕ) (x : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n+1⦌)).I) :
    ((cechComplexFunctor U).obj P).d n (n+1) ≫
        (Pi.π (fun y => P.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n+1⦌)).obj y))) x)
      = ∑ a : Fin (n+2), (-1 : ℤ) ^ (a : ℕ) •
          ((Pi.π (fun y => P.obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj y)))
              (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ a).op).f x)) ≫
            P.map (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ a).op).φ x).op) := by
  simp only [CategoryTheory.cechComplexFunctor,
    CategoryTheory.Limits.FormalCoproduct.cochainComplexFunctor_obj_d]
  rw [CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  rw [Preadditive.sum_comp, Finset.sum_congr rfl (fun i _ => Preadditive.zsmul_comp _ _ _)]
  simp only [CosimplicialObject.δ, FormalCoproduct.cosimplicialObjectFunctor_obj_map,
    Pi.lift_comp_π]

end CechD

import Mathlib
import Submission.Work.DSSEC.Defs
import Submission.Work.DSSEC.cmpMap_natural

/-! The `ℕ`-complex comparison map and the induced `ℤ`-complex chain map. -/

attribute [local instance] MvPolynomial.gradedAlgebra
open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped ZeroObject
open DSMap DSMap.Mix2

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

universe u

namespace Work.DSSEC


section Main

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} {N : ℕ}
  {i : X ⟶ DSMap.PSpace A N} {W : Type u} [CommRing W] {ψ : A →+* W} {t : Idx.{(u)} N → W}

/-- The `n`-th component of the `ℕ`-complex comparison map. -/
noncomputable def chiZeroComp (D : SecData A X f N i W ψ t) (n : ℕ) :
    (DSMap.cech A X f (DSMap.Mix2.chartCover i)).X n ⟶
      (((ModuleCat.restrictScalars ψ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (DSMap.Mix2.chartCech t)).X n :=
  Fan.IsLimit.lift
    (Limits.isLimitOfHasProductOfPreservesLimit (ModuleCat.restrictScalars ψ) (chartTerm t n))
    (fun y => Pi.π (coverTerm A X f i n) y ≫ cmpMap D n y)

lemma chiZeroComp_fac (D : SecData A X f N i W ψ t) (n : ℕ) (y : Fin (n + 1) → Idx.{(u)} N) :
    chiZeroComp D n ≫
        (ModuleCat.restrictScalars ψ).map (Pi.π (chartTerm t n) y) =
      Pi.π (coverTerm A X f i n) y ≫ cmpMap D n y :=
  Fan.IsLimit.fac _ _ _

/-- The summand identity: the `a`-th summand of the componentwise chain condition. -/
lemma chiZeroComp_summand (D : SecData A X f N i W ψ t) (n : ℕ) (a : Fin (n + 2))
    (y : Fin (n + 2) → Idx.{(u)} N) :
    chiZeroComp D n ≫
        (ModuleCat.restrictScalars ψ).map
          (Pi.π (chartTerm t n)
              (((FormalCoproduct.mk (Idx.{(u)} N) (DSMap.Mix2.chartIdx (Idx.{(u)} N))).cech.map
                (SimplexCategory.δ a).op).f y) ≫
            (DSMap.Mix2.chartPresheaf t).map
              (((FormalCoproduct.mk (Idx.{(u)} N) (DSMap.Mix2.chartIdx (Idx.{(u)} N))).cech.map
                (SimplexCategory.δ a).op).φ y).op) =
      Pi.π (coverTerm A X f i n)
          (((FormalCoproduct.mk (Idx.{(u)} N) (DSMap.Mix2.chartCover i)).cech.map
            (SimplexCategory.δ a).op).f y) ≫
        (DSMap.cechPresheaf A X f).map
          (((FormalCoproduct.mk (Idx.{(u)} N) (DSMap.Mix2.chartCover i)).cech.map
            (SimplexCategory.δ a).op).φ y).op ≫ cmpMap D (n + 1) y := by
  rw [Functor.map_comp, ← Category.assoc, chiZeroComp_fac, ← Category.assoc]
  exact congrArg (fun m => Pi.π (coverTerm A X f i n)
      (((FormalCoproduct.mk (Idx.{(u)} N) (DSMap.Mix2.chartCover i)).cech.map
        (SimplexCategory.δ a).op).f y) ≫ m) (cmpMap_natural D n a y)

/-- The chain condition for the `ℕ`-complex comparison map, componentwise. -/
lemma chiZeroComp_comm (D : SecData A X f N i W ψ t) (n : ℕ) (y : Fin (n + 2) → Idx.{(u)} N) :
    chiZeroComp D n ≫
        (((ModuleCat.restrictScalars ψ).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (DSMap.Mix2.chartCech t)).d n (n + 1) ≫
        (ModuleCat.restrictScalars ψ).map (Pi.π (chartTerm t (n + 1)) y) =
      (DSMap.cech A X f (DSMap.Mix2.chartCover i)).d n (n + 1) ≫
        chiZeroComp D (n + 1) ≫
          (ModuleCat.restrictScalars ψ).map (Pi.π (chartTerm t (n + 1)) y) := by
  have hchart : chiZeroComp D n ≫
      ((ModuleCat.restrictScalars ψ).map ((DSMap.Mix2.chartCech t).d n (n + 1)) ≫
        (ModuleCat.restrictScalars ψ).map (Pi.π (chartTerm t (n + 1)) y)) =
      ∑ a : Fin (n + 2), (-1 : ℤ) ^ (a : ℕ) •
        (chiZeroComp D n ≫ (ModuleCat.restrictScalars ψ).map
          (Pi.π (chartTerm t n)
              (((FormalCoproduct.mk (Idx.{(u)} N) (DSMap.Mix2.chartIdx (Idx.{(u)} N))).cech.map
                (SimplexCategory.δ a).op).f y) ≫
            (DSMap.Mix2.chartPresheaf t).map
              (((FormalCoproduct.mk (Idx.{(u)} N) (DSMap.Mix2.chartIdx (Idx.{(u)} N))).cech.map
                (SimplexCategory.δ a).op).φ y).op)) := by
    rw [← Functor.map_comp]
    have h := cech_d_π (U := DSMap.Mix2.chartIdx (Idx.{(u)} N))
      (P := DSMap.Mix2.chartPresheaf t) n y
    erw [h]
    simp only [Functor.map_sum, Functor.map_zsmul, Preadditive.comp_sum,
      Preadditive.comp_zsmul]
    rfl
  have hsource : (DSMap.cech A X f (DSMap.Mix2.chartCover i)).d n (n + 1) ≫
      (chiZeroComp D (n + 1) ≫
        (ModuleCat.restrictScalars ψ).map (Pi.π (chartTerm t (n + 1)) y)) =
      ∑ a : Fin (n + 2), (-1 : ℤ) ^ (a : ℕ) •
        (Pi.π (coverTerm A X f i n)
            (((FormalCoproduct.mk (Idx.{(u)} N) (DSMap.Mix2.chartCover i)).cech.map
              (SimplexCategory.δ a).op).f y) ≫
          (DSMap.cechPresheaf A X f).map
            (((FormalCoproduct.mk (Idx.{(u)} N) (DSMap.Mix2.chartCover i)).cech.map
              (SimplexCategory.δ a).op).φ y).op ≫ cmpMap D (n + 1) y) := by
    rw [chiZeroComp_fac]
    rw [← Category.assoc]
    have h := cech_d_π (U := DSMap.Mix2.chartCover i)
      (P := DSMap.cechPresheaf A X f) n y
    erw [h]
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
    rfl
  rw [show chiZeroComp D n ≫
        (((ModuleCat.restrictScalars ψ).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (DSMap.Mix2.chartCech t)).d n (n + 1) ≫
        (ModuleCat.restrictScalars ψ).map (Pi.π (chartTerm t (n + 1)) y) =
      chiZeroComp D n ≫
        ((ModuleCat.restrictScalars ψ).map ((DSMap.Mix2.chartCech t).d n (n + 1)) ≫
          (ModuleCat.restrictScalars ψ).map (Pi.π (chartTerm t (n + 1)) y)) from rfl]
  rw [hchart, hsource]
  exact Finset.sum_congr rfl (fun a _ => congrArg
    (fun m => (-1 : ℤ) ^ (a : ℕ) • m) (chiZeroComp_summand D n a y))

/-- The `ℕ`-complex comparison map. -/
noncomputable def chiZero (D : SecData A X f N i W ψ t) :
    DSMap.cech A X f (DSMap.Mix2.chartCover i) ⟶
      ((ModuleCat.restrictScalars ψ).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (DSMap.Mix2.chartCech t) where
  f := chiZeroComp D
  comm' n m hnm := by
    obtain rfl : n + 1 = m := hnm
    refine Fan.IsLimit.hom_ext
      (Limits.isLimitOfHasProductOfPreservesLimit (ModuleCat.restrictScalars ψ)
        (chartTerm t (n + 1))) _ _ (fun y => ?_)
    exact chiZeroComp_comm D n y

end Main


section ZLevel

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)} {N : ℕ}
  {i : X ⟶ DSMap.PSpace A N} {W : Type u} [CommRing W] {ψ : A →+* W} {t : Idx.{(u)} N → W}

/-- The degreewise components of the `ℤ`-complex comparison map, indexed by `Option ℕ`
so that the extension to `ℤ`-degrees is definitional. -/
noncomputable def aux2 (D : SecData A X f N i W ψ t) :
    ∀ o : Option ℕ,
      HomologicalComplex.extend.X (DSMap.cech A X f (DSMap.Mix2.chartCover i)) o ⟶
        (ModuleCat.restrictScalars ψ).obj
          (HomologicalComplex.extend.X (DSMap.Mix2.chartCech t) o)
  | some n => (chiZero D).f n
  | none => 0

/-- The chain condition for the components `aux2`. -/
lemma aux2_comm (D : SecData A X f N i W ψ t) (o₁ o₂ : Option ℕ) :
    aux2 D o₁ ≫ (ModuleCat.restrictScalars ψ).map
        (HomologicalComplex.extend.d (DSMap.Mix2.chartCech t) o₁ o₂) =
      HomologicalComplex.extend.d (DSMap.cech A X f (DSMap.Mix2.chartCover i)) o₁ o₂ ≫
        aux2 D o₂ := by
  rcases o₁ with _ | n <;> rcases o₂ with _ | m
  · -- none, none
    have h1 : HomologicalComplex.extend.d (DSMap.Mix2.chartCech t) none none = 0 :=
      HomologicalComplex.extend.d_none_eq_zero _ _ _ rfl
    have h2 : HomologicalComplex.extend.d (DSMap.cech A X f (DSMap.Mix2.chartCover i))
        none none = 0 := HomologicalComplex.extend.d_none_eq_zero _ _ _ rfl
    rw [show aux2 D none = 0 from rfl, h1, h2, ]
    simp
  · -- none, some
    have h1 : HomologicalComplex.extend.d (DSMap.Mix2.chartCech t) none (some m) = 0 :=
      HomologicalComplex.extend.d_none_eq_zero _ _ _ rfl
    have h2 : HomologicalComplex.extend.d (DSMap.cech A X f (DSMap.Mix2.chartCover i))
        none (some m) = 0 := HomologicalComplex.extend.d_none_eq_zero _ _ _ rfl
    rw [show aux2 D none = 0 from rfl, h1, h2, ]
    simp
  · -- some, none
    have h1 : HomologicalComplex.extend.d (DSMap.Mix2.chartCech t) (some n) none = 0 :=
      HomologicalComplex.extend.d_none_eq_zero' _ _ _ rfl
    have h2 : HomologicalComplex.extend.d (DSMap.cech A X f (DSMap.Mix2.chartCover i))
        (some n) none = 0 := HomologicalComplex.extend.d_none_eq_zero' _ _ _ rfl
    rw [show aux2 D none = 0 from rfl, h1, h2, ]
    simp
  · -- some, some
    show (chiZero D).f n ≫ (ModuleCat.restrictScalars ψ).map
        ((DSMap.Mix2.chartCech t).d n m) =
      (DSMap.cech A X f (DSMap.Mix2.chartCover i)).d n m ≫ (chiZero D).f m
    rw [show (ModuleCat.restrictScalars ψ).map ((DSMap.Mix2.chartCech t).d n m)
        = (((ModuleCat.restrictScalars ψ).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (DSMap.Mix2.chartCech t)).d n m from rfl]
    exact (chiZero D).comm n m

/-- The `ℤ`-complex comparison map. -/
noncomputable def chi (D : SecData A X f N i W ψ t) :
    DSMap.cechZ A X f (DSMap.Mix2.chartCover i) ⟶ DSMap.Mix2.chartCechA ψ t where
  f i' := aux2 D (ComplexShape.embeddingUpNat.r i')
  comm' i' j' hij := by
    show aux2 D (ComplexShape.embeddingUpNat.r i') ≫
        (ModuleCat.restrictScalars ψ).map
          (HomologicalComplex.extend.d (DSMap.Mix2.chartCech t)
            (ComplexShape.embeddingUpNat.r i') (ComplexShape.embeddingUpNat.r j')) =
      HomologicalComplex.extend.d (DSMap.cech A X f (DSMap.Mix2.chartCover i))
          (ComplexShape.embeddingUpNat.r i') (ComplexShape.embeddingUpNat.r j') ≫
        aux2 D (ComplexShape.embeddingUpNat.r j')
    exact aux2_comm D _ _

/-- The degree-`0` computation of the `ℤ`-complex comparison map. -/
lemma aux2_iso (D : SecData A X f N i W ψ t) {o : Option ℕ} {n : ℕ} (h : o = some n) :
    (HomologicalComplex.extend.XIso (DSMap.cech A X f (DSMap.Mix2.chartCover i)) h).inv ≫
        aux2 D o ≫ (ModuleCat.restrictScalars ψ).map
          (HomologicalComplex.extend.XIso (DSMap.Mix2.chartCech t) h).hom =
      aux2 D (some n) := by
  cases h
  dsimp only [aux2, HomologicalComplex.extend.XIso]
  simp only [eqToIso_refl, Iso.refl_inv, Iso.refl_hom, Functor.map_id, Category.comp_id]
  exact Category.id_comp _

/-- `chi` in degree `0` composed with the extension isomorphisms of the frozen statement
is the `ℕ`-level comparison map in degree `0`. -/
lemma chi_comp_iso (D : SecData A X f N i W ψ t) :
    ((DSMap.cech A X f (DSMap.Mix2.chartCover i)).extendXIso
        ComplexShape.embeddingUpNat (i := 0) rfl).inv ≫ (chi D).f 0 ≫
      (ModuleCat.restrictScalars ψ).map
        ((DSMap.Mix2.chartCech t).extendXIso ComplexShape.embeddingUpNat
          (i := 0) rfl).hom =
      (chiZero D).f 0 := by
  exact aux2_iso D (h := ComplexShape.Embedding.r_eq_some ComplexShape.embeddingUpNat
    (rfl : ComplexShape.embeddingUpNat.f (0 : ℕ) = (0 : ℤ)))

end ZLevel

end Work.DSSEC

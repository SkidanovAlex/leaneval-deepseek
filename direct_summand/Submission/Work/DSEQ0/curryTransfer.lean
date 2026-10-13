import Mathlib
import Submission.Work.DSEQ0.CurryAffineCover
import Submission.Work.DSEQ0.eulerCharDefs
import Submission.Work.DSMap.Map
import Submission.Work.DSG4a.cech_d_comm_pi
import Submission.Work.DSM5b.CechIsoDefs

/-!
# `Work.DSEQ0.curryTransfer`

The Čech complex of the "curried" presheaf `V ↦ Γ(X, W ⊓ V)` along a family `U` of opens of `X`
is identified, degreewise and compatibly with the differentials, with the Čech complex of the
structure sheaf of `Spec Γ(X,W)` along the pulled-back family `curryPullback hW U`.

The comparison at a tuple `y` is the restriction along the open immersion
`ctG hW : Spec Γ(X,W) ⟶ X`:
`Γ(X, W ⊓ ⨅ a, U (y a)) ⟶ Γ(Spec Γ(X,W), ⨅ a, ctG ⁻¹ᵁ (W ⊓ U (y a)))`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

attribute [local implicit_reducible] CategoryTheory.Limits.FormalCoproduct.power
  DSMap.cechPresheaf DSMap.cech
  Work.DSEQ0.curryPresheaf Work.DSEQ0.cechPresheafCurry Work.DSEQ0.cechPresheafBif
  Work.DSEQ0.meetBif CategoryTheory.Limits.FormalCoproduct.mapPower

open CategoryTheory AlgebraicGeometry Limits Opposite
open scoped Simplicial BigOperators

namespace Work.DSEQ0

universe u

/-! All auxiliary definitions and lemmas of this file live in the namespace
`Work.DSEQ0.CurryTransferAux`, so that this module can be imported together with other files
of the workspace without name clashes. -/

namespace CurryTransferAux

/-! ## The open immersion `Spec Γ(X,W) ⟶ X` and the pulled-back cover -/

section Geo

variable {X : AlgebraicGeometry.Scheme.{u}} {W : X.Opens} (hW : AlgebraicGeometry.IsAffineOpen W)
  {ι : Type u} (U : ι → X.Opens)

/-- The open immersion `Spec Γ(X,W) ⟶ X`. -/
noncomputable abbrev ctG :
    AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.obj (Opposite.op W))) ⟶ X :=
  hW.fromSpec

/-- The pulled-back family of opens on `Spec Γ(X,W)`. -/
noncomputable abbrev ctV :
    ι → (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.obj (Opposite.op W)))).Opens :=
  curryPullback hW U

lemma ctV_apply (i : ι) : ctV hW U i = ctG hW ⁻¹ᵁ (W ⊓ U i) := rfl

lemma ctG_preimage_self : ctG hW ⁻¹ᵁ W = ⊤ := by
  have h := Scheme.Hom.preimage_opensRange (ctG hW)
  rwa [AlgebraicGeometry.IsAffineOpen.opensRange_fromSpec hW] at h

/-- Preimages of finite infima of opens. -/
lemma preimage_iInf_fin {κ : Type*} [Finite κ] (S : κ → X.Opens) :
    ctG hW ⁻¹ᵁ (⨅ i, S i) = ⨅ i, ctG hW ⁻¹ᵁ S i := by
  apply TopologicalSpace.Opens.ext
  rw [TopologicalSpace.Opens.coe_iInf
      (α := AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.obj (Opposite.op W))))
      (U := fun i => ctG hW ⁻¹ᵁ S i)]
  change (ctG hW).base ⁻¹' (((⨅ i, S i) : X.Opens) : Set X) = ⋂ i, ↑(ctG hW ⁻¹ᵁ S i)
  rw [TopologicalSpace.Opens.coe_iInf (U := S), Set.preimage_iInter]
  exact Set.iInter_congr fun i => rfl

lemma ctV_iInf {m : ℕ} (y : Fin (m+1) → ι) :
    (⨅ a, ctV hW U (y a)) = ctG hW ⁻¹ᵁ (⨅ a, U (y a)) := by
  simp only [ctV_apply]
  rw [← preimage_iInf_fin hW (fun a : Fin (m+1) => W ⊓ U (y a)), ← inf_iInf,
    Scheme.Hom.preimage_inf, ctG_preimage_self, top_inf_eq]

lemma cechOb_eq_iInf {Y : AlgebraicGeometry.Scheme.{u}} {κ : Type u} (V : κ → Y.Opens)
    (n : ℕ) (x : Work.DSG4a.cechIx V n) :
    Work.DSG4a.cechOb V n x = ⨅ a, V (x a) := by
  simp only [Work.DSG4a.cechOb, FormalCoproduct.cech_obj, FormalCoproduct.power]
  apply le_antisymm
  · exact le_iInf (fun a => (Pi.π (fun a => V (x a)) a).le)
  · exact (Pi.lift (fun a => homOfLE (iInf_le (fun a => V (x a)) a))).le

/-- The tuple object on the `Spec` side is the preimage of the tuple object on `X`. -/
lemma ctYV_eq (n : ℕ) (y : Work.DSG4a.cechIx (ctV hW U) n) :
    Work.DSG4a.cechOb (ctV hW U) n y = ctG hW ⁻¹ᵁ (W ⊓ Work.DSG4a.cechOb U n y) := by
  rw [cechOb_eq_iInf (ctV hW U) n y, cechOb_eq_iInf U n y, ctV_iInf hW U,
    Scheme.Hom.preimage_inf, ctG_preimage_self, top_inf_eq]

/-- The intersection of `W` with the `X`-tuple object is the image of the `Spec`-tuple object. -/
lemma ctZYV_eq (n : ℕ) (y : Work.DSG4a.cechIx U n) :
    W ⊓ Work.DSG4a.cechOb U n y = ctG hW ''ᵁ (Work.DSG4a.cechOb (ctV hW U) n y) := by
  rw [ctYV_eq hW U n y, Scheme.Hom.image_preimage_eq_opensRange_inf,
    AlgebraicGeometry.IsAffineOpen.opensRange_fromSpec hW]
  rw [inf_left_idem]

/-- The meet-restriction morphism `W ⊓ T ⟶ W ⊓ T'` induced by `γ : op T ⟶ op T'`. -/
noncomputable abbrev meetMor {W : X.Opens} {T T' : X.Opens}
    (γ : Opposite.op T ⟶ Opposite.op T') : Opposite.op (W ⊓ T) ⟶ Opposite.op (W ⊓ T') :=
  (homOfLE (inf_le_inf_left W (leOfHom γ.unop))).op

end Geo

/-! ## Products in `ModuleCat` and the components of the Čech differential -/

section Products

variable {R : Type u} [CommRing R]

/-- The evaluation equivalence identifying the categorical product in `ModuleCat` with the
concrete product of the underlying types. -/
noncomputable def pe {κ : Type u} (M : κ → ModuleCat.{u} R) :
    ↥(∏ᶜ M) ≃ (Π i, ↥(M i)) :=
  (ModuleCat.piIsoPi M).toLinearEquiv.toEquiv

lemma pe_apply {κ : Type u} (M : κ → ModuleCat.{u} R) (z : ↥(∏ᶜ M)) (i : κ) :
    pe M z i = (Pi.π M i).hom z := by
  show (ModuleCat.piIsoPi M).toLinearEquiv.toEquiv z i = _
  rw [← ModuleCat.piIsoPi_hom_ker_subtype M i]
  rfl

/-- Evaluation of a finite sum of morphisms in `ModuleCat`. -/
lemma hom_sum_smul_apply {κ : Type*} {M N : ModuleCat.{u} R}
    (f : κ → (M ⟶ N)) (s : Finset κ) (c : κ → ℤ) (z : ↥M) :
    (ModuleCat.Hom.hom ((∑ i ∈ s, c i • f i) : M ⟶ N) : ↥M → ↥N) z
      = ∑ i ∈ s, c i • (f i).hom z := by
  rw [ModuleCat.hom_sum]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ModuleCat.hom_zsmul]
  rfl

section Cech

variable {C : Type u} [Category C] [HasFiniteProducts C]
  {ι' : Type u} (U' : ι' → C) (P : Cᵒᵖ ⥤ ModuleCat.{u} R)

/-- **Component formula for the Čech differential**: the `y`-component of `d n (n+1)` is the
alternating sum of the components of the deletion cofaces. -/
theorem pe_d (n : ℕ)
    (z : ↥(((cechComplexFunctor U').obj P).X n)) (y : Work.DSG4a.cechIx U' (n+1)) :
    (pe (fun y' : Work.DSG4a.cechIx U' (n+1) => P.obj (op (Work.DSG4a.cechOb U' (n+1) y')))
        ((((cechComplexFunctor U').obj P).d n (n+1)).hom z)) y
      = ∑ a : Fin (n+2), (-1 : ℤ) ^ (a : ℕ) •
          (P.map (((FormalCoproduct.mk ι' U').cech.map (SimplexCategory.δ a).op).φ y).op).hom
            ((pe (fun y' : Work.DSG4a.cechIx U' n => P.obj (op (Work.DSG4a.cechOb U' n y'))) z)
              (((FormalCoproduct.mk ι' U').cech.map (SimplexCategory.δ a).op).f y)) := by
  rw [pe_apply]
  have h1 : (Pi.π (fun y' : Work.DSG4a.cechIx U' (n+1) =>
        P.obj (op (Work.DSG4a.cechOb U' (n+1) y'))) y).hom
        ((((cechComplexFunctor U').obj P).d n (n+1)).hom z)
      = ((((cechComplexFunctor U').obj P).d n (n+1)) ≫
          Pi.π (fun y' : Work.DSG4a.cechIx U' (n+1) =>
            P.obj (op (Work.DSG4a.cechOb U' (n+1) y'))) y).hom z :=
    rfl
  rw [h1]
  have h2 := Work.DSM5b.cech_d_comp_π_gen (U := U') (P := P) (n := n) y
  rw [h2]
  rw [hom_sum_smul_apply]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1

end Cech

end Products

/-! ## The comparison `kappa` between the curried and the `Spec`-side coefficients -/

section Kappa

variable (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
  (f : X ⟶ AlgebraicGeometry.Spec (.of A)) (W : X.Opens) (hW : AlgebraicGeometry.IsAffineOpen W)
  {ι : Type u} (U : ι → X.Opens)

/-- The restriction `Γ(X, W ⊓ cechOb U n y) ⟶ Γ(Spec Γ(X,W), cechOb ctV n y)`, as a morphism of
rings. -/
noncomputable def kappaMor (n : ℕ) (y : Work.DSG4a.cechIx U n) :
    X.presheaf.obj (Opposite.op (W ⊓ Work.DSG4a.cechOb U n y)) ⟶
      (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.obj (Opposite.op W)))).presheaf.obj
        (Opposite.op (Work.DSG4a.cechOb (curryPullback hW U) n y)) :=
  X.presheaf.map (eqToHom (ctZYV_eq hW U n y).symm).op ≫
    ((ctG hW).appIso (Work.DSG4a.cechOb (curryPullback hW U) n y)).hom

/-- The comparison of the coefficients of the two Čech complexes, in degree `n` and at the
tuple `y`. -/
noncomputable def kappa (n : ℕ) (y : Work.DSG4a.cechIx U n) :
    ↥(X.presheaf.obj (Opposite.op (W ⊓ Work.DSG4a.cechOb U n y))) ≃
      ↥((AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.obj (Opposite.op W)))).presheaf.obj
        (Opposite.op (Work.DSG4a.cechOb (curryPullback hW U) n y))) :=
  (((X.presheaf.mapIso (eqToIso (ctZYV_eq hW U n y).symm).op).commRingCatIsoToRingEquiv).trans
    (((ctG hW).appIso (Work.DSG4a.cechOb (curryPullback hW U) n y)).commRingCatIsoToRingEquiv)).toEquiv

lemma kappa_apply (n : ℕ) (y : Work.DSG4a.cechIx U n)
    (x : ↥(X.presheaf.obj (Opposite.op (W ⊓ Work.DSG4a.cechOb U n y)))) :
    kappa X W hW U n y x = (kappaMor X W hW U n y).hom x := rfl

lemma curryPresheaf_map_apply (T T' : X.Opens) (γ : Opposite.op T ⟶ Opposite.op T')
    (w : ↥(X.presheaf.obj (Opposite.op (W ⊓ T)))) :
    ((curryPresheaf A X f W).map γ).hom w = (X.presheaf.map (meetMor γ)).hom w := rfl

/-- **Naturality of `kappaMor`** in the Čech differential, at the level of morphisms. -/
theorem kappa_mor_nat (n : ℕ) (a : Fin (n+2)) (y : Work.DSG4a.cechIx U (n+1)) :
    X.presheaf.map (meetMor (((FormalCoproduct.mk ι U).cech.map
        (SimplexCategory.δ a).op).φ y).op) ≫ kappaMor X W hW U (n+1) y
      = kappaMor X W hW U n
          (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ a).op).f y) ≫
        (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.obj (Opposite.op W)))).presheaf.map
          ((((FormalCoproduct.mk ι (curryPullback hW U)).cech.map
            (SimplexCategory.δ a).op).φ y)).op := by
  simp only [kappaMor]
  have hnat := Scheme.Hom.appIso_hom_naturality (ctG hW)
    (U := Work.DSG4a.cechOb (curryPullback hW U) n
      (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ a).op).f y))
    (V := Work.DSG4a.cechOb (curryPullback hW U) (n+1) y)
    ((((FormalCoproduct.mk ι (curryPullback hW U)).cech.map
      (SimplexCategory.δ a).op).φ y)).op
  rw [Category.assoc, ← hnat, ← Category.assoc, ← Category.assoc]
  have hkey : X.presheaf.map (meetMor (((FormalCoproduct.mk ι U).cech.map
          (SimplexCategory.δ a).op).φ y).op) ≫
        X.presheaf.map (eqToHom (ctZYV_eq hW U (n+1) y).symm).op
      = X.presheaf.map (eqToHom (ctZYV_eq hW U n
            (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ a).op).f y)).symm).op ≫
        X.presheaf.map ((Scheme.Hom.opensFunctor (ctG hW)).map
          (((FormalCoproduct.mk ι (curryPullback hW U)).cech.map
            (SimplexCategory.δ a).op).φ y)).op := by
    rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    exact congrArg X.presheaf.map (Subsingleton.elim _ _)
  rw [hkey]
  simp only [Quiver.Hom.unop_op]

/-- Additivity of `kappa` on finite sums. -/
lemma kappa_sum {κ : Type*} (n : ℕ) (y : Work.DSG4a.cechIx U n) (s : Finset κ) (c : κ → ℤ)
    (g : κ → ↥(X.presheaf.obj (Opposite.op (W ⊓ Work.DSG4a.cechOb U n y)))) :
    kappa X W hW U n y (∑ i ∈ s, c i • g i)
      = ∑ i ∈ s, c i • kappa X W hW U n y (g i) := by
  rw [kappa_apply, kappaMor, CommRingCat.comp_apply, map_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul, map_zsmul]
  rw [kappa_apply, kappaMor, CommRingCat.comp_apply]

/-- **Naturality of `kappa`** in the Čech differential, at the level of elements. -/
lemma kappa_nat (n : ℕ) (a : Fin (n+2)) (y : Work.DSG4a.cechIx U (n+1))
    (w : ↥(X.presheaf.obj (Opposite.op
            (W ⊓ Work.DSG4a.cechOb U n
              (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ a).op).f y))))) :
    kappa X W hW U (n+1) y
        (((curryPresheaf A X f W).map
          (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ a).op).φ y).op).hom w)
      = ((AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.obj (Opposite.op W)))).presheaf.map
          (((FormalCoproduct.mk ι (curryPullback hW U)).cech.map
            (SimplexCategory.δ a).op).φ y).op).hom
        (kappa X W hW U n
          (((FormalCoproduct.mk ι U).cech.map (SimplexCategory.δ a).op).f y) w) := by
  rw [kappa_apply, kappa_apply, curryPresheaf_map_apply]
  exact congrArg (fun g => CommRingCat.Hom.hom g w) (kappa_mor_nat X W hW U n a y)

end Kappa

/-! ## The comparison of the two Čech complexes -/

section Assembly

variable (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
  (f : X ⟶ AlgebraicGeometry.Spec (.of A)) (W : X.Opens) (hW : AlgebraicGeometry.IsAffineOpen W)
  {ι : Type u} (U : ι → X.Opens)

/-- The degreewise comparison of the two Čech complexes. -/
noncomputable def curryPhi (n : ℕ) :
    ↥(((CategoryTheory.cechComplexFunctor U).obj (curryPresheaf A X f W)).X n) ≃
      ↥((DSMap.cech (X.presheaf.obj (Opposite.op W))
          (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.obj (Opposite.op W))))
          (CategoryTheory.CategoryStruct.id _)
          (curryPullback hW U)).X n) :=
  (pe (fun y : Work.DSG4a.cechIx U n =>
      (curryPresheaf A X f W).obj (Opposite.op (Work.DSG4a.cechOb U n y)))).trans
    ((Equiv.piCongrRight (fun y : Work.DSG4a.cechIx U n => kappa X W hW U n y)).trans
      (pe (fun y : Work.DSG4a.cechIx (curryPullback hW U) n =>
        (DSMap.cechPresheaf (X.presheaf.obj (Opposite.op W))
          (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.obj (Opposite.op W))))
          (CategoryTheory.CategoryStruct.id _)).obj
            (Opposite.op (Work.DSG4a.cechOb (curryPullback hW U) n y)))).symm)

lemma pe_curryPhi (n : ℕ)
    (z : ↥(((CategoryTheory.cechComplexFunctor U).obj (curryPresheaf A X f W)).X n)) :
    pe (fun y : Work.DSG4a.cechIx (curryPullback hW U) n =>
        (DSMap.cechPresheaf (X.presheaf.obj (Opposite.op W))
          (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.obj (Opposite.op W))))
          (CategoryTheory.CategoryStruct.id _)).obj
            (Opposite.op (Work.DSG4a.cechOb (curryPullback hW U) n y)))
        (curryPhi A X f W hW U n z)
      = (Equiv.piCongrRight (fun y : Work.DSG4a.cechIx U n => kappa X W hW U n y))
          (pe (fun y : Work.DSG4a.cechIx U n =>
            (curryPresheaf A X f W).obj (Opposite.op (Work.DSG4a.cechOb U n y))) z) := by
  simp only [curryPhi, Equiv.trans_apply]
  exact Equiv.apply_symm_apply _ _

end Assembly

end CurryTransferAux

open CurryTransferAux

theorem curryTransfer (A : Type u) [CommRing A] (X : AlgebraicGeometry.Scheme.{u})
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) {W : X.Opens} (hW : AlgebraicGeometry.IsAffineOpen W)
    {ι : Type u} (U : ι → X.Opens) :
    ∃ (φ : ∀ n : ℕ,
      ↥(((CategoryTheory.cechComplexFunctor U).obj (Work.DSEQ0.curryPresheaf A X f W)).X n) ≃
        ↥((DSMap.cech (X.presheaf.obj (Opposite.op W))
            (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.obj (Opposite.op W))))
            (CategoryTheory.CategoryStruct.id _)
            (Work.DSEQ0.curryPullback hW U)).X n)),
      ∀ (n : ℕ)
        (x : ↥(((CategoryTheory.cechComplexFunctor U).obj (Work.DSEQ0.curryPresheaf A X f W)).X n)),
        φ (n + 1) ((((CategoryTheory.cechComplexFunctor U).obj (Work.DSEQ0.curryPresheaf A X f W)).d n (n + 1)).hom x) =
          (((DSMap.cech (X.presheaf.obj (Opposite.op W))
            (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.obj (Opposite.op W))))
            (CategoryTheory.CategoryStruct.id _)
            (Work.DSEQ0.curryPullback hW U)).d n (n + 1)).hom (φ n x)) := by
  refine ⟨fun n => curryPhi A X f W hW U n, ?_⟩
  intro n x
  dsimp only
  apply (pe (fun y : Work.DSG4a.cechIx (curryPullback hW U) (n+1) =>
    (DSMap.cechPresheaf (X.presheaf.obj (Opposite.op W))
      (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.obj (Opposite.op W))))
      (CategoryTheory.CategoryStruct.id _)).obj
        (Opposite.op (Work.DSG4a.cechOb (curryPullback hW U) (n+1) y)))).injective
  funext y
  rw [pe_curryPhi, Equiv.piCongrRight_apply, Pi.map_apply]
  rw [pe_d (U' := U) (P := curryPresheaf A X f W) (n := n) (z := x) (y := y)]
  rw [kappa_sum]
  simp only [DSMap.cech]
  erw [pe_d (U' := curryPullback hW U)
    (P := DSMap.cechPresheaf (X.presheaf.obj (Opposite.op W))
      (AlgebraicGeometry.Spec (CommRingCat.of (X.presheaf.obj (Opposite.op W))))
      (CategoryTheory.CategoryStruct.id _)) (n := n) (z := curryPhi A X f W hW U n x) (y := y)]
  rw [pe_curryPhi]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  congr 1
  exact kappa_nat A X f W hW U n a y _

end Work.DSEQ0

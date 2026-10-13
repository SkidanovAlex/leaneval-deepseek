import Mathlib
import Submission.Work.DSEQ0.AugDefs
import Submission.Work.DSF1.Sheaf.cechTrivAll_local

/-!
# The "unit case" of the `AddCommGrpCat`-valued Čech complex: setup

This module contains the vocabulary shared by the proof of
`Work.DSEQ0.coaugAb_sectionsV_unit_case` (the coaugmentation of the Čech complex of the family
`U` with coefficients in `Γ(− ⊓ V, 𝒪_X)` is injective with image the `0`-cocycles, when `V` is
contained in one member `U i₀` of the family).

The `AddCommGrpCat`-valued contracting homotopy itself (`kAb`, `deltaXAb`, `homotopy_succAb`) is
in `Submission/Work/DSF1/Sheaf/cechTrivAll_local.lean`; here we add the two missing ingredients
of the *augmented* complex:

* `Work.DSEQ0.IsIsoDelAbTop`: the hypothesis of the unit case for the target category
  `AddCommGrpCat` (the coface maps inserting `i₀` are inverted, and so is `Q(⊤) ⟶ Q(U i₀)`);
* `Work.DSEQ0.kTopAb`: the contraction `Č⁰ ⟶ Q(⊤)` of the coaugmentation, and the identity
  `coaugAb ≫ kTopAb = 𝟙` (`Work.DSEQ0.coaugAb_comp_kTopAb`), which gives injectivity;
* `Work.DSEQ0.isIso_sectionsVMap`: the restriction `Γ(W ⊓ V) ⟶ Γ(W' ⊓ V)` of the structure
  sheaf is an isomorphism as soon as `W ⊓ V = W' ⊓ V`.  This is what makes the Čech complex of
  the family `U` with coefficients `Γ(− ⊓ V, 𝒪_X)` satisfy the unit-case hypotheses when
  `V ≤ U i₀`;
* `Work.DSEQ0.isIsoDelAbTop_sectionsV`: the resulting verification of `IsIsoDelAbTop` for the
  specific coefficient presheaf `C.cechShPresheaf X ⋙ sectionsV X V`.
-/

namespace Work.DSEQ0

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

set_option backward.isDefEq.respectTransparency false

variable {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}

/-! ## Restriction maps which do not change the sections -/

/-- **The sections of the Čech presheaf over `V` only see `⊓ V`.**  If `f : W' ⟶ W` is a
morphism of opens with `W' ⊓ V = W ⊓ V` (i.e. an isomorphism after intersecting with `V`),
then the induced map `Γ(W ⊓ V) ⟶ Γ(W' ⊓ V)` — that is,
`(sectionsV X V).map ((cechShPresheaf X).map f.op)` — is an isomorphism.

This is the technical core of the "unit case": it is applied to the coface maps of the Čech
nerve which insert the index `i₀` when `V ≤ U i₀`. -/
theorem isIso_sectionsVMap {W W' : X.Opens} (f : W' ⟶ W) (V : X.Opens)
    (heq : W' ⊓ V = W ⊓ V) :
    IsIso ((sectionsV X V).map ((C.cechShPresheaf X).map f.op)) := by
  have h : W' ≤ W := leOfHom f
  have heq' : W'.ι ''ᵁ (W'.ι ⁻¹ᵁ V) = W.ι ''ᵁ (W.ι ⁻¹ᵁ V) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact heq
  have hIsoCR : IsIso (X.presheaf.map (homOfLE (le_of_eq heq')).op) := by
    have h1 : IsIso (homOfLE (le_of_eq heq') :
        W'.ι ''ᵁ (W'.ι ⁻¹ᵁ V) ⟶ W.ι ''ᵁ (W.ι ⁻¹ᵁ V)) :=
      CategoryTheory.homOfLE_isIso_of_eq _ heq'
    have h2 : IsIso ((homOfLE (le_of_eq heq')).op) := (isIso_op_iff _).mpr h1
    exact @Functor.map_isIso _ _ _ _ _ _ X.presheaf _ h2
  have hbij : Function.Bijective
      (ConcreteCategory.hom (X.presheaf.map (homOfLE (le_of_eq heq')).op)) :=
    (ConcreteCategory.isIso_iff_bijective _).mp hIsoCR
  have hfun : (ConcreteCategory.hom
        (AlgebraicGeometry.Scheme.Modules.Hom.app (Work.DSF1.Sheaf.restr h) V)
        : ↑Γ(Work.DSF1.secSheaf W, V) → ↑Γ(Work.DSF1.secSheaf W', V))
      = (ConcreteCategory.hom (X.presheaf.map (homOfLE (le_of_eq heq')).op)
        : ↑Γ(Work.DSF1.secSheaf W, V) → ↑Γ(Work.DSF1.secSheaf W', V)) := by
    funext x
    exact Work.DSF1.Sheaf.restr_app h V (le_of_eq heq') x
  have hbij' : Function.Bijective (ConcreteCategory.hom
      (AlgebraicGeometry.Scheme.Modules.Hom.app (Work.DSF1.Sheaf.restr h) V)) := by
    rw [hfun]; exact hbij
  rw [show (sectionsV X V).map ((C.cechShPresheaf X).map f.op) =
      AlgebraicGeometry.Scheme.Modules.Hom.app (Work.DSF1.Sheaf.restr h) V from rfl]
  exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij'

/-! ## The hypothesis of the unit case -/

/-- The hypothesis of the "unit case", for coefficients a presheaf `Q` of abelian groups:
`Q` inverts the coface maps of the Čech nerve which insert the index `i₀`, and also the
restriction `Q(⊤) ⟶ Q (U i₀)`.  (For coefficients of the form `Γ(− ⊓ V)` this holds as soon
as `V ≤ U i₀`: see `Work.DSEQ0.isIsoDelAbTop_sectionsV`.) -/
def IsIsoDelAbTop (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (i₀ : ι) : Prop :=
  IsIso (Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)).op) ∧
    Work.DSF1.Sheaf.IsIsoDelAb U Q i₀

/-- The composite of the coaugmentation with the projection to the component at the constant
index `i₀` is the restriction `Q(⊤) ⟶ Q (U i₀)`, hence an isomorphism. -/
lemma isIso_coaugAb_π (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (i₀ : ι)
    (h : IsIsoDelAbTop U Q i₀) :
    IsIso (coaugAb X U Q ≫
      Limits.Pi.π (fun y : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 y)))
        (fun _ => i₀)) := by
  have h1 : coaugAb X U Q ≫
      Limits.Pi.π (fun y : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 y)))
        (fun _ => i₀) =
      Q.map (homOfLE (le_top : Work.DSF1.Cech.Eobj U 0 (fun _ => i₀) ≤ ⊤)).op :=
    Limits.Pi.lift_comp_π _ _
  rw [h1]
  exact h.1

/-- The contraction of the coaugmentation: `Č⁰ ⟶ Q(⊤)`, the projection to the `i₀`-component
followed by the inverse of `coaugAb ≫ π_{i₀}`. -/
noncomputable def kTopAb (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) {i₀ : ι}
    (h : IsIsoDelAbTop U Q i₀) : ((cechComplexFunctor U).obj Q).X 0 ⟶ Q.obj (op ⊤) :=
  Limits.Pi.π (fun y : Fin 1 → ι => Q.obj (op (Work.DSF1.Cech.Eobj U 0 y))) (fun _ => i₀) ≫
    (@asIso _ _ _ _ _ (isIso_coaugAb_π U Q i₀ h)).inv

/-- `kTopAb` is a retraction of the coaugmentation; in particular `coaugAb` is injective. -/
lemma coaugAb_comp_kTopAb (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) {i₀ : ι}
    (h : IsIsoDelAbTop U Q i₀) :
    coaugAb X U Q ≫ kTopAb U Q h = 𝟙 (Q.obj (op ⊤)) := by
  rw [kTopAb, ← Category.assoc]
  exact (@asIso _ _ _ _ _ (isIso_coaugAb_π U Q i₀ h)).hom_inv_id

/-! ## The coefficient presheaf `Γ(− ⊓ V, 𝒪_X)` satisfies the unit-case hypotheses -/

/-- For `V ≤ U i₀`, the coefficient presheaf `C.cechShPresheaf X ⋙ sectionsV X V`
(`W ↦ Γ(W ⊓ V, 𝒪_X)`) satisfies the unit-case hypotheses
`Work.DSEQ0.IsIsoDelAbTop`. -/
theorem isIsoDelAbTop_sectionsV (X : AlgebraicGeometry.Scheme.{u}) {ι : Type u}
    (U : ι → X.Opens) (V : X.Opens) (i₀ : ι) (hV : V ≤ U i₀) :
    IsIsoDelAbTop U (C.cechShPresheaf X ⋙ sectionsV X V) i₀ := by
  refine ⟨?_, ?_⟩
  · have heq : Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀) ⊓ V = ⊤ ⊓ V := by
      rw [Work.DSF1.Cech.Eobj_zero_eq U i₀, inf_eq_right.mpr hV, top_inf_eq]
    exact isIso_sectionsVMap (homOfLE (le_top :
      Work.DSF1.Cech.Eobj U 0 (fun _ : Fin 1 => i₀) ≤ ⊤)) V heq
  · intro n x
    have hf : Work.DSF1.Cech.Eobj U n
        (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 0).op).f
          (Work.DSF1.Cech.insIdx U i₀ n x)) =
        Work.DSF1.Cech.Eobj U n x :=
      congrArg (Work.DSF1.Cech.Eobj U n) (Work.DSF1.Cech.cech_map_delta0_f U i₀ n x)
    have heq : Work.DSF1.Cech.Eobj U (n+1) (Work.DSF1.Cech.insIdx U i₀ n x) ⊓ V =
        Work.DSF1.Cech.Eobj U n
          (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 0).op).f
            (Work.DSF1.Cech.insIdx U i₀ n x)) ⊓ V := by
      rw [Work.DSF1.Cech.Eobj_insIdx U i₀ n x, hf, inf_assoc, inf_eq_right.mpr hV]
    exact isIso_sectionsVMap (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 0).op).φ
      (Work.DSF1.Cech.insIdx U i₀ n x)) V heq

end Work.DSEQ0

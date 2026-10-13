import Mathlib
import Submission.Work.DSEQ0.AugDefs
import Submission.Work.DSF1.Sheaf.cechTrivAll_local
import Submission.Work.DSF1.Sheaf.cechTrivAll_of_restrP
import Submission.Work.DSMX0bU.cechTrivAll_of_le_mem

/-!
# The Čech complex of `Γ(V, (j_W)_* 𝒪_W)` has trivial cohomology when `V ≤ U i₀`

Let `X` be a scheme, `U : ι → X.Opens` a family of opens, `V : X.Opens` and `i₀ : ι` with
`V ≤ U i₀`.  We show that the Čech complex of the family `U` with coefficients in the presheaf

`Q : W ↦ Γ(V, (j_W)_* 𝒪_W)  =  𝒪_X (W ⊓ V)`

(the composite of the Čech presheaf `Work.DSEQ0.C.cechShPresheaf` with the "sections over `V`"
functor `Work.DSEQ0.sectionsV X V`) has trivial cohomology in positive degrees
(`Work.DSF1.Sheaf.CechTrivAll`).

The complex is contractible.  Inserting the index `i₀` at position `0` of a simplex does not
change the open `E n x ⊓ V`, because `E (n+1) (insIdx U i₀ n x) = E n x ⊓ U i₀` and `V ≤ U i₀`;
hence the cofaces inserting `i₀` act on `Q` by a map which, after intersecting with `V`, is an
inclusion of an open into itself — an isomorphism.  The general machinery of
`Work.DSF1.Sheaf.cechTrivAll_local` (`IsIsoDelAb`, the contracting homotopy `kAb` and the
homotopy identity `homotopy_succAb`, assembled in
`Work.DSMX0bU.cechTrivAll_of_contractible`) then finishes the job.

The only geometric input is the componentwise computation `isIso_restr_app_sectionsV`: the
component at `V` of the restriction `(j_B)_* 𝒪_B ⟶ (j_A)_* 𝒪_A` (for opens `B ≤ A`) is the
restriction map `𝒪_X (A ⊓ V) ⟶ 𝒪_X (B ⊓ V)` of the structure sheaf, via
`Work.DSF1.Sheaf.restr_app`, hence an isomorphism as soon as `B ⊓ V = A ⊓ V`.
-/

namespace Work.DSEQ0

open CategoryTheory AlgebraicGeometry Opposite Limits TopologicalSpace
open scoped Simplicial BigOperators

universe u

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The component at the open `V` of the restriction `(j_B)_*𝒪_B ⟶ (j_A)_*𝒪_A` associated
with `B ≤ A` is the restriction map `𝒪_X (A ⊓ V) ⟶ 𝒪_X (B ⊓ V)` of the structure sheaf
(`Work.DSF1.Sheaf.restr_app`); in particular it is an isomorphism when `B ⊓ V = A ⊓ V`. -/
lemma isIso_restr_app_sectionsV {A B : X.Opens} (hab : B ≤ A) {V : X.Opens}
    (h : B ⊓ V = A ⊓ V) :
    IsIso (Scheme.Modules.Hom.app (Work.DSF1.Sheaf.restr hab) V) := by
  have hp : B.ι ''ᵁ (B.ι ⁻¹ᵁ V) = A.ι ''ᵁ (A.ι ⁻¹ᵁ V) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, h]
  rw [ConcreteCategory.isIso_iff_bijective]
  have hfun : ⇑(Scheme.Modules.Hom.app (Work.DSF1.Sheaf.restr hab) V) =
      ⇑(X.presheaf.map (homOfLE (le_of_eq hp)).op) :=
    funext (fun x => Work.DSF1.Sheaf.restr_app hab V (le_of_eq hp) x)
  rw [hfun]
  have h2 : IsIso (X.presheaf.map (homOfLE (le_of_eq hp)).op) := by
    have h1 : IsIso (homOfLE (le_of_eq hp)) := Work.DSF1.Sheaf.isIso_homOfLE_of_eq _ hp
    exact Functor.map_isIso X.presheaf _
  exact (ConcreteCategory.isIso_iff_bijective _).mp h2

/-- A map of the presheaf `Q = cechShPresheaf X ⋙ sectionsV X V` induced by a morphism
`f : W ⟶ W'` of opens is an isomorphism as soon as `f` becomes an equality after intersecting
with `V`. -/
lemma isIso_comp_map_sectionsV {W W' : (X.Opens)ᵒᵖ} (f : W ⟶ W') (V : X.Opens)
    (h : W'.unop ⊓ V = W.unop ⊓ V) :
    IsIso ((sectionsV X V).map ((C.cechShPresheaf X).map f)) := by
  change IsIso (Scheme.Modules.Hom.app (Work.DSF1.Sheaf.restr (leOfHom f.unop)) V)
  exact isIso_restr_app_sectionsV (leOfHom f.unop) h

/-- The coefficient presheaf `W ↦ Γ(V, (j_W)_* 𝒪_W)` inverts the cofaces of the Čech nerve
which insert the index `i₀`, when `V ≤ U i₀`. -/
lemma isIsoDelAb_sectionsV {ι : Type u} (U : ι → X.Opens) (V : X.Opens) (i₀ : ι)
    (hV : V ≤ U i₀) :
    Work.DSF1.Sheaf.IsIsoDelAb U (C.cechShPresheaf X ⋙ sectionsV X V) i₀ := by
  intro n x
  have hf : Work.DSF1.Cech.Eobj U n
      (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 0).op).f
        (Work.DSF1.Cech.insIdx U i₀ n x)) = Work.DSF1.Cech.Eobj U n x :=
    congrArg (Work.DSF1.Cech.Eobj U n) (Work.DSF1.Cech.cech_map_delta0_f U i₀ n x)
  have h : Work.DSF1.Cech.Eobj U (n+1) (Work.DSF1.Cech.insIdx U i₀ n x) ⊓ V =
      Work.DSF1.Cech.Eobj U n (((Work.DSF1.Cech.E U).map (SimplexCategory.δ 0).op).f
        (Work.DSF1.Cech.insIdx U i₀ n x)) ⊓ V := by
    rw [Work.DSF1.Cech.Eobj_insIdx U i₀ n x, hf, inf_assoc, inf_eq_right.mpr hV]
  exact isIso_comp_map_sectionsV _ V h

theorem cechTrivAll_sectionsV (X : AlgebraicGeometry.Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (V : X.Opens) (i₀ : ι) (hV : V ≤ U i₀) :
    Work.DSF1.Sheaf.CechTrivAll ((CategoryTheory.cechComplexFunctor U).obj
      (CategoryTheory.Functor.comp (Work.DSEQ0.C.cechShPresheaf X)
        (Work.DSEQ0.sectionsV X V))) := by
  have h : Work.DSF1.Sheaf.IsIsoDelAb U (Work.DSEQ0.C.cechShPresheaf X ⋙
      Work.DSEQ0.sectionsV X V) i₀ := isIsoDelAb_sectionsV U V i₀ hV
  exact Work.DSMX0bU.cechTrivAll_of_contractible (Work.DSF1.Sheaf.kAb U _ h)
    (Work.DSF1.Sheaf.homotopy_succAb U _ h)

end Work.DSEQ0

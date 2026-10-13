import Mathlib
import Submission.Work.DSF1.Cech.CechSetup
import Submission.Work.DSF1.Cech.CechComponents

/-!
# Auxiliary data for the "unit case" of the Čech complex

For a presheaf `Q` of `S`-modules on the opens of a scheme and a family of opens
`U : ι → X.Opens` with a distinguished index `i₀` such that `Q` inverts the coface
maps inserting `i₀` (`IsIsoDeletion U Q i₀`), we construct the "contracting homotopy"
`k` of the augmented Čech complex.

In degree `n`, the Čech complex is the product over `x : E _⦋n⦌` of `Q (E n x)`.  The
map `k n : X (n + 1) ⟶ X n` is built from the projection to the `i₀`-inserted index
followed by the inverse of the coface isomorphism; `kTop : X 0 ⟶ Q (⊤)` is the
analogous map in degree `0`, and `coaug : Q(⊤) ⟶ X 0` is the coaugmentation.

The main content of this file is the set of simplicial identities satisfied by these
maps (the "extra codegeneracy" identities), from which the exactness of the augmented
complex follows.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Cech

variable {X : Scheme.{u}} {S : Type u} [CommRing S] {ι : Type u}
variable (U : ι → X.Opens) (Q : X.Opensᵒᵖ ⥤ ModuleCat S)

/-- The cosimplicial object whose alternating coface complex is the Čech complex. -/
noncomputable abbrev Cosimplicial : CosimplicialObject (ModuleCat S) :=
  (FormalCoproduct.cosimplicialObjectFunctor (FormalCoproduct.mk ι U).cech).obj Q

/-- The `y`-th component of the coface `δ i` of the Čech cosimplicial object. -/
lemma cech_delta_comp_π (n : ℕ) (i : Fin (n+2))
    (y : ((E U).obj (op ⦋n+1⦌)).I) :
    (Cosimplicial U Q).δ i ≫
        Pi.π (fun y : ((E U).obj (op ⦋n+1⦌)).I => Q.obj (op (Eobj U (n+1) y))) y =
      Pi.π (fun z : ((E U).obj (op ⦋n⦌)).I => Q.obj (op (Eobj U n z)))
          (((E U).map (SimplexCategory.δ i).op).f y) ≫
        Q.map (((E U).map (SimplexCategory.δ i).op).φ y).op := by
  show Pi.lift _ ≫ Pi.π _ y = _
  exact Pi.lift_comp_π _ _

omit [CommRing S] in
/-- The open `E 0 x` at the `i₀`-point is `U i₀`. -/
lemma Eobj_zero_eq (i₀ : ι) : Eobj U 0 (fun _ => i₀) = U i₀ := by
  show (∏ᶜ (U ∘ (fun _ : Fin 1 => i₀))) = U i₀
  apply le_antisymm
  · exact CategoryTheory.leOfHom (Limits.Pi.π _ 0)
  · exact CategoryTheory.leOfHom (Limits.Pi.lift (fun _ => 𝟙 (U i₀)))

variable {i₀ : ι}

/-- The coaugmentation composed with the projection to the `i₀`-component is an
isomorphism, by the hypothesis `IsIsoDeletion`. -/
lemma isIso_coaug_π (h : IsIsoDeletion U Q i₀) :
    IsIso (coaug U Q ≫
      Pi.π (fun y : ((E U).obj (op ⦋0⦌)).I => Q.obj (op (Eobj U 0 y))) (fun _ => i₀)) := by
  have h1 : coaug U Q ≫
      Pi.π (fun y : ((E U).obj (op ⦋0⦌)).I => Q.obj (op (Eobj U 0 y))) (fun _ => i₀) =
      Q.map (homOfLE (le_top : Eobj U 0 (fun _ => i₀) ≤ ⊤)).op :=
    Pi.lift_comp_π _ _
  rw [h1, Eobj_zero_eq U i₀]
  exact h.1

/-- The "contraction at the bottom": `X 0 ⟶ Q(⊤)`, inverse to the coaugmentation on the
`i₀`-component. -/
noncomputable def kTop (h : IsIsoDeletion U Q i₀) :
    ((cechComplexFunctor U).obj Q).X 0 ⟶ Q.obj (op ⊤) :=
  Pi.π (fun y : ((E U).obj (op ⦋0⦌)).I => Q.obj (op (Eobj U 0 y))) (fun _ => i₀) ≫
    (@asIso _ _ _ _
      (coaug U Q ≫
        Pi.π (fun y : ((E U).obj (op ⦋0⦌)).I => Q.obj (op (Eobj U 0 y))) (fun _ => i₀))
      (isIso_coaug_π U Q h)).inv

/-- `coaug` is a split monomorphism: its composite with `kTop` is the identity. -/
lemma coaug_comp_kTop (h : IsIsoDeletion U Q i₀) :
    coaug U Q ≫ kTop U Q h = 𝟙 (Q.obj (op ⊤)) := by
  rw [kTop, ← Category.assoc]
  exact (@asIso _ _ _ _
    (coaug U Q ≫
      Pi.π (fun y : ((E U).obj (op ⦋0⦌)).I => Q.obj (op (Eobj U 0 y))) (fun _ => i₀))
    (isIso_coaug_π U Q h)).hom_inv_id

/-- The coface isomorphism `Q (E n x) ≅ Q (E (n+1) (insert i₀ x))`. -/
noncomputable def isoIns (h : IsIsoDeletion U Q i₀) (n : ℕ)
    (x : ((E U).obj (op ⦋n⦌)).I) :
    Q.obj (op (Eobj U n x)) ≅ Q.obj (op (Eobj U (n+1) (insIdx U i₀ n x))) :=
  @asIso _ _ _ _ (Q.map (((E U).map (SimplexCategory.δ 0).op).φ (insIdx U i₀ n x)).op) (h.2 n x)

/-- The contracting homotopy of the Čech complex, in degrees `≥ 1`. -/
noncomputable def k (h : IsIsoDeletion U Q i₀) (n : ℕ) :
    ((cechComplexFunctor U).obj Q).X (n+1) ⟶ ((cechComplexFunctor U).obj Q).X n :=
  Pi.lift (f := fun z : ((E U).obj (op ⦋n⦌)).I => Q.obj (op (Eobj U n z)))
    (fun x => Pi.π (fun y : ((E U).obj (op ⦋n+1⦌)).I => Q.obj (op (Eobj U (n+1) y)))
        (insIdx U i₀ n x) ≫
          @inv _ _ _ _ (Q.map (((E U).map (SimplexCategory.δ 0).op).φ (insIdx U i₀ n x)).op)
            (h.2 n x))

/-- The `x`-th component of the homotopy `k n`. -/
lemma k_comp_π (h : IsIsoDeletion U Q i₀) (n : ℕ)
    (x : ((E U).obj (op ⦋n⦌)).I) :
    k U Q h n ≫ Pi.π (fun z : ((E U).obj (op ⦋n⦌)).I => Q.obj (op (Eobj U n z))) x =
      Pi.π (fun y : ((E U).obj (op ⦋n+1⦌)).I => Q.obj (op (Eobj U (n+1) y)))
        (insIdx U i₀ n x) ≫
          @inv _ _ _ _ (Q.map (((E U).map (SimplexCategory.δ 0).op).φ (insIdx U i₀ n x)).op)
            (h.2 n x) := by
  simp only [k, Pi.lift_comp_π]

/-- The "extra codegeneracy" identity `δ₀ ≫ k = 𝟙` in degree `n`. -/
lemma delta0_comp_k (h : IsIsoDeletion U Q i₀) (n : ℕ) :
    (Cosimplicial U Q).δ (0 : Fin (n+2)) ≫ k U Q h n = 𝟙 _ := by
  apply Pi.hom_ext
  intro x
  show ((Cosimplicial U Q).δ (0 : Fin (n+2)) ≫ k U Q h n) ≫
      Pi.π (f := fun z : ((E U).obj (op ⦋n⦌)).I => Q.obj (op (Eobj U n z))) x =
    Pi.π (f := fun z : ((E U).obj (op ⦋n⦌)).I => Q.obj (op (Eobj U n z))) x
  rw [Category.assoc, k_comp_π, ← Category.assoc, cech_delta_comp_π]
  rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

end Work.DSF1.Cech

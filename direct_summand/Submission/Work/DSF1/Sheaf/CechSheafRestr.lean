import Mathlib
import Submission.Work.DSF1.Sheaf.AcycDefs

/-!
# The restriction presheaves of a presheaf along an open, and the sheaf-level Čech complex

For a scheme `X`, an open `W` and a presheaf `P` of abelian groups on `X.Opens`, we define the
presheaf `restrP P W` with `(restrP P W) V = P (V ⊓ W)`, and its functoriality in `W`
(`restrNat`, contravariant in `W`), giving a functor

`restrPFunctor P : (X.Opens)ᵒᵖ ⥤ ((X.Opens)ᵒᵖ ⥤ AddCommGrpCat)`.

Composing with Mathlib's Čech complex functor `cechComplexFunctor U` yields

`cechComplexP U P : (X.Opens)ᵒᵖ ⥤ CochainComplex AddCommGrpCat ℕ`,

whose value at `op W` is the Čech complex of the family `U` with coefficients the restriction
`V ↦ P (V ⊓ W)`.  Its degree-`n` term evaluated at `⊤` is the degree-`n` term of the concrete
Čech complex `cechComplex U F`.
-/

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits

universe u

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The restriction of a presheaf `P` along the open `W`: the presheaf `V ↦ P (V ⊓ W)`. -/
noncomputable def restrP (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (W : X.Opens) :
    X.Opensᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj V := P.obj (op (V.unop ⊓ W))
  map {V V'} f := P.map (homOfLE (inf_le_inf_right W (leOfHom f.unop))).op
  map_id V := by
    rw [Subsingleton.elim (homOfLE (inf_le_inf_right W (leOfHom (𝟙 V).unop)) :
      V.unop ⊓ W ⟶ V.unop ⊓ W) (𝟙 (V.unop ⊓ W))]
    exact P.map_id (op (V.unop ⊓ W))
  map_comp {V V' V''} f g := by
    have key : (homOfLE (inf_le_inf_right W (leOfHom f.unop))).op ≫
        (homOfLE (inf_le_inf_right W (leOfHom g.unop))).op =
        (homOfLE (inf_le_inf_right W (leOfHom (f ≫ g).unop))).op := Subsingleton.elim _ _
    rw [← P.map_comp, key]

@[simp]
lemma restrP_obj (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (W V : X.Opens) :
    (restrP P W).obj (op V) = P.obj (op (V ⊓ W)) := rfl

lemma restrP_map_homOfLE (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (W : X.Opens) {V V' : X.Opens}
    (h : V' ≤ V) :
    (restrP P W).map (homOfLE h).op = P.map (homOfLE (inf_le_inf_right W h)).op := rfl

/-- Composition of the images under `P` of two `homOfLE`-morphisms. -/
lemma map_homOfLE_comp (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) {a b c : X.Opens}
    (h : b ≤ a) (h' : c ≤ b) :
    P.map (homOfLE h).op ≫ P.map (homOfLE h').op = P.map (homOfLE (h'.trans h)).op := by
  rw [← P.map_comp]
  exact congrArg (fun m : op a ⟶ op c => P.map m) (Subsingleton.elim _ _)

/-- The canonical comparison `restrP P W ⟶ restrP P W'` for `W' ≤ W`. -/
noncomputable def restrNat (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) {W W' : X.Opens} (h : W' ≤ W) :
    restrP P W ⟶ restrP P W' where
  app V := P.map (homOfLE (inf_le_inf_left V.unop h)).op
  naturality {V V'} f := by
    show P.map (homOfLE (inf_le_inf_right W (leOfHom f.unop))).op ≫
        P.map (homOfLE (inf_le_inf_left V'.unop h)).op =
      P.map (homOfLE (inf_le_inf_left V.unop h)).op ≫
        P.map (homOfLE (inf_le_inf_right W' (leOfHom f.unop))).op
    rw [map_homOfLE_comp, map_homOfLE_comp]

@[simp]
lemma restrNat_app (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) {W W' : X.Opens} (h : W' ≤ W)
    (V : (X.Opens)ᵒᵖ) :
    (restrNat P h).app V = P.map (homOfLE (inf_le_inf_left V.unop h)).op := rfl

@[simp]
lemma restrNat_refl (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (W : X.Opens) :
    restrNat P (le_refl W) = 𝟙 (restrP P W) := by
  apply CategoryTheory.NatTrans.ext
  funext V
  show P.map (homOfLE (inf_le_inf_left V.unop (le_refl W))).op = 𝟙 (P.obj (op (V.unop ⊓ W)))
  rw [Subsingleton.elim (homOfLE (inf_le_inf_left V.unop (le_refl W)) :
    V.unop ⊓ W ⟶ V.unop ⊓ W) (𝟙 (V.unop ⊓ W))]
  exact P.map_id (op (V.unop ⊓ W))

lemma restrNat_comp (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) {W₁ W₂ W₃ : X.Opens}
    (h₁ : W₂ ≤ W₁) (h₂ : W₃ ≤ W₂) :
    restrNat P h₁ ≫ restrNat P h₂ = restrNat P (h₂.trans h₁) := by
  apply CategoryTheory.NatTrans.ext
  funext V
  show P.map (homOfLE (inf_le_inf_left V.unop h₁)).op ≫
      P.map (homOfLE (inf_le_inf_left V.unop h₂)).op =
    P.map (homOfLE (inf_le_inf_left V.unop (h₂.trans h₁))).op
  rw [map_homOfLE_comp]

/-- The functor `(X.Opens)ᵒᵖ ⥤ ((X.Opens)ᵒᵖ ⥤ AddCommGrpCat)` given by `W ↦ restrP P W`. -/
noncomputable def restrPFunctor (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (X.Opens)ᵒᵖ ⥤ ((X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u}) where
  obj W := restrP P W.unop
  map {W W'} f := restrNat P (leOfHom f.unop)
  map_id W := by
    rw [Subsingleton.elim (leOfHom (𝟙 W).unop) (le_refl W.unop), restrNat_refl]
  map_comp {W W' W''} f g := by
    rw [Subsingleton.elim (leOfHom (f ≫ g).unop)
      ((leOfHom g.unop).trans (leOfHom f.unop)), ← restrNat_comp]

/-- The sheaf-level Čech complex: the value at `W` is the Čech complex of the family `U` with
coefficients the restriction of `P` to `W`. -/
noncomputable def cechComplexP {ι : Type u} (U : ι → X.Opens)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) :
    (X.Opens)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  restrPFunctor P ⋙ (cechComplexFunctor (A := AddCommGrpCat.{u}) U)

/-- The degree-`n` term of the sheaf-level Čech complex, as a presheaf: `W ↦ ∏ x, P (⋂ a, U (x a) ⊓ W)`. -/
noncomputable def cechSheafTerm {ι : Type u} (U : ι → X.Opens)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  cechComplexP U P ⋙ HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℕ) n

/-- The differentials of the sheaf-level Čech complex, as natural transformations. -/
noncomputable def cechSheafD {ι : Type u} (U : ι → X.Opens)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    cechSheafTerm U P n ⟶ cechSheafTerm U P (n+1) where
  app W := ((cechComplexP U P).obj W).d n (n+1)
  naturality {W W'} f := HomologicalComplex.Hom.comm ((cechComplexP U P).map f) n (n+1)

lemma cechSheafD_comp {ι : Type u} (U : ι → X.Opens)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    cechSheafD U P n ≫ cechSheafD U P (n+1) = 0 := by
  apply CategoryTheory.NatTrans.ext
  funext W
  show ((cechComplexP U P).obj W).d n (n+1) ≫ ((cechComplexP U P).obj W).d (n+1) (n+2) = 0
  exact HomologicalComplex.d_comp_d ((cechComplexP U P).obj W) n (n+1) (n+2)

end Work.DSF1.Sheaf

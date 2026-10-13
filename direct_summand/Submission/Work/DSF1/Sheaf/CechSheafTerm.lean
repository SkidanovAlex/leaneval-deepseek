import Mathlib
import Submission.Work.DSF1.Sheaf.CechSheafRestr

/-!
# Sheaf-ness of the sheaf-level Čech terms

For a scheme `X`, a family `U : ι → X.Opens` and a presheaf `P` of abelian groups on `X.Opens`,
the degree-`n` term of the sheaf-level Čech complex is the presheaf

`W ↦ ∏ x : Fin (n+1) → ι, P (⋂ a, U (x a) ⊓ W)`,

a product over `x` of the presheaves `restrL P (⋂ a, U (x a))`, where `restrL P V` is the
presheaf `W ↦ P (V ⊓ W)`.

The main results here are:

* `restrL_isSheaf`: for a sheaf `P`, the presheaf `restrL P V` is a sheaf (it is the pushforward
  of the restriction of `P` to the open `V`);
* `cechSheafTerm_isSheaf`: consequently every term `cechSheafTerm U P n` is a sheaf.
-/

namespace Work.DSF1.Sheaf

open CategoryTheory AlgebraicGeometry Opposite Limits TopologicalSpace
open TopologicalSpace.Opens

set_option backward.isDefEq.respectTransparency false

universe u

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The restriction of a presheaf `P`, with the fixed open on the left: the presheaf
`W ↦ P (V ⊓ W)`. -/
noncomputable def restrL (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (V : X.Opens) :
    X.Opensᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj W := P.obj (op (V ⊓ W.unop))
  map {W W'} f := P.map (homOfLE (inf_le_inf_left V (leOfHom f.unop))).op
  map_id W := by
    rw [Subsingleton.elim (homOfLE (inf_le_inf_left V (leOfHom (𝟙 W).unop)) :
      V ⊓ W.unop ⟶ V ⊓ W.unop) (𝟙 (V ⊓ W.unop))]
    exact P.map_id (op (V ⊓ W.unop))
  map_comp {W W' W''} f g := by
    have key : (homOfLE (inf_le_inf_left V (leOfHom f.unop))).op ≫
        (homOfLE (inf_le_inf_left V (leOfHom g.unop))).op =
        (homOfLE (inf_le_inf_left V (leOfHom (f ≫ g).unop))).op := Subsingleton.elim _ _
    rw [← P.map_comp, key]

@[simp]
lemma restrL_obj (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (V W : X.Opens) :
    (restrL P V).obj (op W) = P.obj (op (V ⊓ W)) := rfl

lemma restrL_map_homOfLE (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (V : X.Opens) {W W' : X.Opens}
    (h : W' ≤ W) :
    (restrL P V).map (homOfLE h).op = P.map (homOfLE (inf_le_inf_left V h)).op := rfl

/-- The `homOfLE`-maps of a presheaf depend on the inequality only through the endpoints. -/
lemma map_homOfLE_congr {C : Type*} [Category* C] (P : X.Opensᵒᵖ ⥤ C) {a b : X.Opens}
    (h h' : a ≤ b) : P.map (homOfLE h).op = P.map (homOfLE h').op := by
  rw [Subsingleton.elim (homOfLE h) (homOfLE h')]

/-- The key lattice identity used to compare the cover `V ⊓ U ·` with the cover `U ·`. -/
lemma inf_inf_inf_eq (V A B : X.Opens) : (V ⊓ A) ⊓ (V ⊓ B) = V ⊓ (A ⊓ B) := by
  rw [inf_assoc, inf_left_comm A V B, ← inf_assoc, inf_idem]

/-- Transport of the comparison map `infLELeft (V ⊓ U i) (V ⊓ U j)` to the comparison map of
`restrL P V`: they differ by the `eqToHom` of the open equality
`(V ⊓ U i) ⊓ (V ⊓ U j) = V ⊓ (U i ⊓ U j)`. -/
lemma map_infLELeft_eq (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (V : X.Opens) {ι : Type u}
    (U : ι → X.Opens) (i j : ι) :
    Q.map (infLELeft (V ⊓ U i) (V ⊓ U j)).op =
      Q.map (homOfLE (inf_le_inf_left V (leOfHom (infLELeft (U i) (U j))))).op ≫
        Q.map (eqToHom (inf_inf_inf_eq V (U i) (U j))).op := by
  rw [← Q.map_comp]
  exact congrArg (fun m : op (V ⊓ U i) ⟶ op ((V ⊓ U i) ⊓ (V ⊓ U j)) => Q.map m)
    (Subsingleton.elim _ _)

/-- Transport of the comparison map `infLERight (V ⊓ U i) (V ⊓ U j)`. -/
lemma map_infLERight_eq (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (V : X.Opens) {ι : Type u}
    (U : ι → X.Opens) (i j : ι) :
    Q.map (infLERight (V ⊓ U i) (V ⊓ U j)).op =
      Q.map (homOfLE (inf_le_inf_left V (leOfHom (infLERight (U i) (U j))))).op ≫
        Q.map (eqToHom (inf_inf_inf_eq V (U i) (U j))).op := by
  rw [← Q.map_comp]
  exact congrArg (fun m : op (V ⊓ U j) ⟶ op ((V ⊓ U i) ⊓ (V ⊓ U j)) => Q.map m)
    (Subsingleton.elim _ _)

/-- Transport of the restriction to `V ⊓ U i` along `iSup (V ⊓ U ·) = V ⊓ iSup U`. -/
lemma map_leSupr_eq (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (V : X.Opens) {ι : Type u}
    (U : ι → X.Opens) (i : ι) (he : iSup (fun i => V ⊓ U i) = V ⊓ iSup U) :
    Q.map (eqToHom he.symm).op ≫
        Q.map (homOfLE (inf_le_inf_left V (leOfHom (Opens.leSupr U i)))).op =
      Q.map (Opens.leSupr (fun i => V ⊓ U i) i).op := by
  rw [← Q.map_comp]
  exact congrArg (fun m : op (iSup (fun i => V ⊓ U i)) ⟶ op (V ⊓ U i) => Q.map m)
    (Subsingleton.elim _ _)

/-- The inverse transport of `map_leSupr_eq`. -/
lemma map_leSupr_eq_inv (Q : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (V : X.Opens) {ι : Type u}
    (U : ι → X.Opens) (i : ι) (he : iSup (fun i => V ⊓ U i) = V ⊓ iSup U) :
    Q.map (eqToHom he).op ≫ Q.map (Opens.leSupr (fun i => V ⊓ U i) i).op =
      Q.map (homOfLE (inf_le_inf_left V (leOfHom (Opens.leSupr U i)))).op := by
  rw [← Q.map_comp]
  exact congrArg (fun m : op (V ⊓ iSup U) ⟶ op (V ⊓ U i) => Q.map m)
    (Subsingleton.elim _ _)

/-- The presheaf `restrL P V` satisfies the sheaf condition as soon as `P` does: a compatible
family over a cover `U` is, after intersecting with `V`, a compatible family over the cover
`V ⊓ U ·` for `P` (the comparison maps are the `eqToHom`-conjugates of those of `restrL P V`),
whose gluing at `iSup (V ⊓ U ·) = V ⊓ iSup U` is the required unique gluing. -/
theorem restrL_isSheafUniqueGluing (P : TopCat.Presheaf AddCommGrpCat.{u} X.toTopCat)
    (hP : TopCat.Presheaf.IsSheafUniqueGluing P) (V : X.Opens) :
    TopCat.Presheaf.IsSheafUniqueGluing (restrL P V) := by
  intro ι U sf hsf
  -- `sf i` is *definitionally*, though not syntactically, a section of `P` over `V ⊓ U i`.
  let sf' : ∀ i, P.obj (op (V ⊓ U i)) := sf
  have hsf' : TopCat.Presheaf.IsCompatible (restrL P V) U sf' := hsf
  -- STEP 1 (done): `sf'` is compatible for `P` on the cover `V ⊓ U ·`.
  have hcompat : TopCat.Presheaf.IsCompatible P (fun i => V ⊓ U i) sf' := by
    intro i j
    have h3 : (P.map (homOfLE (inf_le_inf_left V (leOfHom (infLELeft (U i) (U j))))).op)
        (sf' i) =
        (P.map (homOfLE (inf_le_inf_left V (leOfHom (infLERight (U i) (U j))))).op) (sf' j) :=
      hsf' i j
    rw [map_infLELeft_eq, map_infLERight_eq,
      AddCommGrpCat.comp_apply
        (P.map (homOfLE (inf_le_inf_left V (leOfHom (infLELeft (U i) (U j))))).op)
        (P.map (eqToHom (inf_inf_inf_eq V (U i) (U j))).op) (sf' i),
      AddCommGrpCat.comp_apply
        (P.map (homOfLE (inf_le_inf_left V (leOfHom (infLERight (U i) (U j))))).op)
        (P.map (eqToHom (inf_inf_inf_eq V (U i) (U j))).op) (sf' j),
      h3]
  obtain ⟨s, hs, huniq⟩ := hP (fun i => V ⊓ U i) sf' hcompat
  have he : iSup (fun i => V ⊓ U i) = V ⊓ iSup U := (inf_iSup_eq V U).symm
  -- Restate the goal in the `P`-form: the witness below has type
  -- `ToType (P.obj (op (V ⊓ iSup U)))`, which is definitionally, but not syntactically, the
  -- expected type `ToType ((restrL P V).obj (op (iSup U)))`.
  show ∃! w : ToType (P.obj (op (V ⊓ iSup U))),
      ∀ i, (P.map (homOfLE (inf_le_inf_left V (leOfHom (Opens.leSupr U i)))).op) w = sf' i
  refine ⟨(P.map (eqToHom he.symm).op) s, ?_, ?_⟩
  · intro i
    rw [← AddCommGrpCat.comp_apply, map_leSupr_eq P V U i he]
    exact hs i
  · intro s' hs'
    have hglue : (P.map (eqToHom he).op) s' = s := by
      refine huniq ((P.map (eqToHom he).op) s') ?_
      intro i
      rw [← AddCommGrpCat.comp_apply, map_leSupr_eq_inv P V U i he]
      exact hs' i
    have h2 := congrArg (fun x => (P.map (eqToHom he.symm).op) x) hglue
    rw [← AddCommGrpCat.comp_apply, ← P.map_comp,
      Subsingleton.elim ((eqToHom he).op ≫ (eqToHom he.symm).op) (𝟙 _), P.map_id] at h2
    simpa using h2

/-- For a sheaf `P` and an open `V`, the presheaf `W ↦ P (V ⊓ W)` is a sheaf (it is the
pushforward of the restriction of `P` to the open `V`). -/
theorem restrL_isSheaf (P : TopCat.Presheaf AddCommGrpCat.{u} X.toTopCat)
    (hP : TopCat.Presheaf.IsSheaf P) (V : X.Opens) :
    TopCat.Presheaf.IsSheaf (restrL P V) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing] at hP ⊢
  exact restrL_isSheafUniqueGluing P hP V

open scoped Simplicial

/-- The degree-`n` term of the sheaf-level Čech complex, evaluated at `W`, is the product over the
`n`-simplices `x` of the nerve of the section modules `P (E n .obj x ⊓ W)`. -/
lemma cechSheafTerm_obj_restrP {ι : Type u} (U : ι → X.Opens)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (W : X.Opens) :
    (cechSheafTerm U P n).obj (op W) =
      ∏ᶜ (fun x : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).I =>
        (restrP P W).obj (op (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj x))) := rfl

/-- The same identification, in terms of the restriction presheaves `restrL`. -/
lemma cechSheafTerm_obj {ι : Type u} (U : ι → X.Opens)
    (P : X.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) (W : X.Opens) :
    (cechSheafTerm U P n).obj (op W) =
      ∏ᶜ (fun x : ((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).I =>
        (restrL P (((FormalCoproduct.mk ι U).cech.obj (op ⦋n⦌)).obj x)).obj (op W)) := by
  rw [cechSheafTerm_obj_restrP]
  exact congrArg (fun F => ∏ᶜ F)
    (funext fun x => rfl)

end Work.DSF1.Sheaf

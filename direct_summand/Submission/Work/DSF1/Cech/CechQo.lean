import Mathlib
import Submission.Work.DSF1.Cech.CechSetup

/-!
# The presheaf `W ↦ P (W ⊓ V)` and its comparison with `P`

For a presheaf of modules `P` on the opens of a scheme `X` and an open `V`, this file
introduces the presheaf `Qo P V` given by `W ↦ P (W ⊓ V)` and the natural transformation
`etaO P V : P ⟶ Qo P V` given by restriction to `W ⊓ V`.

These are the presheaf-level ingredients of the "localization at a single open" version of
the unit case of the Čech complex: if `V ≤ U i₀` for a member of a family of opens `U`,
then `Qo P V` inverts the coface maps inserting the index `i₀` (`isIsoDeletion_Qo`), so
that the unit case (`Work.DSF1.Cech.UnitCase`) applies to the Čech complex of `Qo P V`
along `U`.

This file contains definitions only (no proofs depending on data still being developed),
so that it can be imported freely.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u v

namespace Work.DSF1.Cech

variable {X : AlgebraicGeometry.Scheme.{u}} {S : Type u} [CommRing S]

/-- The presheaf `W ↦ P (W ⊓ V)`. -/
noncomputable def Qo (P : X.Opensᵒᵖ ⥤ ModuleCat S) (V : X.Opens) :
    X.Opensᵒᵖ ⥤ ModuleCat S where
  obj W := P.obj (Opposite.op (W.unop ⊓ V))
  map {W W'} f := P.map (homOfLE (inf_le_inf_right V f.unop.le)).op
  map_id W := by
    have h : (homOfLE (inf_le_inf_right V (𝟙 W).unop.le)).op =
        𝟙 (Opposite.op (W.unop ⊓ V)) := Subsingleton.elim _ _
    simpa only [h, P.map_id]
  map_comp f g := by
    have h : (homOfLE (inf_le_inf_right V (f ≫ g).unop.le)).op =
        (homOfLE (inf_le_inf_right V f.unop.le)).op ≫
          (homOfLE (inf_le_inf_right V g.unop.le)).op := Subsingleton.elim _ _
    simpa only [h, P.map_comp]

@[simp]
lemma Qo_obj (P : X.Opensᵒᵖ ⥤ ModuleCat S) (V : X.Opens) (W : X.Opensᵒᵖ) :
    (Qo P V).obj W = P.obj (Opposite.op (W.unop ⊓ V)) := rfl

@[simp]
lemma Qo_map (P : X.Opensᵒᵖ ⥤ ModuleCat S) (V : X.Opens) {W W' : X.Opensᵒᵖ}
    (f : W ⟶ W') :
    (Qo P V).map f = P.map (homOfLE (inf_le_inf_right V f.unop.le)).op := rfl

/-- The restriction `P W ⟶ P (W ⊓ V)`, as a natural transformation `P ⟶ Qo P V`. -/
noncomputable def etaO (P : X.Opensᵒᵖ ⥤ ModuleCat S) (V : X.Opens) : P ⟶ Qo P V where
  app W := P.map (homOfLE (inf_le_left : W.unop ⊓ V ≤ W.unop)).op
  naturality {W W'} f := by
    have h : f ≫ (homOfLE (inf_le_left : W'.unop ⊓ V ≤ W'.unop)).op =
        (homOfLE (inf_le_left : W.unop ⊓ V ≤ W.unop)).op ≫
          (homOfLE (inf_le_inf_right V f.unop.le)).op := Subsingleton.elim _ _
    have key : P.map (f ≫ (homOfLE (inf_le_left : W'.unop ⊓ V ≤ W'.unop)).op) =
        P.map ((homOfLE (inf_le_left : W.unop ⊓ V ≤ W.unop)).op ≫
          (homOfLE (inf_le_inf_right V f.unop.le)).op) := congrArg _ h
    simpa only [Qo, P.map_comp] using key

@[simp]
lemma etaO_app (P : X.Opensᵒᵖ ⥤ ModuleCat S) (V : X.Opens) (W : X.Opensᵒᵖ) :
    (etaO P V).app W = P.map (homOfLE (inf_le_left : W.unop ⊓ V ≤ W.unop)).op := rfl

end Work.DSF1.Cech

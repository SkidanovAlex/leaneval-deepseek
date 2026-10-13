import Mathlib
import Submission.Work.DSF1.Cech.CechSetup

/-!
# The "unit case" applied to a principal open

Let `P` be a presheaf of `R`-modules on `X.Opens`, `U : ι → X.Opens` a family of
opens and `i : ι`.  The presheaf `Qi P U i` given by `W ↦ P (W ⊓ U i)` satisfies the
hypothesis `IsIsoDeletion` of `CechSetup` automatically: inserting the index `i`
does not change the intersections, because they already contain `U i`.  Hence the
"unit case" applies to `cechComplexFunctor U (Qi P U i)`.

The natural transformation `P ⟶ Qi P U i` (restriction to `W ⊓ U i`) compares the
Čech complex of `P` with the Čech complex of `Qi P U i`.
-/

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped Simplicial BigOperators

universe u

namespace Work.DSF1.Cech

variable {X : Scheme.{u}} {R : Type u} [CommRing R] {ι : Type u} (U : ι → X.Opens)

/-- The presheaf `W ↦ P (W ⊓ U i)`. -/
noncomputable def Qi (P : X.Opensᵒᵖ ⥤ ModuleCat R) (i : ι) :
    X.Opensᵒᵖ ⥤ ModuleCat R where
  obj W := P.obj (op (W.unop ⊓ U i))
  map {W V} f := P.map (homOfLE (inf_le_inf_right (U i) f.unop.le)).op
  map_id W := by
    have h : (homOfLE (inf_le_inf_right (U i) (𝟙 W).unop.le)).op =
        𝟙 (op (W.unop ⊓ U i)) := Subsingleton.elim _ _
    simpa only [h, P.map_id]
  map_comp f g := by
    have h : (homOfLE (inf_le_inf_right (U i) (f ≫ g).unop.le)).op =
        (homOfLE (inf_le_inf_right (U i) f.unop.le)).op ≫
          (homOfLE (inf_le_inf_right (U i) g.unop.le)).op := Subsingleton.elim _ _
    simpa only [h, P.map_comp]

/-- The restriction `P W ⟶ P (W ⊓ U i)`. -/
noncomputable def etaI (P : X.Opensᵒᵖ ⥤ ModuleCat R) (i : ι) : P ⟶ Qi U P i where
  app W := P.map (homOfLE (inf_le_left : W.unop ⊓ U i ≤ W.unop)).op
  naturality {W V} f := by
    have h : f ≫ (homOfLE (inf_le_left : V.unop ⊓ U i ≤ V.unop)).op =
        (homOfLE (inf_le_left : W.unop ⊓ U i ≤ W.unop)).op ≫
          (homOfLE (inf_le_inf_right (U i) f.unop.le)).op := Subsingleton.elim _ _
    have key : P.map (f ≫ (homOfLE (inf_le_left : V.unop ⊓ U i ≤ V.unop)).op) =
        P.map ((homOfLE (inf_le_left : W.unop ⊓ U i ≤ W.unop)).op ≫
          (homOfLE (inf_le_inf_right (U i) f.unop.le)).op) := congrArg _ h
    simpa only [Qi, P.map_comp] using key

end Work.DSF1.Cech

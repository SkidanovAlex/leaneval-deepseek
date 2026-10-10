import Mathlib
import Submission.Work.Motivic.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Motivic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

/-- Two partial isomorphisms over the base representing the same rational map from a reduced
scheme to a scheme separated over the base agree at every point of the intersection of their
sources. (The `IsOver` hypotheses are needed to apply Mathlib's
`PartialMap.equiv_iff_of_isSeparated`; in the intended application they are automatic because
the target is separated over the base and the source is reduced.) -/
theorem hom_eq_of_toRationalMap_eq {X Y S : Scheme.{0}} [X.Over S] [Y.Over S] [IsReduced X]
    [IsSeparated (Y ↘ S)] (i j : X.PartialIso Y) [i.toPartialMap.IsOver S]
    [j.toPartialMap.IsOver S] (h : i.toRationalMap = j.toRationalMap) {x : X}
    (hxi : x ∈ i.source) (hxj : x ∈ j.source) :
    i.toPartialMap.hom ⟨x, hxi⟩ = j.toPartialMap.hom ⟨x, hxj⟩ := by
  have hd : Dense ((i.source ⊓ j.source : X.Opens) : Set X) :=
    i.dense_source.inter_of_isOpen_left j.dense_source i.source.2
  have heq : i.toPartialMap.equiv j.toPartialMap := PartialMap.toRationalMap_eq_iff.mp h
  have H : (i.toPartialMap.restrict (i.source ⊓ j.source) hd inf_le_left).hom =
      (j.toPartialMap.restrict (i.source ⊓ j.source) hd inf_le_right).hom :=
    (PartialMap.equiv_iff_of_isSeparated (S := S)
      (f := i.toPartialMap) (g := j.toPartialMap)).mp heq
  have H' : (X.homOfLE inf_le_left ≫ i.toPartialMap.hom) =
      (X.homOfLE inf_le_right ≫ j.toPartialMap.hom) := H
  have hL : (X.homOfLE inf_le_left ≫ i.toPartialMap.hom) ⟨x, hxi, hxj⟩ =
      i.toPartialMap.hom ⟨x, hxi⟩ :=
    (Scheme.Hom.comp_apply (X.homOfLE inf_le_left) i.toPartialMap.hom ⟨x, hxi, hxj⟩).trans
      (congrArg i.toPartialMap.hom (Scheme.homOfLE_apply' inf_le_left x ⟨hxi, hxj⟩))
  have hR : (X.homOfLE inf_le_right ≫ j.toPartialMap.hom) ⟨x, hxi, hxj⟩ =
      j.toPartialMap.hom ⟨x, hxj⟩ :=
    (Scheme.Hom.comp_apply (X.homOfLE inf_le_right) j.toPartialMap.hom ⟨x, hxi, hxj⟩).trans
      (congrArg j.toPartialMap.hom (Scheme.homOfLE_apply' inf_le_right x ⟨hxi, hxj⟩))
  have hpt := congrArg (fun (k : (i.source ⊓ j.source : X.Opens).toScheme ⟶ Y) =>
    k ⟨x, hxi, hxj⟩) H'
  exact hL.symm.trans (hpt.trans hR)

end Work.Motivic

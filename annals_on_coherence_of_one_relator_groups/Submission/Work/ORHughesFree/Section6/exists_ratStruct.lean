import Mathlib
import Submission.Work.ORHughesFree.Section6.ClosureBasic
import Submission.Work.ORHughesFree.Section6.ratOpClosure_smul
import Submission.Work.ORHughesFree.Section6.ratOpClosure_spec
import Submission.Work.ORHughesFree.Section6.imElem_mul
import Submission.Work.ORHughesFree.Section6.imElem_isUnit

namespace Work.ORHughesFree.Section6

open Work.ORHughesFree

/-- The rational `Kˣ × G`-semiring structure on the division closure
`D = divisionClosure (Set.range φ)` of the image of `φ : K[G] →+* U` ([JZLA20, §4.3]):

* the two actions are multiplication by the image of the group-like unit
  `imElem φ u = φ (unitOf u)` on the left and on the right;
* the rational operation is `ratOpClosure`, i.e. inversion on the units of `D` and `0` elsewhere.

This is the explicit witness for `exists_ratStruct`. -/
noncomputable def ratStructOf {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    (φ : MonoidAlgebra K G →+* U) :
    RationalUSemiring (Kˣ × G) ↥(divisionClosure (Set.range φ)) where
  ratOp := ratOpClosure _
  ratOp_zero := ratOpClosure_zero _
  smul u x := imElem φ u * x
  smulRight x u := x * imElem φ u
  smul_eq_mul u r := Subtype.ext (by simp)
  smulRight_eq_mul r u := Subtype.ext (by simp)
  smul_mul u v := by
    rw [imElem_mul]
    simp
  smul_one_one := Subtype.ext (by simp [imElem, unitOf_one])
  smulRight_one_one := Subtype.ext (by simp [imElem, unitOf_one])
  smulRight_one u := Subtype.ext (by simp)
  rat_smul u v r := by
    have hu : IsUnit (imElem φ u) := (imElem_isUnit φ u).1
    have hv : IsUnit (imElem φ v) := (imElem_isUnit φ v).1
    have key : ratOpClosure (divisionClosure (Set.range φ)) (imElem φ u * r * imElem φ v) =
        ↑hv.unit⁻¹ * ratOpClosure (divisionClosure (Set.range φ)) r * ↑hu.unit⁻¹ :=
      ratOpClosure_smul _ hu hv r
    calc ratOpClosure (divisionClosure (Set.range φ)) (imElem φ u * (r * imElem φ v))
        = ratOpClosure (divisionClosure (Set.range φ)) (imElem φ u * r * imElem φ v) := by
            rw [mul_assoc]
      _ = ↑hv.unit⁻¹ * ratOpClosure (divisionClosure (Set.range φ)) r * ↑hu.unit⁻¹ := key
      _ = (imElem φ v⁻¹ * ratOpClosure (divisionClosure (Set.range φ)) r) * imElem φ u⁻¹ := by
            rw [(imElem_isUnit φ v).2 hv, (imElem_isUnit φ u).2 hu]

theorem exists_ratStruct {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]
    (φ : MonoidAlgebra K G →+* U) :
    ∃ r : RationalUSemiring (Kˣ × G) ↥(divisionClosure (Set.range φ)),
      (∀ (u : Kˣ × G) (x : ↥(divisionClosure (Set.range φ))),
        ↑(r.smul u x) = φ (Work.ORHughesFree.unitOf u) * ↑x) ∧
      (∀ (x : ↥(divisionClosure (Set.range φ))) (u : Kˣ × G),
        ↑(r.smulRight x u) = ↑x * φ (Work.ORHughesFree.unitOf u)) ∧
      (∀ x : ↥(divisionClosure (Set.range φ)),
        r.ratOp x = Work.ORHughesFree.ratOpClosure (divisionClosure (Set.range φ)) x) :=
  ⟨ratStructOf φ, fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

end Work.ORHughesFree.Section6

import Mathlib
import Submission.Work.ORHughesFree.Rat.RTerm
import Submission.Work.ORHughesFree.Rat.Source
import Submission.Work.ORHughesFree.Rat.exists_source_fg

namespace Work.ORHughesFree.Rat

theorem eval_restrictScalars_map {U : Type} [Group U] (V : Subgroup U)
    (β : Work.ORHughesFree.RTerm ↥V) :
    Work.ORHughesFree.RTerm.eval (Work.ORHughesFree.RatU U)
        (Work.ORHughesFree.RatU.restrictScalars V) β
      = Work.ORHughesFree.RatU.mk (Work.ORHughesFree.RTerm.map (Subtype.val) β) := by
  induction β with
  | z => rfl
  | o => rfl
  | add a b iha ihb =>
    simp only [Work.ORHughesFree.RTerm.map, Work.ORHughesFree.RTerm.eval,
      Work.ORHughesFree.RatU.mk_add]
    rw [iha, ihb]
  | mul a b iha ihb =>
    simp only [Work.ORHughesFree.RTerm.map, Work.ORHughesFree.RTerm.eval,
      Work.ORHughesFree.RatU.mk_mul]
    rw [iha, ihb]
  | rat a iha =>
    simp only [Work.ORHughesFree.RTerm.map, Work.ORHughesFree.RTerm.eval]
    rw [iha, Work.ORHughesFree.RatU.restrictScalars_ratOp]
    exact (Work.ORHughesFree.RatU.mk_rat (Work.ORHughesFree.RTerm.map Subtype.val a)).symm
  | smulL u a iha =>
    simp only [Work.ORHughesFree.RTerm.map, Work.ORHughesFree.RTerm.eval]
    rw [Work.ORHughesFree.RatU.restrictScalars_smul, iha]
    exact (Work.ORHughesFree.RatU.mk_smulL (u : U)
      (Work.ORHughesFree.RTerm.map Subtype.val a)).symm
  | smulR u a iha =>
    simp only [Work.ORHughesFree.RTerm.map, Work.ORHughesFree.RTerm.eval]
    rw [Work.ORHughesFree.RatU.restrictScalars_smulRight, iha]
    exact (Work.ORHughesFree.RatU.mk_smulR (u : U)
      (Work.ORHughesFree.RTerm.map Subtype.val a)).symm

end Work.ORHughesFree.Rat

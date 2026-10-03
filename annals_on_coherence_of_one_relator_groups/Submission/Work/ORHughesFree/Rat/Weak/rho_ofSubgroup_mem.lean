import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Rat.Weak.SVPart
import Submission.Work.ORHughesFree.Rat.WordModel.Defs
import Submission.Work.ORHughesFree.Rat.WordModel.sigma_rho

namespace Work.ORHughesFree.Rat.Weak

open Work.ORHughesFree
open Work.ORHughesFree.Rat.WordModel
open MonoidAlgebra

/-- Port of `Rat.WordModel.rho_ofSubgroup_mem` (file `Submission/Work/ORHughesFree/Rat/WordModel/rho_ofSubgroup_mem.lean`) into the namespace `Work.ORHughesFree.Rat.Weak`. The original file imports `Rat/exists_source_subgroup_weak.lean`, a cycle for the intended consumer, so the proof has to be reproduced using only `Rat/SourceFrame.lean`, `Rat/Weak/SVPart.lean`, `Rat/WordModel/Defs.lean` and `Rat/WordModel/sigma_rho.lean`; the original proof may be read for guidance. -/
theorem rho_ofSubgroup_mem {U : Type} [Group U] (V : Subgroup U) (β : Work.ORHughesFree.RatU ↥V) :
    Work.ORHughesFree.Rat.WordModel.rho (Work.ORHughesFree.RatU.ofSubgroup V β) ∈
      Work.ORHughesFree.Rat.Weak.SV V := by
  have hcomp : rho (RatU.ofSubgroup V β) = RatU.lift (S U) (RationalUSemiring.restrict V rS) β :=
    DFunLike.congr_fun (RatU.lift_comp_ofSubgroup V (S U) rS) β
  rw [hcomp]
  refine Quotient.inductionOn β ?_
  intro t
  change RTerm.eval (S U) (RationalUSemiring.restrict V rS) t ∈ SV V
  induction t with
  | z => exact SV_zero V
  | o => exact SV_one V
  | add a b iha ihb => exact SV_add iha ihb
  | mul a b iha ihb => exact SV_mul iha ihb
  | rat a iha =>
    change rSRatOp U (RTerm.eval (S U) (RationalUSemiring.restrict V rS) a) ∈ SV V
    by_cases hz : sigma (RTerm.eval (S U) (RationalUSemiring.restrict V rS) a) = 0
    · rw [rSRatOp_of_eq_zero hz]; exact SV_zero V
    · rw [rSRatOp_of_ne hz]
      refine SV_single ?_ 1
      change Mval (letterOf (RTerm.eval (S U) (RationalUSemiring.restrict V rS) a)) ∈ Rat.A V
      rw [letterOf_val, sumVal_toList, ← sigma_apply]
      exact A_ratOp_mem (sigma_mem_A iha)
  | smulL u a iha =>
    show (single (Mu (u : U)) 1 * RTerm.eval (S U) (RationalUSemiring.restrict V rS) a) ∈ SV V
    exact SV_mul (SV_single (InV_Mu u.2) 1) iha
  | smulR u a iha =>
    show (RTerm.eval (S U) (RationalUSemiring.restrict V rS) a * single (Mu (u : U)) 1) ∈ SV V
    exact SV_mul iha (SV_single (InV_Mu u.2) 1)

end Work.ORHughesFree.Rat.Weak

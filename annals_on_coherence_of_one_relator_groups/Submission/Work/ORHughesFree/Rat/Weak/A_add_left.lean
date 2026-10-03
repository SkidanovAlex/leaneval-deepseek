import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Rat.Weak.SVPart
import Submission.Work.ORHughesFree.Rat.WordModel.Defs
import Submission.Work.ORHughesFree.Rat.WordModel.sigma_rho

namespace Work.ORHughesFree.Rat.Weak

open Work.ORHughesFree
open Work.ORHughesFree.Rat.WordModel
open MonoidAlgebra

variable {U : Type} [Group U]

/-- **The word model detects `Rat(V) ⊆ Rat(U)`** (self-contained copy of
`Rat.WordModel.rho_ofSubgroup_mem`): the universal morphism `rho : Rat(U) →+* ℕ[M]` sends the
image of `Rat(V) → Rat(U)` into the `V`-part `SV V` of `ℕ[M]`.

By `RatU.lift_comp_ofSubgroup`, `rho ∘ ofSubgroup V = RatU.lift (S U) (restrict V rS)`; so it
suffices to evaluate `RatU.lift (S U) (restrict V rS) = RTerm.eval (S U) (restrict V rS)` on a
term over `V` (`Quotient.inductionOn` then induction on the term). The `⋄`-letter of an element
`z` evaluates to `ratOp (sigma z)`, and `sigma` maps the `V`-part into `Rat.A V` (`sigma_mem_A`),
which is closed under `ratOp`; `Mu u` for `u ∈ V` evaluates into `Rat.A V`; and `SV V` is closed
under `0`, `1`, `+` and `*`. -/
theorem rho_ofSubgroup_mem_aux (V : Subgroup U) (β : RatU ↥V) :
    rho (RatU.ofSubgroup V β) ∈ SV V := by
  have hcomp : rho (RatU.ofSubgroup V β) =
      RatU.lift (S U) (RationalUSemiring.restrict V rS) β :=
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

/-- Port of `Rat.A_add_left` (file `Submission/Work/ORHughesFree/Rat/A_add_left.lean`) into the namespace `Work.ORHughesFree.Rat.Weak`. The original file imports `Rat/exists_source_subgroup_weak.lean`, a cycle for the intended consumer, so the proof has to be reproduced using only `Rat/SourceFrame.lean`, `Rat/Weak/SVPart.lean`, `Rat/WordModel/Defs.lean` and `Rat/WordModel/sigma_rho.lean`; the original proof may be read for guidance. In particular the containment `rho (A V) ⊆ SV V` (proved in `Rat/WordModel/rho_ofSubgroup_mem.lean`) has to be re-derived here. -/
theorem A_add_left {U : Type} [Group U] {V : Subgroup U} {x y : Work.ORHughesFree.RatU U} :
    x + y ∈ Work.ORHughesFree.Rat.A V → x ∈ Work.ORHughesFree.Rat.A V := by
  intro h
  have h1 : rho (x + y) ∈ SV V := by
    obtain ⟨β, hβ⟩ := h
    rw [← hβ]
    exact rho_ofSubgroup_mem_aux V β
  rw [map_add] at h1
  have h2 : rho x ∈ SV V := SV.add_pure h1
  have h3 : sigma (rho x) ∈ Rat.A V := sigma_mem_A h2
  rwa [sigma_rho x] at h3

end Work.ORHughesFree.Rat.Weak

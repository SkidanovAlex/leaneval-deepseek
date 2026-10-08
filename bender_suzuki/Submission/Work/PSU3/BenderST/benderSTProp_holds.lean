import Mathlib
import ChallengeDeps
import Submission.Work.PSU3.BenderST
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.PSU3.BenderST.transport
import Submission.Work.PSU3.BenderST.transfer
import Submission.Work.PSU3.BenderST.clauses

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.BenderST.benderSTProp_holds`

`BenderSTProp` (`Submission/Work/PSU3/BenderST.lean`) is the model statement behind
Peterfalvi II Ch. V §2 Lemma 2 c): in a simple Bender group `Y`, for every split rank-one
datum `(B,U,w)` and every distinguished involution `s ∈ U`, one of the three clauses
(PSL2 / Sz / PSU3) holds, with `q = #Inv(B) + 1`.

`IsSimpleBenderGroup Y` gives an isomorphism `Y ≃* PSL2Model n`, `SzModel n` or `PSU3Model n`;
conjugating the datum into the model (`isSplitRankOne_map`), the model computation
(`psl2_standard_clause` / `sz_standard_clause` / `psu3_standard_clause`, transferred from the
standard datum to arbitrary data by `benderSTProp_of_stdClause`) gives the clause, and
`stConcl_iso` transports it back to `Y`.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint (involutions twoPoint IsAbelianSubgroup IsSplitRankOne)

namespace Work.PSU3.BenderST

theorem benderSTProp_holds : Work.PSU3.BenderSTProp := by
  intro Y _ _ hY B U w hsplit s r hs hs2 hr hsr
  cases hY with
  | isPSL2 n hn e =>
      refine stConcl_iso (B := B) (U := U) (w := w) (s := s) (r := r) e ?_
      exact benderSTProp_of_stdClause (Submission.PSL2.pSL2BenderPair n hn)
        (benderPair_isSplitRankOne _ Submission.PSL2.weylPSL_mul_self) (psl2_stdClause n hn)
        (isSplitRankOne_map e hsplit) (e s) (e r)
        (Subgroup.mem_map_of_mem e.toMonoidHom hs)
        (by simpa using (orderOf_injective e.toMonoidHom e.injective s).trans hs2)
        (Subgroup.mem_map_of_mem e.toMonoidHom hr)
        (by
          have h1 : e (w * s * w) = e (r⁻¹ * w * r) := by rw [hsr]
          simpa only [map_mul, map_inv] using h1)
  | isSuzuki n hn e =>
      refine stConcl_iso (B := B) (U := U) (w := w) (s := s) (r := r) e ?_
      exact benderSTProp_of_stdClause (Submission.Sz.szBenderPair n hn)
        (benderPair_isSplitRankOne _ (Work.Models.ModelData.szWgM_mul_self n)) (sz_stdClause n hn)
        (isSplitRankOne_map e hsplit) (e s) (e r)
        (Subgroup.mem_map_of_mem e.toMonoidHom hs)
        (by simpa using (orderOf_injective e.toMonoidHom e.injective s).trans hs2)
        (Subgroup.mem_map_of_mem e.toMonoidHom hr)
        (by
          have h1 : e (w * s * w) = e (r⁻¹ * w * r) := by rw [hsr]
          simpa only [map_mul, map_inv] using h1)
  | isPSU3 n hn e =>
      refine stConcl_iso (B := B) (U := U) (w := w) (s := s) (r := r) e ?_
      exact benderSTProp_of_stdClause (Submission.PSU3.psu3BenderPair n hn)
        (benderPair_isSplitRankOne _ (Work.Models.ModelData.psu3Weyl_mul_self n))
        (psu3_stdClause n hn)
        (isSplitRankOne_map e hsplit) (e s) (e r)
        (Subgroup.mem_map_of_mem e.toMonoidHom hs)
        (by simpa using (orderOf_injective e.toMonoidHom e.injective s).trans hs2)
        (Subgroup.mem_map_of_mem e.toMonoidHom hr)
        (by
          have h1 : e (w * s * w) = e (r⁻¹ * w * r) := by rw [hsr]
          simpa only [map_mul, map_inv] using h1)

end Work.PSU3.BenderST

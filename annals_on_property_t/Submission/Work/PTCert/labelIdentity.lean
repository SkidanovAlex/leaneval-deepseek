import Mathlib
import Submission.Work.PTCert.Glue3
import Submission.Work.PTCert.labelData
import Submission.Work.PTCert.sigmaGroupFacts
import Submission.Work.PTCert.labelPrinciple
import Submission.Work.PTCert.keyFiberSum
import Submission.Work.PTCert.tgtFiberSum
import Submission.Work.PTCert.resFiberSum
import Submission.Work.PTCert.conjWitness
import Submission.Work.PTCert.sumDecomp

/-! Guidance from the project lead (the requester):

Context: `Submission/Work/PTCert/Glue2.lean` (concrete objects of the rank-5 certificate: EI, fE,
actE, actN, repE, nuE, Pmat, …, and the semantic Props ESem/TabSem/NSem/RowSem/GroupSem/OrbLabSem/
ClassSem/KleinSem = plain meanings of the kernel checks) and `Glue3.lean` (the Props of the
mathematical steps). READ BOTH FIRST, and `NOTES_LEAD_glue.md` (workspace root) for the whole chain.
Hypotheses of the form `CodeFacts`, `ConjActFacts`, `ActCSound`, `BitsBridge`, `OrbitDecomp`,
`KleinLevel`, `FourierTransport`, `LdlChainSound`, `WhtSound` are GlueDefs Props proved in parallel by
other agents; `ESem`… are data facts proved by kernel checks. Use them as given; do not re-prove them.
Already-proved theorems you may use directly: `Work.PTCert.avgMatInvariant`, `rowFormula`,
`twistedFourierCriterion`, `psdOfBlock`, `psdSignedPerm`, `labelPrinciple`, `avgPrinciple`, `gramSOS`,
`avgGram`, `ldlScaledPrinciple`, `letterAction`, `modelSound`, `sigmaGroupFacts` (+ namespace
SigmaFacts: signAut_mul, signAut_inv, sigAut_mul, sigAut_inv, mem_SigmaSet_iff, ...), `permCheckKSound`.
NEVER unfold the big data definitions (`eAll`, `eM`, …) or try `decide` on them: all data facts come
through the Sem hypotheses. Do not change Glue*.lean. If the statement is false, `declare_false`
with the concrete reason (and say which hypothesis is missing).
Apply `labelPrinciple` (Interfaces `LabelPrinciple`, PROVED) with G = G5, Sg (IsFinSubgroup via sigmaGroupFacts 5),
index type = a sum type of three families (or ℕ-encoded), r l := lprod 5 (canonW l):
 (a) keys (r, g), r < 18, g < ngE r: coefficient (1/SCv)·multE·pv, element lprod 5 (keyWord r g), label gcls (keyOf r g);
 (b) targets p < 6561: coefficient -(q p / Dq), element lprod 5 [invL (p/81), p%81, 0, 0], label tcls p;
 (c) residual c < ncls: coefficient res c/(SCv·Dq)/2 with element lprod 5 (canonW c) (label c, conjugator 1) and with
     element (lprod 5 (canonW c))⁻¹ (label icls c).
Conjugators: ClassSem witnesses. Note `of (lprod ..)⁻¹` in residualSum is `MonoidAlgebra.of ℝ G5 (lprod 5 (canonW c))⁻¹`
(postfix ⁻¹ binds tighter than application: this is `of (g⁻¹)`).
Per-label sums: for label l < ncls, keys with gcls = l are exactly klist[l] (ClassSem: flatten klist is a permutation of
allKeys ngL, allKeys enumerates (r, g) with g < ngE r, and every k ∈ klist[c] has gcls k = c; so the filter of all keys by
label l is klist[l] as a multiset); similarly targets/tlist. Residual part: res l / 2 + Σ_{c : icls c = l} res c / 2 = res l
(icls is an involution: icls c = l ↔ c = icls l; res (icls l) = res l). So the label sum is
(Dq·U_l - SCv·Tq_l + res_l)/(SCv·Dq) = 0 by the class-sum hypothesis. Labels ≥ ncls have no terms.
Then the sum of all terms equals the element in the statement (Finset.sum over the sum type splits).
-/

namespace Work.PTCert

open Submission.PTCert Submission.PTCert.G
open Submission.PTCert.D
open Work.PTCert.LabelData
open scoped BigOperators

/-- Casting an integer list sum into `ℝ` (used to compare the class-sum hypothesis, which is
`ℤ`-valued, with the `ℝ`-valued fibre sums). -/
private lemma intCast_map_sum (l : List ℕ) (f : ℕ → ℤ) :
    (((l.map f).sum : ℤ) : ℝ) = (l.map (fun k => ((f k : ℤ) : ℝ))).sum := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, Int.cast_add, ih]

theorem labelIdentity (hC : ClassSem) : LabelIdentity := by
  intro pv q res Dq SCv hDq hSCv hcs hres
  classical
  have hSg : IsFinSubgroup Sg := (sigmaGroupFacts 5).1
  rw [← sumDecomp pv q res Dq SCv]
  have key := labelPrinciple (G := G5) (Sg := Sg) hSg (Finset.univ : Finset TIdx)
      (tCoef pv q res SCv Dq) tElt tLab labRep ?hconj ?hzero
  · exact key
  · intro t _
    exact conjWitness hC t
  · intro l
    rw [Finset.sum_filter, Fintype.sum_sum_type, Fintype.sum_sum_type]
    have hA : (∑ a : Σ r : Fin 18, Fin (ngE r.1),
          (if tLab (Sum.inl a) = l then tCoef pv q res SCv Dq (Sum.inl a) else 0))
        = (∑ t : Σ r : Fin 18, Fin (ngE r.1),
          (if gcls (keyOf t.1.1 t.2.1) = l then
            (1 / (SCv : ℝ)) * ((multE (keyOf t.1.1 t.2.1) : ℝ) * (pv (keyOf t.1.1 t.2.1) : ℝ))
          else 0)) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      dsimp only [tLab, tCoef]
      rfl
    have hB : (∑ a : Fin 6561,
          (if tLab (Sum.inr (Sum.inl a)) = l then tCoef pv q res SCv Dq (Sum.inr (Sum.inl a)) else 0))
        = (∑ p : Fin 6561, (if tcls p.1 = l then -((q p.1 : ℝ) / (Dq : ℝ)) else 0)) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      dsimp only [tLab, tCoef]
      rfl
    have hC' : (∑ x : Fin ncls × Bool,
          (if tLab (Sum.inr (Sum.inr x)) = l then tCoef pv q res SCv Dq (Sum.inr (Sum.inr x)) else 0))
        = (∑ x : Fin ncls × Bool,
          (if (if x.2 then icls x.1.1 else x.1.1) = l then
            ((res x.1.1 : ℝ) / ((SCv : ℝ) * (Dq : ℝ)) / 2) else 0)) := by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      dsimp only [tLab, tCoef]
      rfl
    rw [hA, hB, hC',
      keyFiberSum hC (fun k => (1 / (SCv : ℝ)) * ((multE k : ℝ) * (pv k : ℝ))) l,
      tgtFiberSum hC (fun p => -((q p : ℝ) / (Dq : ℝ))) l,
      resFiberSum hC res ((SCv : ℝ) * (Dq : ℝ)) l hres]
    by_cases hl : l < ncls
    · rw [if_pos hl, List.sum_map_mul_left]
      have hT : ((tlist.getD l []).map (fun p => -((q p : ℝ) / (Dq : ℝ)))).sum
          = -(1 / (Dq : ℝ)) * ((tlist.getD l []).map (fun p => (q p : ℝ))).sum := by
        rw [show (fun p : ℕ => -((q p : ℝ) / (Dq : ℝ)))
            = (fun p => (-(1 / (Dq : ℝ))) * (q p : ℝ)) from by funext p; ring]
        rw [List.sum_map_mul_left]
      rw [hT]
      have hKA : ((klist.getD l []).map (fun k => (multE k : ℝ) * (pv k : ℝ))).sum
          = ((((klist.getD l []).map (fun k => (multE k : ℤ) * pv k)).sum : ℤ) : ℝ) := by
        rw [intCast_map_sum]
        exact congrArg List.sum (List.map_congr_left (fun k _ => by push_cast; rfl))
      have hTB : ((tlist.getD l []).map (fun p => (q p : ℝ))).sum
          = ((((tlist.getD l []).map q).sum : ℤ) : ℝ) := by
        rw [intCast_map_sum]
      have h0 : (Dq : ℝ) * ((klist.getD l []).map (fun k => (multE k : ℝ) * (pv k : ℝ))).sum
          - (SCv : ℝ) * ((tlist.getD l []).map (fun p => (q p : ℝ))).sum + (res l : ℝ) = 0 := by
        have hz := hcs l hl
        have hcl := congrArg (fun z : ℤ => (z : ℝ)) hz
        rw [Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_mul, Int.cast_zero] at hcl
        rw [← hKA, ← hTB] at hcl
        exact hcl
      have hS : (SCv : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hSCv
      have hD : (Dq : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hDq
      have hgoal : (1 / (SCv : ℝ)) * ((klist.getD l []).map (fun k => (multE k : ℝ) * (pv k : ℝ))).sum
            + (-(1 / (Dq : ℝ)) * ((tlist.getD l []).map (fun p => (q p : ℝ))).sum
              + (res l : ℝ) / ((SCv : ℝ) * (Dq : ℝ)))
          = ((Dq : ℝ) * ((klist.getD l []).map (fun k => (multE k : ℝ) * (pv k : ℝ))).sum
              - (SCv : ℝ) * ((tlist.getD l []).map (fun p => (q p : ℝ))).sum + (res l : ℝ))
            / ((SCv : ℝ) * (Dq : ℝ)) := by
        field_simp
        ring
      rw [hgoal, h0, zero_div]
    · rw [if_neg hl]
      have hkl : klist.getD l [] = [] := List.getD_eq_default klist [] (by rw [klist_length hC]; exact Nat.le_of_not_lt hl)
      have htl : tlist.getD l [] = [] := List.getD_eq_default tlist [] (by rw [tlist_length hC]; exact Nat.le_of_not_lt hl)
      rw [hkl, htl]
      simp


end Work.PTCert

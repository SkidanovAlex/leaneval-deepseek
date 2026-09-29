import Mathlib
import Submission.Work.C17d.DyChainDefs

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

/-!
# The cleared chain of `∂_y^k` computes the iterated `pairStep` (area C17d)

We show that the polynomial chain `(Dc, Ac, Bc)` of `DyChainDefs` is exactly the
clearance of the recursion `pairStep` on `ℚ(X)`: for every `k`,
`A_k/D_k` and `B_k/D_k` are the two coordinates of `(pairStep)^k (1,0)`.
-/

namespace Work.C17d

open Polynomial
open Work.C17

noncomputable section

/-- **One step of the cleared `pairStep` recursion.**
If `(u,v) = (A/D, B/D)` then `pairStep (u,v) = (A''/D'', B''/D'')` where
`(D'',A'',B'')` is obtained from `(D,A,B)` by the cleared step `chainStep`. -/
lemma pairStep_chain (a b : ℚ) (k : ℕ) :
    Work.C17d.pairStep a b
        (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Ac a b k)
            / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b k),
         algebraMap (Polynomial ℚ) (RatFunc ℚ) (Bc a b k)
            / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b k))
      = (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Ac a b (k + 1))
            / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b (k + 1)),
         algebraMap (Polynomial ℚ) (RatFunc ℚ) (Bc a b (k + 1))
            / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b (k + 1))) := by
  have hD : algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b k) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (Dc_ne_zero a b k)
  have hD' : algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b (k + 1)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (Dc_ne_zero a b (k + 1))
  have hw : algebraMap (Polynomial ℚ) (RatFunc ℚ) wX ≠ 0 :=
    RatFunc.algebraMap_ne_zero wX_ne_zero
  have hp2 : algebraMap (Polynomial ℚ) (RatFunc ℚ) (P2x a b) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (P2x_ne_zero a b)
  refine Prod.ext ?_ ?_
  · show rhoQ * (Submission.CDT.dRat
          (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Ac a b k)
            / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b k))
        - (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Bc a b k)
            / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b k))
          * P0Q a b / P2Q a b)
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Ac a b (k + 1))
          / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b (k + 1))
    rw [Submission.CDT.dRat_div, Ac_succ, Dc_succ, rhoQ_eq, P0Q, P2Q]
    simp only [map_mul, map_sub, map_add, map_pow]
    field_simp <;> ring_nf
  · show rhoQ * (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Ac a b k)
          / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b k)
        + Submission.CDT.dRat
          (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Bc a b k)
            / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b k))
        - (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Bc a b k)
            / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b k))
          * P1Q a b / P2Q a b)
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Bc a b (k + 1))
          / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b (k + 1))
    rw [Submission.CDT.dRat_div, Bc_succ, Dc_succ, rhoQ_eq, P1Q, P2Q]
    simp only [map_mul, map_sub, map_add, map_pow]
    field_simp <;> ring_nf

/-- The iterated `pairStep` is the clearance of the chain: its coordinates are `A_k/D_k`
and `B_k/D_k`. -/
lemma chain_eq_pairStep (a b : ℚ) (k : ℕ) :
    (Work.C17d.pairStep a b)^[k] (1, 0)
      = (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Ac a b k)
            / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b k),
         algebraMap (Polynomial ℚ) (RatFunc ℚ) (Bc a b k)
            / algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih, pairStep_chain]

theorem DyChain_rat (a b : ℚ) (k : ℕ) :
    (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17d.Ac a b k)
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17d.Dc a b k)
          * ((Work.C17d.pairStep a b)^[k] (1, 0)).1) ∧
    (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17d.Bc a b k)
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Work.C17d.Dc a b k)
          * ((Work.C17d.pairStep a b)^[k] (1, 0)).2) := by
  have hD : algebraMap (Polynomial ℚ) (RatFunc ℚ) (Dc a b k) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (Dc_ne_zero a b k)
  have h := chain_eq_pairStep a b k
  constructor
  · have hfst := congrArg Prod.fst h
    simp only [Prod.fst] at hfst
    rw [hfst]
    exact (mul_div_cancel₀ (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Ac a b k)) hD).symm
  · have hsnd := congrArg Prod.snd h
    simp only [Prod.snd] at hsnd
    rw [hsnd]
    exact (mul_div_cancel₀ (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Bc a b k)) hD).symm

end

end Work.C17d

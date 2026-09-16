import Submission.ZagierHoffmanProof.StepL180

set_option autoImplicit false
set_option maxHeartbeats 40000000
open Polynomial RatFunc
open scoped BigOperators
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

/-!
# Step L181: `ambNu` IS the recursion's measure — the chain members descend whenever the
# depth does not decrease (which the committed `*_dep_ge` facts supply for the TIE members)

`ambNu k q w t = ((psum t k, w − depth t), ((q+2)^(w+1) − 1 − initVal q w t, entry))` inserts the
DEPTH between the prefix-`k` sum and the `Init`-data, whereas `lkμ3 k q w t` groups the prefix
sum with the `Init`-data only.  This module records the decisive consequence of that grouping:

  • ★★ `ambNu_lt_of_mainkStep3_of_dep_le` — `MainkStep3 k q w s m` plus the NON-STRICT depth
    bound `depth s ≤ depth m` already gives `ambNu k q w m < ambNu k q w s`:
      – C1 (prefix drop) → first component;
      – C2′/C3 (prefix equal, `Init` grows / entry drops) → the DEPTH component (strict when
        `depth s < depth m`), else the `Init`/entry components, which `MainkStep3` supplies.
    (StepL176's `ambNu_lt_of_mainkStep3_of_dep_gt` is the strict-depth special case.)
  • ★ `ambNu_lt_iff` / `ambNu_same_projection`: `ambNu`'s first block is EXACTLY the first block
    of the ambient ports' descent (`StepL165/172/173/175`), so ONE measure serves both the chain
    dispatch (`MainkStep3` + `*_dep_ge`) and the ambient chain ports.
CONSEQUENCE (PLAN SESSION 272 addendum): the tie members of every chain are exactly the
`C2′/C3` members, and for them the committed depth invariants give `depth s ≤ depth m`
(`type1_dep_ge`, `type3_dep_ge`, StepL161 for the generic `(k,j)` chains; `maink_g5_aSide_dep_ge`
StepL170 and `maink_g5_bSide_dep_gt` StepL173 for the G5 chain; `maink_case2_j_type3_dep`
StepL175 for the CASE-2 chain, whose C2′/C3 members are necessarily its TYPE-3 family since the
TYPE-2/qqq families strictly drop at the chain's level).  Hence the chain dispatch of the
recursion can be run on `ambNu`, and the residual shrinks to the TOWER outputs `c` with
`depth c = depth x` and `psum c k = psum x k` (where only the `Init`-transference is needed).
theorem_B/D remain ABP-gated (no route).
-/

namespace ZagierHoffmanPositiveChar
attribute [instance] P2Data.fin
attribute [instance] RelData.finA
attribute [instance] RelData.finB
attribute [instance] FixedRel.fin
attribute [local instance] Classical.propDecidable
variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-- ★★ `MainkStep3` + a NON-STRICT depth bound decreases `ambNu`. -/
lemma ambNu_lt_of_mainkStep3_of_dep_le (k q w : ℕ) {r r' : ℕ} (s : Fin r → ℕ+) (m : Fin r' → ℕ+)
    (hsw : weight r s = w) (hmw : weight r' m = w)
    (hdep : r ≤ r') (h : MainkStep3 k q w s m) :
    ambNu k q w m < ambNu k q w s := by
  rcases h with hlt | ⟨heq, hiv⟩ | ⟨heq, hiv, hdrop⟩
  · exact ambNu_lt_of_psum_lt k q w s m hlt
  · have hsub : w - r' ≤ w - r := Nat.sub_le_sub_left hdep w
    rw [ambNu, ambNu, Prod.Lex.lt_iff]
    rcases lt_or_eq_of_le hsub with hlt2 | heq2
    · left
      rw [Prod.Lex.lt_iff]
      exact Or.inr ⟨heq, hlt2⟩
    · right
      constructor
      · apply toLex_inj.mpr
        refine Prod.ext heq ?_
        show w - r' = w - r
        omega
      · have hivM : initVal q w m < (q + 2) ^ (w + 1) := initVal_lt_pow q w m hmw
        have hivM1 : initVal q w m ≤ (q + 2) ^ (w + 1) - 1 := Nat.le_sub_one_of_lt hivM
        have hk : initVal q w s < (q + 2) ^ (w + 1) - 1 :=
          lt_of_lt_of_le hiv hivM1
        show toLex ((q + 2) ^ (w + 1) - 1 - initVal q w m, pad0 m (initLen q m))
            < toLex ((q + 2) ^ (w + 1) - 1 - initVal q w s, pad0 s (initLen q s))
        rw [Prod.Lex.lt_iff]
        left
        exact Nat.sub_lt_sub_left hk hiv
  · have hsub : w - r' ≤ w - r := Nat.sub_le_sub_left hdep w
    rw [ambNu, ambNu, Prod.Lex.lt_iff]
    rcases lt_or_eq_of_le hsub with hlt2 | heq2
    · left
      rw [Prod.Lex.lt_iff]
      exact Or.inr ⟨heq, hlt2⟩
    · right
      constructor
      · apply toLex_inj.mpr
        refine Prod.ext heq ?_
        show w - r' = w - r
        omega
      · show toLex ((q + 2) ^ (w + 1) - 1 - initVal q w m, pad0 m (initLen q m))
            < toLex ((q + 2) ^ (w + 1) - 1 - initVal q w s, pad0 s (initLen q s))
        rw [Prod.Lex.lt_iff]
        right
        constructor
        · show (q + 2) ^ (w + 1) - 1 - initVal q w m
              = (q + 2) ^ (w + 1) - 1 - initVal q w s
          rw [hiv]
        · exact hdrop

/-- ★ The first block of `ambNu` is exactly the pair used by the ambient ports' descents
(`(psum · k, w − depth)`), so one measure serves the chain dispatch and the ports. -/
lemma ambNu_first_block (k q w : ℕ) {r : ℕ} (s : Fin r → ℕ+) :
    ambNu k q w s = toLex (toLex (psum s k, w - r),
      toLex ((q + 2) ^ (w + 1) - 1 - initVal q w s, pad0 s (initLen q s))) := rfl

end ZagierHoffmanPositiveChar
